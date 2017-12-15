package dotty.tools.dotc
package transform.localopt

import core.Constants.Constant
import core.Contexts.Context
import core.Decorators._
import core.Names.Name
import core.NameKinds.LocalOptInlineLocalObj
import core.Types.Type
import core.StdNames._
import core.Symbols._
import core.Flags._
import ast.Trees._
import scala.collection.mutable
import scala.collection.mutable.LinkedHashMap
import transform.SymUtils._
import config.Printers.simplify
import Simplify._

/** Rewrite fields of local instances as vals.
 *
 *  If a local instance does not escape the local scope, it will be removed
 *  later by DropNoEffects, thus implementing the equivalent of (local) multi
 *  parameter value classes. The main motivation for this transformation is to
 *  get ride of the intermediate tuples object somes created when pattern
 *  matching on Scala2 case classes.
 */
class InlineLocalFunctions(val simplifyPhase: Simplify) extends Optimisation {
  import ast.tpd._

  // local functions
  val defined = mutable.Set[Symbol]()
  // number of time a given function is referenced
  val refs = mutable.Map[Symbol, Int]()
  // number of time a given function is called
  val calls = mutable.Map[Symbol, Int]()
  // functions that will be inline and that should be discarded
  var toDiscard: mutable.Set[Symbol] = null

  // discarded function symbol -> original def
  val discarded = mutable.Map[Symbol, DefDef]()
  // argument map for inlined functions
  val args = mutable.Map[Symbol, Symbol]()

  object FunDef {
    def unapply(funDef: DefDef)(implicit ctx: Context): Option[Symbol] = {
      Some(funDef.symbol)
    }
  }

  def clear(): Unit = {
    defined.clear()
    refs.clear()
    calls.clear()
    toDiscard = null

    discarded.clear()
    args.clear()
  }


  def visitor(implicit ctx: Context): Tree => Unit = {
    case FunDef(sym) => 
      defined += sym

    case id: Ident if defined.contains(id.symbol) =>
      refs(id.symbol) = refs.getOrElse(id.symbol, 0) + 1

    case Apply(fn, _) if defined.contains(fn.symbol) => 
      calls(fn.symbol) = calls.getOrElse(fn.symbol, 0) + 1

    case _ =>
  }


  def transformer(implicit ctx: Context): Tree => Tree = {
    if (toDiscard eq null) toDiscard = defined.filter(fun => {
        val callCount = calls.getOrElse(fun, 0)
        val refCount = refs.getOrElse(fun, 0)
        // we inline everything called at most once and that is not referenced otherwise
        callCount <= 1 && refCount == callCount
      });
    {
      case funDef @ FunDef(sym) if toDiscard.contains(sym) =>
        discarded(sym) = funDef
        EmptyTree

      case id: Ident if toDiscard.contains(ctx.owner) && id.symbol.is(Param) =>
        // this is the parameter of a function that will be inlined, change it to a non param symbol
        ref(inlinedSymbol(id.symbol))

      case call @ Apply(fn, arguments) if discarded.contains(fn.symbol) =>
        // def all arguements then inline
        val func = discarded(fn.symbol)
        val params = func.vparamss.flatten
        assert(params.size == arguments.size) 
        Block(arguments.zip(params).map { 
          case (arg, param) => 
            val inlined = inlinedSymbol(param.symbol)
            ValDef(inlined.asTerm, arg) 
        }, func.rhs)

      case t => t
    }
  }


  private def inlinedSymbol(sym: Symbol)(implicit ctx: Context): Symbol =
    args.get(sym) match {
      case Some(s) => s
      case None =>
        val s = ctx.newSymbol(
          sym.owner,
          LocalOptInlineLocalObj.fresh(), 
          (sym.flags &~ (Param | Case)) | Synthetic, 
          sym.info, 
          sym.privateWithin, 
          sym.coord)

        args(sym) = s
        s
    }
    
}

