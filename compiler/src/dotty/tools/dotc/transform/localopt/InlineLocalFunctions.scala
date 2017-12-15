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

  val defined = mutable.Set[Symbol]()
  val refs = mutable.Map[Symbol, Int]()
  val calls = mutable.Map[Symbol, Int]()
  var discard: mutable.Set[Symbol] = null

  val functions = mutable.Map[Symbol, DefDef]()
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
    discard = null

    functions.clear()
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
    if (discard eq null) discard = defined.filter(fun => {
        val callCount = calls.getOrElse(fun, 0)
        val refCount = refs.getOrElse(fun, 0)
        callCount <= 1 && refCount == callCount
      });
    {
      case funDef @ FunDef(sym) if discard.contains(sym) =>
        functions(sym) = funDef
        EmptyTree

      case id: Ident if discard.contains(ctx.owner) && id.symbol.is(Param) =>
        ref(inlinedSymbol(id.symbol))

      case call @ Apply(fn, arguments) if functions.contains(fn.symbol) =>
        val func = functions(fn.symbol)
        val params = func.vparamss.flatten
        if (params.size == arguments.size) {
          Block(arguments.zip(params).map { 
            case (arg, param) => 
              val inlined = inlinedSymbol(param.symbol)
              ValDef(inlined.asTerm, arg) 
          }, func.rhs)
        } else call

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

