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
  val defined = mutable.Map[Symbol, DefDef]()
  // number of time a given function is referenced
  val refs = mutable.Map[Symbol, Int]()
  // number of time a given function is called
  val calls = mutable.Map[Symbol, Int]()



  object FunDef {
    def unapply(funDef: DefDef)(implicit ctx: Context): Option[Symbol] =
      if (funDef.symbol.is(Method) && 
          !funDef.symbol.is(Override) && 
          funDef.symbol.owner.is(Method) &&
          funDef.symbol.owner == ctx.owner) Some(funDef.symbol)
      else None
  }

  def clear(): Unit = {
    defined.clear()
    refs.clear()
    calls.clear()
  }


  def visitor(implicit ctx: Context): Tree => Unit = {
    case funDef @ FunDef(sym) => 
      defined += sym -> funDef

    case Apply(fn, _) => 
      val sym = fn.symbol 
      //if (defined.contains(sym))
        calls(sym) = calls.getOrElse(sym, 0) + 1

    case t if t.denot.exists => 
      val sym = t.symbol 
      if (defined.contains(sym))
        refs(sym) = refs.getOrElse(sym, 0) + 1

    case _ => 
  }


  def transformer(implicit ctx: Context): Tree => Tree = {
    /*case FunDef(sym) if defined.contains(sym) && shouldDiscard(sym) =>
      EmptyTree*/

    case call @ Apply(fn, arguments) if defined.contains(fn.symbol) && shouldInline(fn.symbol) && !isRecCall(fn.symbol) =>
      // def all arguements then inline
      val func = defined(fn.symbol)
      val params = func.vparamss.flatten
      assert(params.size == arguments.size)

      val inlinedArgs = mutable.Map[Symbol, Symbol]()
      val bindings = arguments.zip(params).map { 
        case (arg, param) => cpy.ValDef(param)(rhs = arg)
      }
      val body = func.rhs

      print(fn.symbol + " inlined ")
      var owner = ctx.owner
      while(owner.exists) {
        print("into " + owner + " ")
        owner = owner.owner
      }
      println("")

      Inlined(call, bindings, body).changeOwner(fn.symbol, ctx.owner)

    case t => t
  }

  private def isRecCall(fn: Symbol)(implicit ctx: Context): Boolean = {
    var owner = ctx.owner
    while(owner.exists) {
      if (owner == fn) {
        return true
      }
      owner = owner.owner
    }
    false
  }

  private def shouldDiscard(fn: Symbol): Boolean = refs.getOrElse(fn, 0) == 0

  private def shouldInline(fn: Symbol): Boolean = {
    val callCount = calls.getOrElse(fn, 0)
    val refCount = refs.getOrElse(fn, 0)
    // we inline everything called at most once and that is not referenced otherwise
    callCount <= 1 && refCount == callCount
  }


  /*private def inlinedSymbol(sym: Symbol)(implicit ctx: Context): Symbol =
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
    }*/
}

