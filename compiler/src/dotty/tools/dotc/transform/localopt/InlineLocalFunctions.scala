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

  val functions = mutable.Map[Symbol, DefDef]()
  val refs = mutable.Map[Symbol, Int]()
  var discard: Set[Symbol] = null

  object FunDef {
    def unapply(funDef: DefDef)(implicit ctx: Context): Option[Symbol] = {
      Some(funDef.symbol)
    }
  }

  def clear(): Unit = {
    functions.clear()
    refs.clear()
    discard = null
  }


  def visitor(implicit ctx: Context): Tree => Unit = {
    case fn @ FunDef(sym) => functions(sym) = fn

    case id: Ident if functions.contains(id.symbol) =>
      refs(id.symbol) = refs.getOrElse(id.symbol, 0) + 1

    /*case CaseValDef(sym, _) =>
      caseVals += sym -> 
        ctx.newSymbol(
          sym.owner,
          LocalOptInlineLocalObj.fresh(), 
          (sym.flags &~ Case) | Synthetic, 
          sym.info, 
          sym.privateWithin, 
          sym.coord)*/

    case _ =>
  }


  def transformer(implicit ctx: Context): Tree => Tree = {
    if (discard eq null) discard = refs.filter(fun => fun._2 == 1).map(_._1).toSet;
    {
      case FunDef(sym) if discard.contains(sym) =>
        EmptyTree

      case t @ FunDef(sym) => 
        t

      case call @ Apply(fn, caseVals) if functions.contains(fn.symbol) && refs.getOrElse(fn.symbol, 0) == 1 =>
        val func = functions(fn.symbol)
        val params = func.vparamss.flatten
        if (params.size == caseVals.size) {
          Block(caseVals.zip(params).map { case (arg, param) => ValDef(param.symbol.asTerm, arg) }, func.rhs)
        } else call

      case t => t
    }
  }
}

