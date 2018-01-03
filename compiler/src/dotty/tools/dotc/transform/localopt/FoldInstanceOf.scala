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


class FoldInstanceOf extends Optimisation {
  import ast.tpd._

  val defined = newMutableSymbolMap[ValDef]

  def clear(): Unit =  defined.clear()

  def visitor(implicit ctx: Context): Tree => Unit = {
    case t: ValDef if t.rhs != EmptyTree && isVal(t.symbol) => 
      defined.put(t.symbol, t)

    case _ =>
  }

  def transformer(implicit ctx: Context): Tree => Tree = {
    case t @ TypeApply(fun @ Select(x, _), List(tp)) if defined.contains(x.symbol) && fun.symbol == defn.Any_isInstanceOf => 
      val cond = rewriteIsInstanceOf(defined(x.symbol).rhs, tp.tpe).filter(isPureExpr(_))
      if (cond.isDefined) {
        /*val exprType = defined(x.symbol).rhs.tpe.widenDealias.widenTermRefExpr
        val testType = tp.tpe.widenDealias.widenTermRefExpr
        println(exprType.show  + " <:< " + testType.show + " = " + (exprType relaxed_<:< testType))
        println(testType.show  + " <:< " + exprType.show + " = " + (testType relaxed_<:< exprType))*/
        println(defined(x.symbol).show + ":  " + t.show + " => " + cond.get.show + "\n\n")
      }
      cond.getOrElse(t)

    case t => t
  }

  private def isVal(s: Symbol)(implicit ctx: Context): Boolean = !s.is(Mutable | Lazy) && !s.is(Method) && !s.owner.isClass

  private def rewriteIsInstanceOf(tree: Tree, testType: Type)(implicit ctx: Context): Option[Tree] = {
    val exprType = tree.tpe
    tree match {
      case br @ If(cond, thenp, elsep) =>
        (rewriteIsInstanceOf(thenp, testType), 
         rewriteIsInstanceOf(elsep, testType)) match {
          case (Some(newThen), Some(newElse)) => Some(If(cond, newThen, newElse))
          case _ => None 
        }

      case Apply(Select(New(_), _), _) => 
        Some(Literal(Constant(exprType relaxed_<:< testType)))

      case Block(_, expr) => 
        rewriteIsInstanceOf(expr, testType)

      case _ =>
        if (exprType relaxed_<:< testType) Some(Literal(Constant(true)))
        else None
    }
  }
}

