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

  def clear(): Unit = {
    defined.clear()
  }

  def visitor(implicit ctx: Context): Tree => Unit = {
    case t: ValDef if t.rhs != EmptyTree && isVal(t.symbol) => 
      defined.put(t.symbol, t)

    case _ =>
  }

  def transformer(implicit ctx: Context): Tree => Tree = {
    case t @ TypeApply(fun @ Select(x, _), List(tp)) if defined.contains(x.symbol) && fun.symbol == defn.Any_isInstanceOf => 
      conditionForType(defined(x.symbol).rhs, tp.tpe).filter(isPureExpr(_)).getOrElse(t)

    case t => t
  }

  private def isVal(s: Symbol)(implicit ctx: Context): Boolean = !s.is(Mutable) && !s.is(Method) && !s.owner.isClass

  private def conditionForType(tree: Tree, tpe: Type)(implicit ctx: Context): Option[Tree] = 
    tree match {
      case If(cond, thenp, elsep) => 
        val thenDerives = thenp.tpe.derivesFrom(tpe.typeSymbol)
        val elseDerives = elsep.tpe.derivesFrom(tpe.typeSymbol)
        if (thenDerives == elseDerives) Some(Literal(Constant(thenDerives)))
        else if (thenDerives) Some(cond)
        else Some(cond.select(defn.Boolean_!).ensureApplied)
      case t if t.tpe.derivesFrom(tpe.typeSymbol) => Some(Literal(Constant(true)))
      case t if !tpe.derivesFrom(t.tpe.typeSymbol) => Some(Literal(Constant(false)))
      case _ => None
    } 
}

