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


class InlineVals extends Optimisation {
  import ast.tpd._

  val defined = newMutableSymbolMap[ValDef]
  val timesUsed = newMutableSymbolMap[Int]

  val impureTimeUsed = newMutableSymbolMap[Int]

  def clear(): Unit = {
    defined.clear()
    timesUsed.clear()
    impureTimeUsed.clear()
  }

  def visitor(implicit ctx: Context): Tree => Unit = {
    case t: ValDef if t.symbol.exists && !t.symbol.is(Param) && isVal(t.symbol) && isPureExpr(t.rhs) =>
        defined.put(t.symbol, t)

    case t: ValDef if t.symbol.exists && !t.symbol.is(Param) =>
        impureTimeUsed.put(t.symbol, 0)

    case t: Ident if defined.contains(t.symbol) =>
      val b4 = timesUsed.getOrElseUpdate(t.symbol, 0)
      timesUsed.update(t.symbol, b4 + 1)

    case Assign(id: Ident, _) if impureTimeUsed.contains(id.symbol) =>
      impureTimeUsed.update(id.symbol, impureTimeUsed(id.symbol) - 1)

    case t: Ident if impureTimeUsed.contains(t.symbol) => 
      impureTimeUsed.update(t.symbol, impureTimeUsed(t.symbol) + 1)


    case _ =>
  }

  def transformer(implicit ctx: Context): Tree => Tree = {
    case t: ValDef if timesUsed.getOrElse(t.symbol, 0) == 1 =>
      EmptyTree

    case t: ValDef if impureTimeUsed.getOrElse(t.symbol, 1) <= 0 =>
      t.rhs

    case Assign(id: Ident, rhs) if impureTimeUsed.getOrElse(id.symbol, 1) <= 0 =>
      rhs

    case t: Ident if timesUsed.getOrElse(t.symbol, 0) == 1 =>
      defined(t.symbol).rhs.changeOwner(t.symbol.owner, ctx.owner)

    case t => t
  }

  private def isVal(s: Symbol)(implicit ctx: Context): Boolean = !s.is(Mutable) && !s.is(Method) && !s.owner.isClass
}

