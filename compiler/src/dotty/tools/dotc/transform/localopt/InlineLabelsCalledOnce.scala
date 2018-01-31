package dotty.tools.dotc
package transform.localopt

import core.Contexts.Context
import core.Symbols._
import core.Flags._
import transform.SymUtils._
import scala.collection.mutable
import config.Printers.simplify

/** Inlines LabelDef which are used exactly once.
 *
 *  @author DarkDimius, OlivierBlanvillain
 */
class InlineLabelsCalledOnce extends Optimisation {
  import ast.tpd._

  val timesUsed = newMutableSymbolMap[Int]
  val defined   = newMutableSymbolMap[DefDef]

  def clear(): Unit = {
    timesUsed.clear()
    defined.clear()
  }

  def visitor(implicit ctx: Context): Tree => Unit = {
    case d: DefDef if d.symbol.is(Label) =>
      var isRecursive = false
      d.rhs.foreachSubTree { x =>
        if (x.symbol == d.symbol)
          isRecursive = true
      }
      if (!isRecursive)
        defined.update(d.symbol, d)

    case t: Apply if t.symbol.is(Label) =>
      val b4 = timesUsed.getOrElseUpdate(t.symbol, 0)
      timesUsed.update(t.symbol, b4 + 1)

    case _ =>
  }

  def transformer(implicit ctx: Context): Tree => Tree = {
    case a: Apply =>
      defined.get(a.symbol) match {
        case Some(defDef) if usedOnce(a.symbol) =>
          simplify.println(s"Inlining labeldef ${defDef.name}")
          println("inlineLabel")
          val args = a.args
          val params = defDef.vparamss.flatten
          assert(params.size == args.size)
          val bindings = args.zip(params).map {
            case (arg, param) => cpy.ValDef(param)(rhs = arg)
          }
          Block(bindings, defDef.rhs.changeOwner(defDef.symbol, ctx.owner))

        case Some(defDef) if defDef.rhs.isInstanceOf[Literal] =>
          println("inlineLiteral")
          defDef.rhs

        case _ => a
      }

    case d: DefDef if usedOnce(d.symbol) =>
      simplify.println(s"Dropping labeldef (used once) ${d.name} ${timesUsed.get(d.symbol)}")
      defined.update(d.symbol, d)
      EmptyTree

    case d: DefDef if neverUsed(d.symbol) =>
      simplify.println(s"Dropping labeldef (never used) ${d.name} ${timesUsed.get(d.symbol)}")
      EmptyTree

    case t => t
  }

  def usedN(s: Symbol, n: Int)(implicit ctx: Context): Boolean =
    s.is(Label)                    &&
    timesUsed.getOrElse(s, 0) == n &&
    defined.contains(s)

  def usedOnce(s: Symbol)(implicit ctx: Context): Boolean  = usedN(s, 1)
  def neverUsed(s: Symbol)(implicit ctx: Context): Boolean = usedN(s, 0)
}
