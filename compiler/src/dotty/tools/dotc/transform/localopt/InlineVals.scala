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
 *  get rid of the intermediate tuples object somes created when pattern
 *  matching on Scala2 case classes.
 */
class InlineVals extends Optimisation {
  import ast.tpd._


  val defined = newMutableSymbolMap[ValDef]
  val timesUsed = newMutableSymbolMap[Int]

  def clear(): Unit = {
   
    defined.clear()
    timesUsed.clear()
  }

  def visitor(implicit ctx: Context): Tree => Unit = {
    case t: ValDef if isVal(t.symbol) => 
      if (isPureExpr(t.rhs))
        defined.put(t.symbol, t)

    case t: Ident if defined.contains(t.symbol) =>
      val b4 = timesUsed.getOrElseUpdate(t.symbol, 0)
      timesUsed.update(t.symbol, b4 + 1)

    case _ =>
  }

  def transformer(implicit ctx: Context): Tree => Tree = {
    case t: ValDef if timesUsed.getOrElse(t.symbol, 0) == 1 =>
      //println("inlining " + t.show)
      EmptyTree

    case t: Ident if timesUsed.getOrElse(t.symbol, 0) == 1 =>
      defined(t.symbol).rhs

    case t => t
  }

  private def isVal(s: Symbol)(implicit ctx: Context): Boolean = !s.is(Mutable) && !s.is(Method) && !s.owner.isClass
}

