package dotty.tools.dotc
package transform.localopt

import core.Constants.{Constant, NullTag}
import core.Contexts.Context
import core.NameKinds.LocalOptNullChecksName
import core.Symbols._
import core.Types._
import core.Flags._
import core.Names._
import core.StdNames._
import ast.Trees._
import scala.collection.mutable

/** Eliminate unnecessary null checks
 *
 *  - (this)  cannot be null
 *  - (new C) cannot be null
 *  - literal is either null itself or non null
 *  - fallsback to `tpe.isNotNull`, which will eventually be true for non nullable types.
 *  - in (a.call; a == null), the first call throws a NPE if a is null; the test can be removed.
 *
 *  
 *  @author DarkDimius, Jvican, OlivierBlanvillain, gan74
 */
class RemoveUnnecessaryNullChecks extends Optimisation {
  import ast.tpd._

  val checked = newMutableSymbolMap[Symbol]
  val ignore = mutable.Set[Symbol]()
  val newSymbols = mutable.Set[Symbol]()



  // matches sym == null or null == sym
  object NullCheck {
    def unapply(t: Apply)(implicit ctx: Context): Option[Symbol] =
      t match {
        case t @ Apply(Select(id: Ident, op), List(rhs)) if (t.symbol == defn.Object_eq || t.symbol == defn.Any_==) && !isVar(id.symbol) && isAlwaysNull(rhs) => Some(id.symbol)
        case t @ Apply(Select(lhs, op), List(id: Ident)) if (t.symbol == defn.Object_eq || t.symbol == defn.Any_==) && !isVar(id.symbol) && isAlwaysNull(lhs) => Some(id.symbol)
        case _ => None
      }
  }

  def clear(): Unit = {
    checked.clear()
    ignore.clear()
    newSymbols.clear()
  }

  def visitor(implicit ctx: Context): Tree => Unit = {
    case t: ValDef =>
      t.rhs match {
        case NullCheck(sym) => ignore += sym
        case _ =>
      }

    case NullCheck(sym) if !checked.contains(sym) =>
      val newSym = companionSymbol(sym)
      checked.put(sym, newSym)
      newSymbols += newSym

    case _ => 
  }


  def transformer(implicit ctx: Context): Tree => Tree = {
    case NullCheck(sym) if !ignore.contains(sym) => ref(checked(sym))

    case t: ValDef if checked.contains(t.symbol) && !ignore.contains(t.symbol) =>
      val isNull = nullness(t.rhs) match {
        case Some(n) => Literal(Constant(n))
        case None => nullcheck(t.symbol)
      }

      Thicket(List(t, ValDef(checked(t.symbol).asTerm, isNull)))

    case blk @ Block(stats, expr) =>
      val newStats = stats.mapConserve {
        case s @ Apply(Select(id: Ident, _), _) if checked.contains(id.symbol) && !ignore.contains(id.symbol) =>
          Thicket(List(s, toFalse(checked(id.symbol))))
        case s => s
      }
      cpy.Block(blk)(newStats, expr)

    case If(id: Ident, thenp, elsep) if newSymbols.contains(id.symbol) =>
      If(id, Block(List(toTrue(id.symbol)), thenp), Block(List(toFalse(id.symbol)), thenp))

    case t => t
  }


  private def isNeverNull(tree: Tree)(implicit ctx: Context): Boolean =
    tree match {
      case Block(_, expr) => isNeverNull(expr)
      case If(_, th, el) => isNeverNull(th) && isNeverNull(el)
      case t: Typed => isNeverNull(t.expr)
      case t: Literal => t.const.tag != NullTag
      case _: This => true
      case _: New => true
      case t: Apply if t.symbol.isConstructor => true
      case Apply(Select(New(_), _), _) => true
      case t => t.tpe.isNotNull
    }

  private def isAlwaysNull(tree: Tree)(implicit ctx: Context): Boolean = 
    tree match {
      case EmptyTree => true
      case Block(_, expr) => isAlwaysNull(expr)
      case If(_, th, el) => isAlwaysNull(th) && isAlwaysNull(el)
      case t: Typed => isAlwaysNull(t.expr)
      case t: Literal => t.const.tag == NullTag
      case _ => false
    }

  private def nullness(tree: Tree)(implicit ctx: Context): Option[Boolean] = 
    if (isNeverNull(tree)) Some(false)
    else if (isAlwaysNull(tree)) Some(true)
    else None


  private def isVar(s: Symbol)(implicit ctx: Context): Boolean = s.is(Mutable | Lazy)

  private def toFalse(sym: Symbol)(implicit ctx: Context) = Assign(ref(sym), Literal(Constant(false)))
  private def toTrue(sym: Symbol)(implicit ctx: Context) = Assign(ref(sym), Literal(Constant(true)))
  private def nullcheck(sym: Symbol)(implicit ctx: Context) = ref(sym).select(defn.Object_eq).appliedTo(Literal(Constant(null)))
  private def companionSymbol(sym: Symbol)(implicit ctx: Context) = 
    ctx.newSymbol(sym.owner, LocalOptNullChecksName.fresh(), Synthetic | Mutable, nullcheck(sym).tpe)
}
