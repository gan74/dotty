package dotty.tools.dotc
package transform.localopt

import core.Constants.{Constant, NullTag}
import core.Contexts.Context
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

  // matches sym == null or null == sym
  object NullCheck {
    def unapply(t: Tree)(implicit ctx: Context): Option[(Symbol, Boolean, Tree)] =
      t match {
        case t @ Apply(Select(id: Ident, op), List(rhs)) if !isVar(id.symbol) && isAlwaysNull(rhs) => 
          if (t.symbol == defn.Object_eq || t.symbol == defn.Any_==) Some((id.symbol, true, rhs))
          else if (t.symbol == defn.Object_ne || t.symbol == defn.Any_!=) Some((id.symbol, false, rhs))
          else None
        case t @ Apply(Select(lhs, op), List(id: Ident)) if !isVar(id.symbol) && isAlwaysNull(lhs) => 
          if (t.symbol == defn.Object_eq || t.symbol == defn.Any_==) Some((id.symbol, true, lhs))
          else if (t.symbol == defn.Object_ne || t.symbol == defn.Any_!=) Some((id.symbol, false, lhs))
          else None
        case s @ Select(NullCheck(sym, isNull, rhs), _) if s.symbol eq defn.Boolean_! => Some(sym, !isNull, rhs)
        case _ => None
      }
  }

  def clear(): Unit = ()

  def visitor(implicit ctx: Context): Tree => Unit = NoVisitor


  def transformer(implicit ctx: Context): Tree => Tree = {
    // transform tree recursively replacing nullchecks for symbols in nullness
    def transform(tree: Tree, nullness: mutable.Map[Symbol, Boolean]) =
      if (nullness.isEmpty) tree
      else new TreeMap() {
          override def transform(tree: Tree)(implicit ctx: Context): Tree = {
            val innerCtx = if (tree.isDef && tree.symbol.exists) ctx.withOwner(tree.symbol) else ctx
            super.transform(tree)(innerCtx) match {
              case t @ NullCheck(sym, isNull, rhs) if nullness.contains(sym) => 
                println("nullcheck")
                Block(List(rhs), Literal(Constant(nullness(sym) == isNull)))
              case t => t
            }
          }
        }.transform(tree)

    {
      case blk @ Block(stats, expr) => 
        // (symbol -> is null) elements for which we don't have informations aren't in the map
        val nullness = mutable.Map[Symbol, Boolean]()

        // map statements and propagate nullness
        val newStats = stats.mapConserve {
          case t: ValDef if !isVar(t.symbol) => 
            if      (isAlwaysNull(t.rhs)) nullness += t.symbol -> true
            else if (isNeverNull(t.rhs)) nullness += t.symbol -> false
            else if (t.rhs.symbol.exists && nullness.contains(t.rhs.symbol)) 
              nullness += t.symbol -> nullness(t.rhs.symbol)
            
            transform(t, nullness)

          // throw NPE if id is null
          case t @ Apply(Select(id: Ident, _), _) if !isVar(id.symbol) => 
            nullness += id.symbol -> false
            transform(t, nullness)

          case t => 
            transform(t, nullness)
        }

        cpy.Block(blk)(newStats, transform(expr, nullness))

      case br @ If(cond, thenp, elsep) => 
        cond match {
          case NullCheck(sym, isNull, _) => 
            val newThen = transform(thenp, mutable.Map[Symbol, Boolean](sym -> isNull))
            val newElse = transform(elsep, mutable.Map[Symbol, Boolean](sym -> !isNull))
            cpy.If(br)(cond, newThen, newElse)

          case _ =>
            val nullness = mutable.Map[Symbol, Boolean]()
            for (n <- nullchecksIn(cond)) 
              n match {
                case (sym, isNull) => nullness.put(sym, isNull)
              }
            val newThen = transform(thenp, nullness)
            cpy.If(br)(cond, newThen, elsep)
        }
       

      case t => t
    }
  }

  private def nullchecksIn(tree: Tree)(implicit ctx: Context): List[(Symbol, Boolean)] = {
    tree match {
      case NullCheck(sym, isNull, _) => List((sym, isNull))
      case Apply(s @ Select(lhs, _), List(rhs)) if s.symbol == defn.Boolean_&& => nullchecksIn(lhs) ++ nullchecksIn(rhs)
      case _ => List()
    }
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

  private def isVar(s: Symbol)(implicit ctx: Context): Boolean = s.is(Mutable | Lazy)
}
