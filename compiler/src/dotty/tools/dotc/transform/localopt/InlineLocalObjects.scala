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
class InlineLocalObjects(val simplifyPhase: Simplify) extends Optimisation {
  import ast.tpd._


  // ValDefs whose lhs is used with `._1` (or any getter call).
  val gettersCalled = mutable.HashSet[Symbol]()

  // ValDefs whose rhs is a case class instantiation: potential candidates.
  val candidates = mutable.HashSet[Symbol]()

  // Immutable sorted map from class to new fields, initialized between visitor and transformer.
  var newFieldsMapping: Map[Symbol, LinkedHashMap[Symbol, Symbol]] = null
  //                          |                     |       |
  //                          |                     |       New fields, replacements these getters
  //                          |                     Usages of getters of these classes
  //                          ValDefs of the classes that are being torn apart; = candidates.intersect(gettersCalled)

  def clear(): Unit = {
    candidates.clear()
    gettersCalled.clear()
    newFieldsMapping = null
  }

  def initNewFieldsMapping()(implicit ctx: Context): Unit =
    if (newFieldsMapping == null) {
      newFieldsMapping = candidates.intersect(gettersCalled).map { refVal =>
        val accessors = refVal.info.classSymbol.caseAccessors.filter(_.isGetter)
        val newLocals = accessors.map { x =>
          val owner: Symbol  = refVal.owner
          val name:  Name    = LocalOptInlineLocalObj.fresh()
          val flags: FlagSet = Synthetic | Mutable
          val info:  Type    = x.asSeenFrom(refVal.info).info.finalResultType.widenDealias
          ctx.newSymbol(owner, name, flags, info)
        }
        (refVal, LinkedHashMap[Symbol, Symbol](accessors.zip(newLocals): _*))
      }.toMap
    }

  


  def visitor(implicit ctx: Context): Tree => Unit = {
    case t: ValDef if isCaseClassDef(t) && shouldInline(t.rhs) =>
      candidates += t.symbol
    case t @ Select(qual, _) if isImmutableAccessor(t) =>
      gettersCalled += qual.symbol
    case _ =>
  }

  def transformer(implicit ctx: Context): Tree => Tree = {
    initNewFieldsMapping();
    {
      case t: ValDef if isCaseClassDef(t) && newFieldsMapping.contains(t.symbol) && candidates.contains(t.symbol) =>
        val newFields     = newFieldsMapping(t.symbol).values.toList
        val newFieldsDefs = newFields.map(nf => ValDef(nf.asTerm, EmptyTree))
        val recreate      = cpy.ValDef(t)(rhs = transformCaseClassCtor(t.symbol, t.rhs))
        simplify.println(s"Replacing ${t.symbol.fullName} with stack-allocated fields ($newFields)")
        Thicket(newFieldsDefs :+ recreate)

      case t @ Select(rec, _) if isImmutableAccessor(t) && candidates.contains(rec.symbol) =>
        newFieldsMapping.getOrElse(rec.symbol, Map.empty[Symbol, Symbol]).get(t.symbol) match {
          case None         => t
          case Some(newSym) => ref(newSym)
        }

      case t => t
    }
  }

  // should we try to inline this rhs ?
  private def shouldInline(tree: Tree)(implicit ctx: Context): Boolean = {
    def score(tree: Tree, forked: Boolean): Int =
      tree match {
        case If(cond, thenp, elsep) => 
          val t = score(thenp, true)
          val e = score(elsep, true)
          if (math.min(t, e) != 0) math.max(t, e)
          else 0
        case Block(stats, expr) => score(expr, forked)
        case Apply(fun, args) if fun.symbol.isConstructor => 2
        case Apply(fun, args) if forked => 1
        case t => 0
      }
    score(tree, false) > 1
  }
    

  // remove lhs ctors from from tree
  private def transformCaseClassCtor(lhs: Symbol, tree: Tree, forked: Boolean = false)(implicit ctx: Context): Tree = 
    tree match {
      case t @ If(cond, thenp, elsep) => 
        If(cond, transformCaseClassCtor(lhs, thenp, true), transformCaseClassCtor(lhs, elsep, true))

      case t @ Block(stats, expr) => 
        Block(stats, transformCaseClassCtor(lhs, expr, forked))

      case t @ Apply(fun, args) if fun.symbol.isConstructor => 
        val newFields        = newFieldsMapping(lhs).values.toList 
        val newFieldsAssigns = newFields.zip(args).map { case (nf, arg) => Assign(ref(nf), arg) }
        val recreate         = fun.appliedToArgs(newFields.map(x => ref(x)))
        Block(newFieldsAssigns, recreate)

      case t: Apply if forked && t.tpe != defn.NothingType => 
        val temp = ctx.newSymbol(ctx.owner, LocalOptInlineLocalObj.fresh(), Synthetic, t.tpe.finalResultType.widenDealias)
        val newFields        = newFieldsMapping(lhs)
        val newFieldsAssigns = newFields.toList.map { case (getter, nf) => Assign(ref(nf), ref(temp).select(getter.name)) }
        Block(ValDef(temp.asTerm, t) +: newFieldsAssigns, ref(temp))

      case t => t
    }


  private def isCaseClassDef(t: ValDef)(implicit ctx: Context): Boolean = 
    t.symbol.info.classSymbol.is(CaseClass)                          && // is rhs a case class?
    !t.symbol.is(Lazy | Mutable)                                     && // is lhs a val?
    !t.symbol.info.classSymbol.caseAccessors.exists(_.is(Mutable))   && // is the case class immutable?
    t.tpe.widenDealias == t.symbol.info.finalResultType.widenDealias
}

