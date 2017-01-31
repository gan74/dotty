package generic

import Shapes._

/** enum SearchResult {
 *    case Success(result: Color)
 *    case Diverging
 *    case NoMatch
 *    case Ambiguous(alt1: SearchResult, alt2: SearchResult)
 *  }
 */
sealed trait SearchResult extends Enum

object SearchResult extends EnumValues[SearchResult](2) {

  private def $new(tag: Int, name: String) = new SearchResult {
    def enumTag = tag
    override def toString = name
    registerEnumValue(this)
  }

  abstract case class Success(result: Color) extends SearchResult {
    def enumTag = 0
  }
  object Success {
    def apply(result: Color): SearchResult = new Success(result) {}
    implicit def SuccessShape: Success `shaped` Color =
      new (Success `shaped` Color) {
        def toShape(s: Success) = s.result
        def fromShape(c: Color) = new Success(c) {}
    }
  }

  val Diverging = $new(1, "Diverging")
  val NoMatch = $new(2, "NoMatch")

  abstract case class Ambiguous(alt1: SearchResult, alt2: SearchResult) extends SearchResult {
    def enumTag = 3
  }
  object Ambiguous {
    def apply(alt1: SearchResult, alt2: SearchResult): SearchResult = new Ambiguous(alt1, alt2) {}
    implicit def AmbiguousShape: Ambiguous `shaped` Prod[SearchResult, SearchResult] =
      new (Ambiguous `shaped` Prod[SearchResult, SearchResult]) {
        def toShape(a: Ambiguous) = Prod(a.alt1, a.alt2)
        def fromShape(p: Prod[SearchResult, SearchResult]) = new Ambiguous(p.fst, p.snd) {}
    }
  }

  implicit def SearchResultShape:
    SearchResult `shaped` Sum[Success, Sum[Ambiguous, EnumValue[SearchResult]]] =
    new (SearchResult `shaped` Sum[Success, Sum[Ambiguous, EnumValue[SearchResult]]]) {
      def toShape(x: SearchResult) = x match {
        case x: Success => Fst(x)
        case x: Ambiguous => Snd(Fst(x))
        case x => Snd(Snd(EnumValue(x.enumTag)))
      }
      def fromShape(x: Sum[Success, Sum[Ambiguous, EnumValue[SearchResult]]]): SearchResult = x match {
        case Fst(s) => s
        case Snd(Fst(a)) => a
        case Snd(Snd(ev)) => value(ev.tag)
      }
    }
}