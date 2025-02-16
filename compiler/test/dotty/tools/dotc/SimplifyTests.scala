package dotty.tools.dotc

import org.junit.Assert._
import org.junit.Test
import dotty.tools.backend.jvm._
import dotty.tools.dotc.config.CompilerCommand
import dotty.tools.dotc.core.Contexts.FreshContext
import scala.tools.asm.tree.MethodNode

class SimplifyPosTests extends SimplifyTests(optimise = true)
class SimplifyNegTests extends SimplifyTests(optimise = false)

abstract class SimplifyTests(val optimise: Boolean) extends DottyBytecodeTest {
  override protected def initializeCtx(c: FreshContext): Unit = {
    super.initializeCtx(c)
    if (optimise) {
      val flags = Array("-optimise") // :+ "-Xprint:simplify"
      val summary = CompilerCommand.distill(flags)(c)
      c.setSettings(summary.sstate)
    }
  }

  def checkNotEquals(source: String, expected: String, shared: String = ""): Unit = 
    check(source, expected, shared, false)

  def check(source: String, expected: String, shared: String = "", equal: Boolean = true): Unit = {
    import ASMConverters._
    val src =
      s"""
      $shared
      |class A {
      |  def main(): Unit = {
            $source
      |  }
      |}
      |class B {
      |  def main(): Unit = {
            $expected
      |  }
      |}
      """.stripMargin
    checkBCode(src) { dir =>
      def instructions(clazz: String): List[Instruction] = {
        val clsIn   = dir.lookupName(s"$clazz.class", directory = false).input
        val clsNode = loadClassNode(clsIn)
        instructionsFromMethod(getMethod(clsNode, "main"))
      }
      val A = instructions("A")
      val B = instructions("B")
      val diff = diffInstructions(A, B)
      if (optimise)
        assert(if (equal) A == B else A != B, s"Bytecode doesn't match: (lhs = source, rhs = expected) \n$diff")
      else
        assert(A != B, s"Same Bytecodes without -optimise: you are testing the wrong thing!")
    }
  }

  @Test def inlineVals =
    check("println(1)",
       """
          |val one = 1
          |val anotherone = one
          |println(anotherone)
       """)

  @Test def inlineCaseIntrinsicsDottyApply =
    check(
      source   = "CC.apply(1, 2)",
      expected = "new CC(1, 2)",
      shared   = "case class CC(i: Int, j: Int)")

  @Test def inlineCaseIntrinsicsScalacApply =
    check("::.apply(1, Nil)", "new ::(1, Nil)")

  @Test def inlineCaseIntrinsicsScalacUnapply =
    check(
      """
         |val t = Tuple2(1, "s")
         |print(Tuple2.unapply(t))
      """,
      """
         |print(new Some(new Tuple2(1, "s")))
      """)

  @Test def dropNoEffects =
    check(
      """
         |val a = "wow"
         |print(1)
      """,
      """
         |print(1)
      """)

  @Test def dropNoEffectsTuple =
    check("new Tuple2(1, 3)", "")

  @Test def inlineLocalObjects =
    check(
      """
         |val t = new Tuple2(1, 3)
         |print(t._1 + t._2)
      """,
      """
         |val i = 3
         |print(1 + i) // Prevents typer from constant folding 1 + 3 to 4
      """)

  @Test def inlineOptions =
    check(
      """
         |val sum = Some("s")
         |println(sum.isDefined)
      """,
      """
         |println(true)
      """)


  /*
   * Valify tests
   */ 

 @Test def valifyInlinedObjects =
  check(
    """
       |var t = new Tuple2(1, 3)
       |print(t._1 + t._2)
    """,
    """
       |print(4)
    """)

 @Test def valifySimpleVar =
  check(
    """
       |var t = 1
       |print(t + 1)
    """,
    """
       |print(2)
    """)

  @Test def valifyConditional =
    check(
      """
        |var i = 0
        |if(readBoolean()) {
        |  i = 4
        |  print(i)
        |}
        |i = 5
        |print(i)
      """,
      """
        |var i = 0
        |if(readBoolean()) {
        |  i = 4
        |  print(4)
        |}
        |print(5)
      """)

  @Test def valifyPartial =
    check(
      """
        |var i = 0
        |if(readBoolean()) i = 4
        |print(i)
        |i = 5
        |print(i)
      """,
      """
        |var i = 0
        |if(readBoolean()) i = 4
        |print(i)
        |print(5)
      """)

  @Test def valifyDropPartial =
    check(
      """
        |var i = 1
        |i = 2
        |i = i + 2
        |print(i)
      """,
      """
        |print(4)
      """)

  @Test def valifyVarVal =
    check(
      """
        |val cst = readInt()
        |var i = cst
        |print(i)
      """,
      """
        |val i = readInt()
        |print(i)
      """)

  @Test def valifyValVar =
    check(
      """
        |var i = 7
        |val cst = i
        |print(cst)
      """,
      """
        |print(7)
      """)

  // check for incorrecly eliminated statements with side effects 
  @Test def valifySideEffects =
    checkNotEquals(
      """
        |val ar = Array.ofDim[Int](5)
      """, """""")

  @Test def valifyAdvancedSideEffects =
    checkNotEquals(
      """
        |val ar = Array.ofDim[Int](5)
        |var x = 0
        |while (x <= 5) {
        |  print(x)
        |  val a = ar(x)
        |  x += 1
        |}
      """,
      """
        |val ar = Array.ofDim[Int](5)
        |var x = 0
        |while (x <= 5) {
        |  print(x)
        |  x += 1
        |}
      """)


  /*
   * Constant folding tests
   */

  @Test def basicConstantFold =
    check(
      """
        |val i = 3
        |val j = i + 4
        |print(j)
      """,
      """
        |print(7)
      """)

  @Test def branchConstantFold =
    check(
      """
         |val t = true // val needed, or typer takes care of this
         |if (t) print(1)
         |else   print(2)
      """,
      """
         |print(1)
      """)

  @Test def arithmeticConstantFold =
    check(
      """
        |val i = 3
        |val j = i + 4
        |if(j - i >= (i + 1) / 2) 
        |  print(i + 1)
      """,
      """
        |print(4)
      """)

  @Test def twoValConstantFold =
    check(
      """
        |val i = 3
        |val j = 4
        |val k = i * j
        |print(k - j)
      """,
      """
        |print(8)
      """)

  // @Test def listPatmapExample =
  //   check(
  //     """
  //        |val l = 1 :: 2 :: Nil
  //        |l match {
  //        |  case Nil => print("nil")
  //        |  case x :: xs => print(x)
  //        |}
  //     """,
  //     """TODO
  //     """)

  // @Test def fooCCExample =
  //   check(
  //     source   =
  //     """
  //       |val x: Any = new Object {}
  //       |val (a, b) = x match {
  //       |  case CC(s @ 1, CC(t, _)) =>
  //       |    (s , 2)
  //       |  case _ => (42, 43)
  //       |}
  //       |a + b
  //     """,
  //     expected =
  //     """TODO
  //     """,
  //     shared   = "case class CC(a: Int, b: Object)")

  // @Test def booleansFunctionExample =
  //   check(
  //     """
  //     |val a: Any = new Object {}
  //     |val (b1, b2) = (a.isInstanceOf[String], a.isInstanceOf[List[Int]])
  //     |(b1, b2) match {
  //     |  case (true, true) => true
  //     |  case (false, false) => true
  //     |  case _ => false
  //     |}
  //     """,
  //     """
  //     |val a: Any = new Object {}
  //     |val bl = a.isInstanceOf[List[_]]
  //     |val bl2 = a.isInstanceOf[String]
  //     |if (true == bl2 && true == bl)
  //     |  true
  //     |else
  //     |  false == bl2 && false == bl
  //     """)
}
