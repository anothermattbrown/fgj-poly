import FGJU._
import org.scalatest.{FlatSpec, Matchers}
import FGJU.Conversions._
import FGJU.Representation2._

import scala.collection.immutable.ListMap

class TestQuoter extends FlatSpec with Matchers {
  val cds = classDecls.map(p => parser.parseClassDecl(p._2))
  val q = new Quoter().addClassDecls(cds)

  "newIndex(0)" should "parse and typecheck" in {
    val idxSrc = q.newIndex(0, List("A"))
    val e = parser.parseExpr(idxSrc)
    val myTrans = q.addTypeVar("A",Left(Star))
    val t1 = parser.parseTy("IndexZ<A,Nil>")
    val t2 = myTrans.tcExpr(e)
    myTrans.alphaEquivTy(t1,t2) shouldBe (true)

    val sup = parser.parseTy("Index<Pair<A,Nil>,A>")
    myTrans.assertIsSubtypeOf(t2,sup)
  }

  "newIndex(1)" should "parse and typecheck" in {
    val idxSrc = new Quoter().newIndex(1, List("A","B"))
    val e = parser.parseExpr(idxSrc)
    val myTrans = q.addTypeVar("A",Left(Star)).addTypeVar("B",Left(Star))
    val t1 = parser.parseTy("IndexS<A,Pair<B,Nil>,B>")
    val t2 = myTrans.tcExpr(e)
    myTrans.alphaEquivTy(t1,t2) shouldBe (true)

    val sup = parser.parseTy("Index<Pair<A,Pair<B,Nil>>,B>")
    myTrans.assertIsSubtypeOf(t2,sup)
  }

  "quoteSubPairWidths(List(), Nil)" should "parse and typecheck" in {
    val subSrc = q.quoteSubPairWidths(List(), "Nil")
    val sub = parser.parseExpr(subSrc)
    val expectedTy = parser.parseTy("Sub<Nil,Nil>")
    val actualTy = q.tcExpr(sub)
    q.assertIsSubtypeOf(actualTy, expectedTy)
  }

  "quoteSubPairWidths(List(A), Nil)" should "parse and typecheck" in {
    val myQ = q.addTypeVar("A",Left(Star))
    val subSrc = myQ.quoteSubPairWidths(List("A"), "Nil")
    val sub = parser.parseExpr(subSrc)
    val expectedTy = parser.parseTy("Sub<Pair<A,Nil>,Nil>")
    val actualTy = myQ.tcExpr(sub)
    myQ.assertIsSubtypeOf(actualTy, expectedTy)
  }

  "quoteSubPairWidths(List(A,B), Nil)" should "parse and typecheck" in {
    val myQ = q.addTypeVar("A",Left(Star)).addTypeVar("B",Left(Star))
    val subSrc = myQ.quoteSubPairWidths(List("A","B"), "Nil")
    val sub = parser.parseExpr(subSrc)
    val expectedTy = parser.parseTy("Sub<Pair<A,Pair<B,Nil>>,Nil>")
    val actualTy = myQ.tcExpr(sub)
    myQ.assertIsSubtypeOf(actualTy, expectedTy)
  }

  "quoteSubPairWidths(List(A,B), Pair<C,Nil>)" should "parse and typecheck" in {
    val myQ = q.addTypeVar("A",Left(Star)).addTypeVar("B",Left(Star)).addTypeVar("C",Left(Star))
    val subSrc = myQ.quoteSubPairWidths(List("A","B"), "Pair<C,Nil>")
    val sub = parser.parseExpr(subSrc)
    val expectedTy = parser.parseTy("Sub<Pair<A,Pair<B,Pair<C,Nil>>>,Pair<C,Nil>>")
    val actualTy = myQ.tcExpr(sub)
    myQ.assertIsSubtypeOf(actualTy, expectedTy)
  }

  "quoteSubPairDepths(List(), List(), List())" should "parse and typecheck" in {
    val src = q.quoteSubPairDepths(Nil, Nil, Nil)
    var sub = parser.parseExpr(src)
    val expectedTy = parser.parseTy("Sub<Nil,Nil>")
    val actualTy = q.tcExpr(sub)
    q.assertIsSubtypeOf(actualTy,expectedTy)
  }

  "quoteSubPairDepths(List(Pair<A,Nil>), List(Nil), List(quoteSubPairWidths(List(A),Nil))" should "parse and typecheck" in {
    val myQ = q.addTypeVar("A",Left(Star))
    val subWidthSrc = myQ.quoteSubPairWidths(List("A"), "Nil")
    val src = myQ.quoteSubPairDepths(List("Pair<A,Nil>"), List("Nil"), List(subWidthSrc))
    var sub = parser.parseExpr(src)
    println(src)
    val expectedTy = parser.parseTy("Sub<Pair<Pair<A,Nil>,Nil>,Pair<Nil,Nil>>")
    val actualTy = myQ.tcExpr(sub)
    myQ.assertIsSubtypeOf(actualTy,expectedTy)
  }

  "quoteSubPairDepths(List(Pair<A,Nil>,Pair<B,Nil>), List(Nil,Nil), List(quoteSubPairWidths(List(A),Nil),quoteSubPairWidths(List(B),Nil))" should "parse and typecheck" in {
    val myQ = q.addTypeVar("A",Left(Star)).addTypeVar("B",Left(Star))
    val subWidthASrc = myQ.quoteSubPairWidths(List("A"), "Nil")
    val subWidthBSrc = myQ.quoteSubPairWidths(List("B"), "Nil")
    val src = myQ.quoteSubPairDepths(List("Pair<A,Nil>","Pair<B,Nil>"), List("Nil","Nil"), List(subWidthASrc,subWidthBSrc))
    var sub = parser.parseExpr(src)
    println(src)
    val expectedTy = parser.parseTy("Sub<Pair<Pair<A,Nil>,Pair<Pair<B,Nil>,Nil>>,Pair<Nil,Pair<Nil,Nil>>>")
    val actualTy = myQ.tcExpr(sub)
    myQ.assertIsSubtypeOf(actualTy,expectedTy)
  }



  // Variable tests
  """newVarExpr("x")""" should "parse and typecheck" in {
    val myQ : Quoter =
        q
        .setThisType(Top)
        .addTypeVar("A", Left(Star)).addTypeVar("B",Left(Star))
        .addVarDecls(List(VarDecl("x",TVar("A")), VarDecl("y",TVar("B"))))
    val xSrc = myQ.newVarExpr("x")
    val xExpr = parser.parseExpr(xSrc)
    val expectedTy = parser.parseTy("VarExpr<Pair<Nil,Nil>,Pair<A,Pair<B,Nil>>,A>")
    val actualTy = myQ.tcExpr(xExpr)

    myQ.alphaEquivTy(expectedTy,actualTy) should be (true)
  }

}
