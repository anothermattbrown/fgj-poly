import FGJU._
import org.scalatest.{FlatSpec, Matchers}
import FGJU.Conversions._
import FGJU.Representation2._

import scala.collection.immutable.ListMap

class TestQuoter extends FlatSpec with Matchers {
  val cds = classDecls.map(p => parser.parseClassDecl(p._2))
  val trans = new Quoter().addClassDecls(cds)

  "newIndex(0)" should "parse and typecheck" in {
    val idxSrc = trans.newIndex(0, List("A"))
    val e = parser.parseExpr(idxSrc)
    val myTrans = trans.addTypeVar("A",Left(Star))
    val t1 = parser.parseTy("IndexZ<A,Nil>")
    val t2 = myTrans.tcExpr(e)
    myTrans.alphaEquivTy(t1,t2) shouldBe (true)

    val sup = parser.parseTy("Index<Pair<A,Nil>,A>")
    myTrans.assertIsSubtypeOf(t2,sup)
  }

  "newIndex(1)" should "parse and typecheck" in {
    val idxSrc = new Quoter().newIndex(1, List("A","B"))
    val e = parser.parseExpr(idxSrc)
    val myTrans = trans.addTypeVar("A",Left(Star)).addTypeVar("B",Left(Star))
    val t1 = parser.parseTy("IndexS<A,Pair<B,Nil>,B>")
    val t2 = myTrans.tcExpr(e)
    myTrans.alphaEquivTy(t1,t2) shouldBe (true)

    val sup = parser.parseTy("Index<Pair<A,Pair<B,Nil>>,B>")
    myTrans.assertIsSubtypeOf(t2,sup)
  }

  // Variable tests
  """newVarExpr("x")""" should "parse and typecheck" in {
    val myTrans : Quoter =
        trans
        .setThisType(Top)
        .addTypeVar("A", Left(Star)).addTypeVar("B",Left(Star))
        .addVarDecls(List(VarDecl("x",TVar("A")), VarDecl("y",TVar("B"))))
    val xSrc = myTrans.newVarExpr("x")
    val xExpr = parser.parseExpr(xSrc)
    val expectedTy = parser.parseTy("VarExpr<Pair<Nil,Nil>,Pair<A,Pair<B,Nil>>,A>")
    val actualTy = myTrans.tcExpr(xExpr)

    myTrans.alphaEquivTy(expectedTy,actualTy) should be (true)
  }

}
