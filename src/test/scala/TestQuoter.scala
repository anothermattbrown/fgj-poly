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

  "quoteSubtypeClassMethods for a class with no methods" should "parse and typecheck" in {
    val A = parser.parseClassDecl("class A{}")
    val myQ = q.addClassDecl(A)
    val src = myQ.quoteSubtypeClassMethods(TVar("A"))
    val sub = parser.parseExpr(src)
    val actualTy = myQ.tcExpr(sub)
  }

  "quoteSubTy" should "handle reflexivity" in {
    val A = parser.parseClassDecl("class A{}")
    val myQ = q.addClassDecl(A)
    val tyA = TVar("A")
    val src = myQ.quoteSubtypeType(tyA,tyA)
    val sub = parser.parseExpr(src)
    val expectedTy = parser.parseTy("SubRefl<Pair<Nil,Nil>>")
    val actualTy = myQ.tcExpr(sub)
    myQ.assertIsSubtypeOf(actualTy,expectedTy)
  }

  "quoteSubTy" should "handle Top subtypings" in {
    val A = parser.parseClassDecl("class A{ Top f; }")
    val myQ = q.addClassDecl(A)
    val tyA = TVar("A")
    val src = myQ.quoteSubtypeType(tyA,Top)
    val sub = parser.parseExpr(src)
    val expectedTy = parser.parseTy(s"SubTop<${myQ.quoteType(tyA)}>")
    val actualTy = myQ.tcExpr(sub)
    myQ.assertIsSubtypeOf(actualTy,expectedTy)
  }

  "quoteSubTy" should "handle type-quantified types" in {
    val A = parser.parseClassDecl("class A{}")
    val myQ = q.addClassDecl(A)
    val tySub = parser.parseTy("<X:*>A")
    val qTySub = myQ.quoteType(tySub)
    val tySup = parser.parseTy("<X:*>Top")
    val qTySup = myQ.quoteType(tySup)
    val src = myQ.quoteSubtypeType(tySub,tySup)
    val sub = parser.parseExpr(src)
    val expectedTy = parser.parseTy(s"Sub<$qTySub, $qTySup>")
    val actualTy = myQ.tcExpr(sub)
    myQ.assertIsSubtypeOf(actualTy, expectedTy)
  }

  "quoteSubTy" should "handle kind-quantified types" in {
    val A = parser.parseClassDecl("class A{}")
    val myQ = q.addClassDecl(A)
    val tySub = parser.parseTy("<+X>A")
    val qTySub = myQ.quoteType(tySub)
    val tySup = parser.parseTy("<+X>Top")
    val qTySup = myQ.quoteType(tySup)
    val src = myQ.quoteSubtypeType(tySub,tySup)
    val sub = parser.parseExpr(src)
    val expectedTy = parser.parseTy(s"Sub<$qTySub, $qTySup>")
    val actualTy = myQ.tcExpr(sub)
    myQ.assertIsSubtypeOf(actualTy, expectedTy)
  }

  "quoteSubTy" should "handle transitive subtypings" in {
    val A = parser.parseClassDecl("class A{}")
    val B = parser.parseClassDecl("class B extends A{Top f;}")
    val C = parser.parseClassDecl("class C extends B{Top g;}")
    val myQ = q.addClassDecls(List(A,B,C))
    val tySub = parser.parseTy("C")
    val qTySub = myQ.quoteType(tySub)
    val tySup = parser.parseTy("A")
    val qTySup = myQ.quoteType(tySup)
    val src = myQ.quoteSubtypeType(tySub,tySup)
    val sub = parser.parseExpr(src)
    val expectedTy = parser.parseTy(s"Sub<$qTySub, $qTySup>")
    val actualTy = myQ.tcExpr(sub)
    myQ.assertIsSubtypeOf(actualTy, expectedTy)
  }

  "quoteSubTy" should "handle width subtyping of methods" in {
    val A = parser.parseClassDecl("class A{}")
    val B = parser.parseClassDecl("class B extends A{Top m(Top x){ return x; }}")
    val myQ = q.addClassDecls(List(A,B))
    val tySub = parser.parseTy("B")
    val qTySub = myQ.quoteType(tySub)
    val tySup = parser.parseTy("A")
    val qTySup = myQ.quoteType(tySup)
    val src = myQ.quoteSubtypeType(tySub,tySup)
    val sub = parser.parseExpr(src)
    val expectedTy = parser.parseTy(s"Sub<$qTySub, $qTySup>")
    val actualTy = myQ.tcExpr(sub)
    myQ.assertIsSubtypeOf(actualTy, expectedTy)
  }

  "quoteSubTy" should "handle depth subtyping of methods" in {
    val A = parser.parseClassDecl("class A{A m(A a) {return a;} }")
    val B = parser.parseClassDecl("class B extends A{B m(Top x){ return this; }}")
    val myQ = q.addClassDecls(List(A,B))
    val tySub = parser.parseTy("B")
    val qTySub = myQ.quoteType(tySub)
    val tySup = parser.parseTy("A")
    val qTySup = myQ.quoteType(tySup)
    val src = myQ.quoteSubtypeType(tySub,tySup)
    val sub = parser.parseExpr(src)
    val expectedTy = parser.parseTy(s"Sub<$qTySub, $qTySup>")
    val actualTy = myQ.tcExpr(sub)
    myQ.assertIsSubtypeOf(actualTy, expectedTy)
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
