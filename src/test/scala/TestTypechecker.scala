import FGJPoly._
import org.scalatest._

import Conversions._


class TestTypechecker extends FlatSpec with Matchers {
  "substTy" should "not substitute bound type variables" in {
    val tyPoly = parser.parseTy("[A]Foo<A>").get
    val tyB    = parser.parseTy("B").get
    val subst  = Map("A" -> tyB)
    new Typechecker().substTy(subst,tyPoly) should be (tyPoly)
  }
  "lookupFieldType" should "handle monomorphic classes" in {
    val cd = parser.parseClassDecl("class A { B x; }").get
    val tc = new Typechecker().addClassDecl(cd)
    val tyA = parser.parseTy("A").get
    val tyB = parser.parseTy("B").get
    tc.lookupFieldType(tyA, "x") should be(tyB)
  }
  "lookupFieldType" should "handle generic classes" in {
    val cd = parser.parseClassDecl("class A<T> { T x; }").get
    val tc = new Typechecker().addClassDecl(cd)
    val tyA = parser.parseTy("A<B>").get
    val tyB = parser.parseTy("B").get
    tc.lookupFieldType(tyA, "x") should be(tyB)
  }
  "getParentType" should "handle generic classes" in {
    val cd = parser.parseClassDecl("class IntMap<T> extends Map<Int,T> {}").get
    val tc = new Typechecker().addClassDecl(cd)
    val sub = parser.parseTy("IntMap<Foo>").get
    val sup = parser.parseTy("Map<Int,Foo>").get
    tc.getParentType(sub) should be(sup)
  }
}
