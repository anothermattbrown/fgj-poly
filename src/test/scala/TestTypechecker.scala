import org.scalatest._
import FGJU.Conversions._
import FGJU._


class TestTypechecker extends FlatSpec with Matchers {
  "substTy" should "substitute free type variables" in {
    val fooA = parser.parseTy("Foo<A>").get
    val fooB = parser.parseTy("Foo<B>").get
    val tyB    = parser.parseTy("B").get
    val subst  = Map("A" -> tyB)
    new Typechecker().substTy(Map(),subst,fooA) should be (fooB)
  }
  "substTy" should "not substitute ∀-bound type variables" in {
    val tyPoly = parser.parseTy("∀A.Foo<A>").get
    val tyB    = parser.parseTy("B").get
    val subst  = Map("A" -> tyB)
    new Typechecker().substTy(Map(),subst,tyPoly) should be (tyPoly)
  }
  "substTy" should "not substitute λ-bound type variables" in {
    val ty = parser.parseTy("λA.Foo<A>").get
    val tyB    = parser.parseTy("B").get
    val subst  = Map("A" -> tyB)
    new Typechecker().substTy(Map(),subst,ty) should be (ty)
  }
  "substTy" should "not let kind variables bind type variables" in {
    val fooA = parser.parseTy("ΛA.Foo<A>").get
    val fooB = parser.parseTy("ΛA.Foo<B>").get
    var tyB  = parser.parseTy("B").get
    val subst= Map("A" -> tyB)
    new Typechecker().substTy(Map(),subst,fooA) should be (fooB)
  }
  "substTy" should "not let type variables bind kind variables" in {
    val fooA = parser.parseTy("λA.Foo<+A>").get
    val fooB = parser.parseTy("λA.Foo<+B>").get
    var kB  = parser.parseKind("B").get
    val kSubst= Map("A" -> kB)
    new Typechecker().substTy(kSubst,Map(),fooA) should be (fooB)
  }

  "lookupFieldType" should "handle monomorphic classes" in {
    val cB = parser.parseClassDecl("class B{}").get
    val cA = parser.parseClassDecl("class A { B x; }").get
    val tc = new Typechecker().addClassDecls(List(cB,cA))
    val tyA = parser.parseTy("A").get
    val tyB = parser.parseTy("B").get
    tc.lookupFieldType(tyA, "x") should be(tyB)
  }
  "lookupFieldType" should "handle generic classes" in {
    val cB = parser.parseClassDecl("class B{}").get
    val cA = parser.parseClassDecl("class A<T> { T x; }").get
    val tc = new Typechecker().addClassDecls(List(cB,cA))
    val tyA = parser.parseTy("A<B>").get
    val tyB = parser.parseTy("B").get
    tc.lookupFieldType(tyA, "x") should be(tyB)
  }
  "getParentType" should "handle generic classes" in {
    val cInt    = parser.parseClassDecl("class Int{}").get
    val cFoo    = parser.parseClassDecl("class Foo{}").get
    val cMap    = parser.parseClassDecl("class Map<K,V> {}").get
    val cIntMap = parser.parseClassDecl("class IntMap<T> extends Map<Int,T> {}").get
    val tc = new Typechecker().addClassDecls(List(cInt,cFoo,cMap,cIntMap))
    val sub = parser.parseTy("IntMap<Foo>").get
    val sup = parser.parseTy("Map<Int,Foo>").get
    tc.getParentType(sub) should be(sup)
  }
}
