import FGJPoly._
import org.scalatest._


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
  "unify" should "unify single type variables" in {
    val tc = new Typechecker()
    val ftvs = Set("A")
    val tyA = parser.parseTy("A").get
    tc.unify(ftvs,tyA,Top) should be(Map("A" -> Top))
  }
  "unify" should "unify type parameters" in {
    val tc = new Typechecker()
    val ftvs = Set("V")
    val ty1 = parser.parseTy("A<V>").get
    val ty2 = parser.parseTy("A<Top>").get
    tc.unify(ftvs,ty1,ty2) should be(Map("V" -> Top))
  }
  "unifySubtype" should "unify type parameters" in {
    val tc = new Typechecker()
    val ftvs = Set("V")
    val ty1 = parser.parseTy("A<V>").get
    val ty2 = parser.parseTy("A<Top>").get
    tc.unifySubtype(ftvs,ty1,ty2) should be(Map("V" -> Top))
  }
  "unifySubtype" should "instantiate variables" in {
    val funDecl = parser.parseClassDecl("class Fun<A,B> {}").get
    val idDecl  = parser.parseClassDecl("class Id<C> extends Fun<C,C> {}").get
    val tc = new Typechecker().addClassDecl(funDecl).addClassDecl(idDecl)
    val sub = parser.parseTy("Id<V>").get
    val sup = parser.parseTy("Fun<Int,Int>").get
    val int = parser.parseTy("Int").get
    tc.unifySubtype(Set("V"), sub, sup) should be(Map("V" -> int))
  }
  "assertIsInstiationOf" should "handle simple instantiations" in {
    val ty1 = parser.parseTy("[T] Foo<T>").get
    val ty2 = parser.parseTy("Foo<Int>").get
    val tc = new Typechecker()
    tc.assertIsInstantiationOf(ty2,ty1)
  }
  "assertIsInstantiationOf" should "handle bounded instantiations" in {
    val A = parser.parseClassDecl("class A{}").get
    val B = parser.parseClassDecl("class B extends A{}").get
    val inst = parser.parseTy("Foo<B>").get
    val forall = parser.parseTy("[T ~> A] Foo<T>").get
    val tc = new Typechecker().addClassDecl(A).addClassDecl(B)
    tc.assertIsInstantiationOf(inst,forall)
  }
  "assertIsInstantiationOf" should "unify type variables" in {
    val A = parser.parseClassDecl("class A{}").get
    val B = parser.parseClassDecl("class B{}").get
    val inst = parser.parseTy("Foo<B>").get
    val forall = parser.parseTy("[T] Foo<A>").get
    val tc = new Typechecker().addClassDecl(A).addClassDecl(B)
    an [Exception] should be thrownBy tc.assertIsInstantiationOf(inst,forall)
  }
  "assertIsInstantiationOf" should "check bounds" in {
    val A = parser.parseClassDecl("class A{}").get
    val B = parser.parseClassDecl("class B{}").get
    val inst = parser.parseTy("Foo<B>").get
    val forall = parser.parseTy("[T ~> A] Foo<T>").get
    val tc = new Typechecker().addClassDecl(A).addClassDecl(B)
    an [Exception] should be thrownBy tc.assertIsInstantiationOf(inst,forall)
  }

}
