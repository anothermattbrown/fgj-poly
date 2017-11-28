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

  "tcExpr" should "typecheck this expressions" in {
    val A = parser.parseClassDecl("class A{}").get
    new Typechecker().addClassDecl(A).setThisType(TVar("A")).tcExpr(This) should be (TVar("A"))
  }
  "tcExpr" should "typecheck new expressions" in {
    val A = parser.parseClassDecl("class A{}").get
    val e = parser.parseExpr("new A()").get
    new Typechecker().addClassDecl(A).tcExpr(e) should be (TVar("A"))
  }
  "tcExpr" should "reject new expressions for undefined classes" in {
    val e = parser.parseExpr("new A()").get
    an [Exception] should be thrownBy new Typechecker().tcExpr(e)
  }
  "tcExpr" should "typecheck new expressions with generic parameters" in {
    val A = parser.parseClassDecl("class A<B>{}").get
    val e = parser.parseExpr("new A<Top>()").get
    new Typechecker().addClassDecl(A).tcExpr(e) should be (TTApp(TVar("A"),Top))
  }
  "tcExpr" should "reject new expressions with too many generic parameters" in {
    val A = parser.parseClassDecl("class A<B>{}").get
    val e = parser.parseExpr("new A<Top,Top>()").get
    an [Exception] should be thrownBy new Typechecker().addClassDecl(A).tcExpr(e)
  }
  "tcExpr" should "reject new expressions with too few generic parameters" in {
    val A = parser.parseClassDecl("class A<B>{}").get
    val e = parser.parseExpr("new A()").get
    an [Exception] should be thrownBy new Typechecker().addClassDecl(A).tcExpr(e)
  }
  "tcExpr" should "typecheck new expressions with constructor parameters" in {
    val A = parser.parseClassDecl("class A{}").get
    val B = parser.parseClassDecl("class B{A a;}").get
    val e = parser.parseExpr("new B(new A())").get
    new Typechecker().addClassDecls(List(A,B)).tcExpr(e) should be (TVar("B"))
  }
  "tcExpr" should "allow constructor parameters to be subtypes of field types" in {
    val A = parser.parseClassDecl("class A{}").get
    val B = parser.parseClassDecl("class B{Top a;}").get
    val e = parser.parseExpr("new B(new A())").get
    new Typechecker().addClassDecls(List(A,B)).tcExpr(e) should be (TVar("B"))
  }
  "tcExpr" should "check the types of constructor parameters" in {
    val A = parser.parseClassDecl("class A{}").get
    val B = parser.parseClassDecl("class B{}").get
    val C = parser.parseClassDecl("class C{A a;}").get
    val e = parser.parseExpr("new C(new B())").get
    an [Exception] should be thrownBy new Typechecker().addClassDecls(List(A,B,C)).tcExpr(e)
  }

  "alphaEquivTy" should "be true for syntactically equal types 1" in {
    val A = parser.parseTy("<A> B<A>").get
    new Typechecker().alphaEquivTy(A,A) should be(true)
  }
  "alphaEquivTy" should "be true for syntactically equal types 2" in {
    val A = parser.parseTy("B<+A>").get
    new Typechecker().alphaEquivTy(A,A) should be(true)
  }

  // TODO: test typechecking method bodies
}
