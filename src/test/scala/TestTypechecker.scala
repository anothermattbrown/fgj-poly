import org.scalatest._
import FGJU.Conversions._
import FGJU._


class TestTypechecker extends FlatSpec with Matchers {
  "substTy" should "substitute free type variables" in {
    val fooA = parser.parseTy("Foo<A>")
    val fooB = parser.parseTy("Foo<B>")
    val tyB    = parser.parseTy("B")
    val subst  = Map("A" -> tyB)
    new Typechecker().substTy(Map(),subst,fooA) should be (fooB)
  }
  "substTy" should "not substitute ∀-bound type variables" in {
    val tyPoly = parser.parseTy("∀A.Foo<A>")
    val tyB    = parser.parseTy("B")
    val subst  = Map("A" -> tyB)
    val tc = new Typechecker()
    tc.alphaEquivTy(tc.substTy(Map(),subst,tyPoly), tyPoly) should be (true)
  }
  "substTy" should "not substitute λ-bound type variables" in {
    val ty = parser.parseTy("λA.Foo<A>")
    val tyB    = parser.parseTy("B")
    val subst  = Map("A" -> tyB)
    val tc = new Typechecker()
    tc.alphaEquivTy(tc.substTy(Map(),subst,ty), ty) should be (true)
  }
  "substTy" should "not let kind variables bind type variables" in {
    val fooA = parser.parseTy("ΛA.Foo<A>")
    val fooB = parser.parseTy("ΛA.Foo<B>")
    var tyB  = parser.parseTy("B")
    val subst= Map("A" -> tyB)
    val tc = new Typechecker()
    tc.alphaEquivTy(tc.substTy(Map(),subst,fooA), fooB) should be (true)
  }
  "substTy" should "not let type variables bind kind variables" in {
    val fooA = parser.parseTy("λA.Foo<+A>")
    val fooB = parser.parseTy("λA.Foo<+B>")
    var kB  = parser.parseKind("B")
    val kSubst= Map("A" -> kB)
    val tc = new Typechecker()
    tc.alphaEquivTy(tc.substTy(kSubst,Map(),fooA),fooB) should be (true)
  }

  "lookupFieldType" should "handle monomorphic classes" in {
    val cB = parser.parseClassDecl("class B{}")
    val cA = parser.parseClassDecl("class A { B x; }")
    val tc = new Typechecker().addClassDecls(List(cB,cA))
    val tyA = parser.parseTy("A")
    val tyB = parser.parseTy("B")
    tc.lookupFieldType(tyA, "x") should be(tyB)
  }
  "lookupFieldType" should "handle generic classes" in {
    val cB = parser.parseClassDecl("class B{}")
    val cA = parser.parseClassDecl("class A<T> { T x; }")
    val tc = new Typechecker().addClassDecls(List(cB,cA))
    val tyA = parser.parseTy("A<B>")
    val tyB = parser.parseTy("B")
    tc.lookupFieldType(tyA, "x") should be(tyB)
  }

  "lookupMethodSig" should "handle inheritance" in {
    val cA = parser.parseClassDecl("class A{}")
    val cB = parser.parseClassDecl("class B{ A a() { return new A(); }}")
    val cC = parser.parseClassDecl("class C extends B {}")
    val tc = new Typechecker().addClassDecls(List(cA,cB,cC))
    val tyA = parser.parseTy("A")
    val tyC = parser.parseTy("C")
    tc.lookupMethodSig(tyC, "a").get should be (
      tc.MethodSig(List(), tyA, "a", List())
    )
  }
  "lookupMethodSig" should "avoid capture of generics" in {
    val cF = parser.parseClassDecl("class F<T>{}")
    val cA = parser.parseClassDecl(
      """class A<T> {
        |  <F:* -> *> F<T> a(F<T> x) { return x; }
        |}
      """.stripMargin
    )
    val tc = new Typechecker().addClassDecls(List(cF,cA))
    val tyA = parser.parseTy("A<F<Top>>")
    val tyFTop = parser.parseTy("F<Top>")
    val identF = Ident("F",1)
    val tyFFTop = TTApp(TVar(identF),tyFTop)
    val sigActual = tc.lookupMethodSig(tyA, "a").get
    val sigExpected = tc.MethodSig(
          List(GVarDecl(identF, GAType(Left(KArr(Star,Star))))),
          tyFFTop,
          "a",
          List(tyFFTop))
    tc.assertAlphaEquivMethodSig(sigActual,sigExpected)
  }

  "getParentType" should "handle generic classes" in {
    val cInt    = parser.parseClassDecl("class Int{}")
    val cFoo    = parser.parseClassDecl("class Foo{}")
    val cMap    = parser.parseClassDecl("class Map<K,V> {}")
    val cIntMap = parser.parseClassDecl("class IntMap<T> extends Map<Int,T> {}")
    val tc = new Typechecker().addClassDecls(List(cInt,cFoo,cMap,cIntMap))
    val sub = parser.parseTy("IntMap<Foo>")
    val sup = parser.parseTy("Map<Int,Foo>")
    tc.getParentType(sub) should be(sup)
  }

  "tcExpr" should "typecheck this expressions" in {
    val A = parser.parseClassDecl("class A{}")
    new Typechecker().addClassDecl(A).setThisType(TVar("A")).tcExpr(This) should be (TVar("A"))
  }
  "tcExpr" should "typecheck new expressions" in {
    val A = parser.parseClassDecl("class A{}")
    val e = parser.parseExpr("new A()")
    new Typechecker().addClassDecl(A).tcExpr(e) should be (TVar("A"))
  }
  "tcExpr" should "reject new expressions for undefined classes" in {
    val e = parser.parseExpr("new A()")
    an [Exception] should be thrownBy new Typechecker().tcExpr(e)
  }
  "tcExpr" should "typecheck new expressions with generic parameters" in {
    val A = parser.parseClassDecl("class A<B>{}")
    val e = parser.parseExpr("new A<Top>()")
    new Typechecker().addClassDecl(A).tcExpr(e) should be (TTApp(TVar("A"),Top))
  }
  "tcExpr" should "reject new expressions with too many generic parameters" in {
    val A = parser.parseClassDecl("class A<B>{}")
    val e = parser.parseExpr("new A<Top,Top>()")
    an [Exception] should be thrownBy new Typechecker().addClassDecl(A).tcExpr(e)
  }
  "tcExpr" should "reject new expressions with too few generic parameters" in {
    val A = parser.parseClassDecl("class A<B>{}")
    val e = parser.parseExpr("new A()")
    an [Exception] should be thrownBy new Typechecker().addClassDecl(A).tcExpr(e)
  }
  "tcExpr" should "typecheck new expressions with constructor parameters" in {
    val A = parser.parseClassDecl("class A{}")
    val B = parser.parseClassDecl("class B{A a;}")
    val e = parser.parseExpr("new B(new A())")
    new Typechecker().addClassDecls(List(A,B)).tcExpr(e) should be (TVar("B"))
  }
  "tcExpr" should "allow constructor parameters to be subtypes of field types" in {
    val A = parser.parseClassDecl("class A{}")
    val B = parser.parseClassDecl("class B{Top a;}")
    val e = parser.parseExpr("new B(new A())")
    new Typechecker().addClassDecls(List(A,B)).tcExpr(e) should be (TVar("B"))
  }
  "tcExpr" should "check the types of constructor parameters" in {
    val A = parser.parseClassDecl("class A{}")
    val B = parser.parseClassDecl("class B{}")
    val C = parser.parseClassDecl("class C{A a;}")
    val e = parser.parseExpr("new C(new B())")
    an [Exception] should be thrownBy new Typechecker().addClassDecls(List(A,B,C)).tcExpr(e)
  }
  "tcExpr" should "handle letKind expressions" in {
    val A = parser.parseClassDecl("class A<+X>{}")
    val e = parser.parseExpr("letKind K = * in new A<+K>()")
    val t = parser.parseTy("A<+*>")
    new Typechecker().addClassDecl(A).tcExpr(e) should be(t)
  }
  "tcExpr" should "handle letType expressions" in {
    val A = parser.parseClassDecl("class A<X:*>{}")
    val e = parser.parseExpr("letType T : * = Top in new A<T>()")
    val t = parser.parseTy("A<Top>")
    new Typechecker().addClassDecl(A).tcExpr(e) should be(t)
  }
  "tcExpr" should "consider let-bound type variables equivalent to their definitions" in {
    val A = parser.parseClassDecl("class A<X:*>{}")
    val e = parser.parseExpr(
      """letType T : * = Top in
        |let a : A<Top> = new A<T>() in
        |let b : A<T> = a in
        |a
      """.stripMargin
    )
    val t = parser.parseTy("A<Top>")
    new Typechecker().addClassDecl(A).tcExpr(e) should be(t)
  }
  "tcExpr" should "handle let expressions" in {
    val A = parser.parseClassDecl("class A{}")
    val B = parser.parseClassDecl("class B{A a;}")
    val e = parser.parseExpr("let a : A = new A() in new B(a)")
    val t = parser.parseTy("B")
    new Typechecker().addClassDecls(List(A,B)).tcExpr(e) should be(t)
  }
  "tcExpr" should "require values for superclasses fields" in {
    val A = parser.parseClassDecl("class A {}")
    val B = parser.parseClassDecl("class B {A x;}")
    val C = parser.parseClassDecl("class C extends B {A y;}")
    val e = parser.parseExpr("new C(new A())")
    an [Exception] shouldBe thrownBy (
      new Typechecker().addClassDecls(List(A,B,C)).tcExpr(e)
    )
  }



  "alphaEquivTy" should "be true for syntactically equal types 1" in {
    val A = parser.parseTy("<A> B<A>")
    new Typechecker().alphaEquivTy(A,A) should be(true)
  }
  "alphaEquivTy" should "be true for syntactically equal types 2" in {
    val A = parser.parseTy("B<+A>")
    new Typechecker().alphaEquivTy(A,A) should be(true)
  }

  "alphaEquivK" should "rename kind variables" in {
    val k1 = parser.parseKind("<X> X -> *")
    val k2 = parser.parseKind("<Y> Y -> *")
    new Typechecker().alphaEquivK(k1,k2) should be(true)
  }

  // TODO: test typechecking method bodies

  "assertValidMethodSigOverride" should "allow covariance in return types" in {
    val A = parser.parseClassDecl("class A{}")
    val B = parser.parseClassDecl("class B extends A{}")
    val Foo = parser.parseClassDecl("class Foo{ A m() {return new A(); }}")
    val Bar = parser.parseClassDecl("class Bar extends Foo {B m() {return new B(); }}")
    new Typechecker().addClassDecls(List(A,B,Foo,Bar))
  }
  "assertValidMethodSigOverride" should "disallow contravariance in return types" in {
    val A = parser.parseClassDecl("class A{}")
    val B = parser.parseClassDecl("class B extends A{}")
    val Foo = parser.parseClassDecl("class Foo{ B m() {return new B(); }}")
    val Bar = parser.parseClassDecl("class Bar extends Foo {A m() {return new A(); }}")
    an [Exception] should be thrownBy new Typechecker().addClassDecls(List(A,B,Foo,Bar))
  }
  "assertValidMethodSigOverride" should "allow contravariance in argument types" in {
    val A = parser.parseClassDecl("class A{}")
    val B = parser.parseClassDecl("class B extends A{}")
    val Foo = parser.parseClassDecl("class Foo{ A m(B b) {return b; }}")
    val Bar = parser.parseClassDecl("class Bar extends Foo {A m(A a) {return a; }}")
    new Typechecker().addClassDecls(List(A,B,Foo,Bar))
  }
  "assertValidMethodSigOverride" should "disallow covariance in argument types" in {
    val A = parser.parseClassDecl("class A{}")
    val B = parser.parseClassDecl("class B extends A{}")
    val Foo = parser.parseClassDecl("class Foo{ A m(A a) {return a; }}")
    val Bar = parser.parseClassDecl("class Bar extends Foo {A m(B b) {return b; }}")
    an [Exception] should be thrownBy new Typechecker().addClassDecls(List(A,B,Foo,Bar))
  }
}
