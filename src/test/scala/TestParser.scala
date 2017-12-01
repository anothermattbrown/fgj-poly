import org.scalatest._
import FGJU.Conversions._
import FGJU._

class TestParser extends FlatSpec with Matchers {
  "parseVarDecl" should "parse var declarations" in {
    parser.parseVarDecl("Foo f") should be (VarDecl("f", TVar("Foo")))
  }

  "parseExpr" should "parse this expressions" in {
    parser.parseExpr("this") should be (This)
  }
  "parseExpr" should "parse new expressions" in {
    parser.parseExpr("new A()") should be (New("A", List(), List()))
  }
  "parseExpr" should "parse new expressions with generic parameters" in {
    parser.parseExpr("new A<+*,B>()") should be (New("A", List(Left(Star),Right(TVar("B"))), List()))
  }
  "parseExpr" should "parse new expressions with constructor parameters" in {
    parser.parseExpr("new A(x,y)") should be (New("A", List(), List(Var("x"),Var("y"))))
  }
  "parseExpr" should "parse var expressions" in {
    parser.parseExpr("foo") should be (Var("foo"))
  }
  "parseExpr" should "parse field expressions" in {
    parser.parseExpr("foo.bar") should be (Field(Var("foo"), "bar"))
  }
  "parseExpr" should "parse call expressions" in {
    parser.parseExpr("foo.bar(this)") should be (Call(Var("foo"),List(),"bar",List(This)))
  }
  "parseExpr" should "parse nested fields" in {
    parser.parseExpr("foo.bar.baz") should be (Field(Field(Var("foo"),"bar"),"baz"))
  }
  "parseExpr" should "parse nested calls" in {
    parser.parseExpr("foo.bar().baz()") should be (
      Call(Call(Var("foo"), List(), "bar", List()), List(), "baz", List())
    )
  }
  "parseExpr" should "parse method calls with type parameters" in {
    parser.parseExpr("foo.<X,Y>bar()") should be (
      Call(Var("foo"), List(Right(TVar("X")), Right(TVar("Y"))), "bar", List())
    )
  }
  "parseExpr" should "parse type abstractions" in {
    parser.parseExpr("/\\X.x") should be(TAbs("X",Right(Top),Var("x")))
  }
  "parseExpr" should "parse type abstractions with extends clauses" in {
    parser.parseExpr("/\\X extends Y. x") should be(TAbs("X",Right(TVar("Y")),Var("x")))
  }
  "parseExpr" should "parse type abstractions with kind annotations" in {
    parser.parseExpr("/\\X:* -> *. x") should be(TAbs("X",Left(KArr(Star,Star)),Var("x")))
  }
  "parseExpr" should "parse type applications" in {
    parser.parseExpr("x<Top>") should be(TApp(Var("x"), Top))
  }
  "parseExpr" should "parse kind abstractions" in {
    parser.parseExpr("/\\+X.x") should be(KAbs("X",Var("x")))
  }
  "parseExpr" should "parse kind applications" in {
    parser.parseExpr("x<+ *>") should be(KApp(Var("x"),Star))
  }
  "parseExpr" should "parse calls with call receivers" in {
    parser.parseExpr("x.m().n()") should be (
      Call(
        Call(Var("x"),List(),"m",List()),
        List(),
        "n",
        List())
      )
  }
  "parseExpr" should "parse calls with field recievers" in {
    parser.parseExpr("x.f.m()") should be (
      Call(
        Field(Var("x"), "f"),
        List(),
        "m",
        List()
      )
    )
  }
  "parseExpr" should "parse letKind expressions" in {
    parser.parseExpr("letKind X = * in foo") should be (
      KLet("X", Star, Var("foo"))
    )
  }
  "parseExpr" should "parse letType expressions" in {
    parser.parseExpr("letType T : * = Top in foo") should be (
      TLet("T", Star, Top, Var("foo"))
    )
  }
  "parseExpr" should "parse let expressions" in {
    val x = Var("x")
    parser.parseExpr("let x : Top = x in x") should be (
      Let("x",Top,x,x)
    )
  }

  "parseMethodDecl" should "parse method declarations" in {
    val A = TVar("A")
    val decl_a = VarDecl("a", A)
    val m = MethodDecl(List(GVarDecl("A", GAType(Right(Top))), GVarDecl("A", GAType(Right(A)))),
      A, "m", List(decl_a,decl_a), Var("x"))
    parser.parseMethodDecl("<A,A extends A> A m(A a, A a){return x;}") should be (m)
  }
  "parseMethodDecl" should "parse TypeApp's method" in {
    val X = KVar("X")
    val dA = GVarDecl("A", GAType(Left(X)))
    val A = TVar("A")
    val TA = TTApp("T","A")
    val eTy = TForallTy("A", Left(X), TA)
    val m = MethodDecl(List(dA),TA,"apply",List(VarDecl("e",eTy)),TApp(Var("e"),A))
    print(parser.parseMethodDecl("<A:X> T<A> apply(<A:X> T<A> e) { return e<A>; }"))
    parser.parseMethodDecl("<A:X> T<A> apply(<A:X> T<A> e) { return e<A>; }") should be (m)
  }
  "parseMethodDecl" should "parse TypeApp's tester's method" in {
    val src =
      """A<B> go() {
        |  return (new TypeApp()).<+ *, λT:*.A<T>, B> apply(/\T. new A<T>());
        |}
      """.stripMargin
    parser.parseMethodDecl(src)
  }
  "parseMethodDecl" should "parse TupleSubtypeTrans's visitRefl method" in {
    var src =
      """  TupleSubtype<A,C> visitRefl(Eq<A,B> eq) {
        |    return eq.<λT:*. TupleSubtype<T,C>>toLeft(this.subBC);
        |  }
      """.stripMargin
    parser.parseMethodDecl(src)
  }

  "parseClassDecl" should "parse class declarations with fields" in {
    parser.parseClassDecl("class A { B b; }") should be(ClassDecl(List(), "A", Top, List[(String,Type)](("b", "B")), List()))
  }
  "parseClassDecl" should "parse generic class declarations" in {
    val A = TVar("A")
    val decl_a = VarDecl("a", A)
    val m = MethodDecl(
      List(GVarDecl("A", GAType(Right(Top))), GVarDecl("A", GAType(Right(A)))),
      A, "m", List(decl_a,decl_a), Var("x"))
    val c = ClassDecl(List(GVarDecl("T",GAType(Right(Top)))), "Foo", A, List(), List(m))
    parser.parseClassDecl("class Foo<T> extends A { <A,A extends A> A m(A a, A a){return x;} }") should be (c)
  }

  "parseKind" should "parse *" in {
    parser.parseKind("*") should be (Star)
  }
  "parseKind" should "parse kind variables" in {
    parser.parseKind("X") should be (KVar("X"))
  }
  "parseKind" should "parse arrow kinds" in {
    parser.parseKind("A -> B -> C") should be (KArr(KVar("A"),KArr(KVar("B"),KVar("C"))))
  }
  "parseKind" should "parse parenthesized kinds" in {
    parser.parseKind("(A -> B) -> C") should be (KArr(KArr(KVar("A"),KVar("B")), KVar("C")))
  }
  "parseKind" should "parse quantified kinds using forall syntax" in {
    parser.parseKind("∀X.X -> *") should be (KForall("X",KArr(KVar("X"),Star)))
  }
  "parseKind" should "parse quantified kinds using angle-bracket syntax" in {
    parser.parseKind("<X> X -> *") should be (KForall("X",KArr(KVar("X"),Star)))
  }


  "parseTy" should "parse Top" in {
    parser.parseTy("Top") should be (Top)
  }
  "parseTy" should "parse quantified types" in {
    val A = TVar("A")
    parser.parseTy("∀A.A") should be (TForallTy("A", Right(Top), A))
  }
  "parseTy" should "parse bounded quantified types" in {
    val A = TVar("A")
    val C = TVar("C")
    parser.parseTy("∀A. ∀B extends A.C") should be (TForallTy("A", Right(Top), TForallTy("B", Right(A), C)))
  }
  "parseTy" should "parse quantified types with kind annotations" in {
    val A = TVar("A")
    val C = TVar("C")
    parser.parseTy("∀A:*.C") should be (TForallTy("A", Left(Star), C))
  }
  "parseTy" should "parse kind quantified types" in {
    val A = TVar("A")
    val C = TVar("C")
    parser.parseTy("∀+K. ∀A:K.C") should be (TForallK("K", TForallTy("A", Left(KVar("K")), C)))
  }
  "parseTy" should "parse type abstractions" in {
    val A = TVar("A")
    parser.parseTy("λA.A") should be (TTAbs("A", Right(Top), A))
  }
  "parseTy" should "parse type abstractions with extends clauses" in {
    val A = TVar("A")
    val C = TVar("C")
    parser.parseTy("λA. λB extends A.C") should be (TTAbs("A", Right(Top), TTAbs("B", Right(A), C)))
  }
  "parseTy" should "parse type abstractions with kind annotations" in {
    val A = TVar("A")
    val C = TVar("C")
    parser.parseTy("λA:*.C") should be (TTAbs("A", Left(Star), C))
  }
  "parseTy" should "parse kind abstractions" in {
    val A = TVar("A")
    val C = TVar("C")
    parser.parseTy("ΛK. λA:K.C") should be (TKAbs("K", TTAbs("A", Left(KVar("K")), C)))
  }
  "parseTy" should "parse single type applications" in {
    val A = TVar("A")
    val B = TVar("B")
    parser.parseTy("A<B>") should be (TTApp(A,B))
  }
  "parseTy" should "parse two type applications in one list" in {
    val A = TVar("A")
    val B = TVar("B")
    val C = TVar("C")
    parser.parseTy("A<B,C>") should be (TTApp(TTApp(A,B),C))
  }
  "parseTy" should "parse two type applications in two lists" in {
    val A = TVar("A")
    val B = TVar("B")
    val C = TVar("C")
    parser.parseTy("A<B><C>") should be (TTApp(TTApp(A,B),C))
  }
  "parseTy" should "parse single kind applications" in {
    val A = TVar("A")
    val B = KVar("B")
    parser.parseTy("A<+B>") should be (TKApp(A,B))
  }
  "parseTy" should "parse two kind applications in one list" in {
    val A = TVar("A")
    val B = KVar("B")
    val C = KVar("C")
    parser.parseTy("A<+B,+C>") should be (TKApp(TKApp(A,B),C))
  }
  "parseTy" should "parse two kind applications in two lists" in {
    val A = TVar("A")
    val B = KVar("B")
    val C = KVar("C")
    parser.parseTy("A<+B><+C>") should be (TKApp(TKApp(A,B),C))
  }


}
