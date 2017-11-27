import FGJPoly._
import org.scalatest._
import Conversions.stringToIdent

class TestParser extends FlatSpec with Matchers {
  "parseVarDecl" should "parse var declarations" in {
    parser.parseVarDecl("Foo f").get should be (VarDecl("f", TClass("Foo", List())))
  }

  "parseExpr" should "parse this expressions" in {
    parser.parseExpr("this").get should be (This)
  }
  "parseExpr" should "parse var expressions" in {
    parser.parseExpr("foo").get should be (Var("foo"))
  }
  "parseExpr" should "parse field expressions" in {
    parser.parseExpr("foo.bar").get should be (Field(Var("foo"), "bar"))
  }
  "parseExpr" should "parse call expressions" in {
    parser.parseExpr("foo.bar(this)").get should be (Call(Var("foo"),List(),"bar",List(This)))
  }
  "parseExpr" should "parse nested fields" in {
    parser.parseExpr("foo.bar.baz").get should be (Field(Field(Var("foo"),"bar"),"baz"))
  }
  "parseExpr" should "parse nested calls" in {
    parser.parseExpr("foo.bar().baz()").get should be (
      Call(Call(Var("foo"), List(), "bar", List()), List(), "baz", List())
    )
  }
  "parseExpr" should "parse method calls with type parameters" in {
    parser.parseExpr("foo.<X,Y>bar()").get should be (
      Call(Var("foo"), List(TClass("X", List()), TClass("Y", List())), "bar", List())
    )
  }
  "parseExpr" should "parse type abstractions" in {
    parser.parseExpr("ΛX.x").get should be(TAbs("X",Right(Top),Var("x")))
  }
  "parseExpr" should "parse type abstractions with extends clauses" in {
    parser.parseExpr("ΛX extends Y.x").get should be(TAbs("X",Right(TClass("Y",List())),Var("x")))
  }
  "parseExpr" should "parse type abstractions with kind annotations" in {
    parser.parseExpr("ΛX:* -> *.x").get should be(TAbs("X",Left(KArr(Star,Star)),Var("x")))
  }
  "parseExpr" should "parse type applications" in {
    parser.parseExpr("x<Top>").get should be(TApp(Var("x"), Top))
  }
  "parseExpr" should "parse kind abstractions" in {
    parser.parseExpr("Λ+X.x").get should be(KAbs("X",Var("x")))
  }
  "parseExpr" should "parse kind applications" in {
    parser.parseExpr("x+<*>").get should be(KApp(Var("x"),Star))
  }

  "parseMethodDecl" should "parse method declarations" in {
    val A = TClass("A", List())
    val decl_a = VarDecl("a", A)
    val m = MethodDecl(List(TVarDecl("A", Right(Top)), TVarDecl("A", Right(A))),
      A, "m", List(decl_a,decl_a), Var("x"))
    parser.parseMethodDecl("<A,A extends A> A m(A a, A a){return x;}").get should be (m)
  }

  "parseClassDecl" should "parse class declarations" in {
    val A = TClass("A", List())
    val decl_a = VarDecl("a", A)
    val m = MethodDecl(List(TVarDecl("A", Right(Top)), TVarDecl("A", Right(A))),
      A, "m", List(decl_a,decl_a), Var("x"))
    val c = ClassDecl(List(TVarDecl("T",Right(Top))), "Foo", A, List(), List(m))
    parser.parseClassDecl("class Foo<T> extends A { <A,A extends A> A m(A a, A a){return x;} }").get should be (c)
  }

  "parseKind" should "parse *" in {
    parser.parseKind("*").get should be (Star)
  }
  "parseKind" should "parse kind variables" in {
    parser.parseKind("X").get should be (KVar("X"))
  }
  "parseKind" should "parse arrow kinds" in {
    parser.parseKind("A -> B -> C").get should be (KArr(KVar("A"),KArr(KVar("B"),KVar("C"))))
  }
  "parseKind" should "parse parenthesized kinds" in {
    parser.parseKind("(A -> B) -> C").get should be (KArr(KArr(KVar("A"),KVar("B")), KVar("C")))
  }
  "parseKind" should "parse quantified kinds" in {
    parser.parseKind("∀X.X -> *").get should be (KForall("X",KArr(KVar("X"),Star)))
  }


  "parseTy" should "parse Top" in {
    parser.parseTy("Top").get should be (Top)
  }
  "parseTy" should "parse quantified types" in {
    val A = TClass("A", List())
    parser.parseTy("∀A.A").get should be (TForallTy("A", Right(Top), A))
  }
  "parseTy" should "parse bounded quantified types" in {
    val A = TClass("A", List())
    val C = TClass("C", List())
    parser.parseTy("∀A. ∀B extends A.C").get should be (TForallTy("A", Right(Top), TForallTy("B", Right(A), C)))
  }
  "parseTy" should "parse quantified types with kind annotations" in {
    val A = TClass("A", List())
    val C = TClass("C", List())
    parser.parseTy("∀A:*.C").get should be (TForallTy("A", Left(Star), C))
  }
  "parseTy" should "parse kind quantified types" in {
    val A = TClass("A", List())
    val C = TClass("C", List())
    parser.parseTy("∀+K. ∀A:K.C").get should be (TForallK("K", TForallTy("A", Left(KVar("K")), C)))
  }

}
