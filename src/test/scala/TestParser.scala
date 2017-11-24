import FGJPoly._
import org.scalatest._


class TestParser extends FlatSpec with Matchers {
  it should "parse var declarations" in {
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

  "parseExpr" should "parse cast expressions" in {
    var A = TClass("A",List())
    parser.parseExpr("(A)(A)this").get should be (
      Cast(A,Cast(A,This))
    )
  }

  "parseMethodDecl" should "parse method declarations" in {
    val A = TClass("A", List())
    val decl_a = VarDecl("a", A)
    val m = MethodDecl(List(TVarDecl("A", None), TVarDecl("A", Some(A))),
      A, "m", List(decl_a,decl_a), Var("x"))
    parser.parseMethodDecl("<A,A ~> A> A m(A a, A a){return x;}").get should be (m)
  }

  "parseClassDecl" should "parse class declarations" in {
    val A = TClass("A", List())
    val decl_a = VarDecl("a", A)
    val m = MethodDecl(List(TVarDecl("A", None), TVarDecl("A", Some(A))),
      A, "m", List(decl_a,decl_a), Var("x"))
    val c = ClassDecl(List(TVarDecl("T",None)), "Foo", A, List(), List(m))
    parser.parseClassDecl("class Foo<T> extends A { <A,A ~> A> A m(A a, A a){return x;} }").get should be (c)
  }

  "parseTy" should "parse Top" in {
    parser.parseTy("Top").get should be (Top)
  }
  "parseTy" should "parse quantified types" in {
    val A = TClass("A", List())
    val decl_A = TVarDecl("A", None)
    val decl_B = TVarDecl("B", Some(A))
    val C = TClass("C", List())
    parser.parseTy("[A,B ~> A] C").get should be (TForall(List(decl_A,decl_B), C))
  }

}
