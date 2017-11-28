import FGJU._
import org.scalatest._
import FGJU.Conversions._

class TestRepresentation extends FlatSpec with Matchers {
  "SupertypeOf" should "typecheck" in {
    val supertypeOf = parser.parseClassDecl(Representation.SupertypeOfSrc).get
    new Typechecker().addClassDecl(supertypeOf).tcClassDecl("SupertypeOf")

  }
  "TypeApp" should "typecheck" in {
    val cd = parser.parseClassDecl(Representation.TypeAppSrc).get
    new Typechecker().addClassDecl(cd).tcClassDecl("TypeApp")
  }
  "TypeApp" should "do instantiations" in {
    val ASrc = "class A<T:*> {}"
    val BSrc = "class B{}"
    val TestSrc =
      """class Test {
        | A<B> go() {
        |   return new TypeApp().<+ *, λT:*.A<T>, B> apply(<T> new A<T>());
        | }
        |}
      """.stripMargin
    val cds = List(Representation.TypeAppSrc, ASrc, BSrc, TestSrc).map(parser.parseClassDecl(_).get)
    val tc = new Typechecker().addClassDecls(cds)
    List[Ident]("A","B","Test").foreach(tc.tcClassDecl)
  }

  "UnderTAbs" should "typecheck" in {
    val fun = parser.parseClassDecl(Representation.FunSrc).get
    val cd = parser.parseClassDecl(Representation.UnderTAbsSrc).get
    new Typechecker().addClassDecls(List(fun,cd)).tcClassDecl("UnderTAbs")
  }
  "KindApp" should "typecheck" in {
    print(parser.parseClassDecl(Representation.KindAppSrc))
    val cd = parser.parseClassDecl(Representation.KindAppSrc).get
    new Typechecker().addClassDecl(cd).tcClassDecl("KindApp")
  }

  val srcs = List(
    Representation.SupertypeOfSrc,
    /*
    Representation.StrippedVisitorSrc,
    Representation.StrippedSrc,
    Representation.SomeStrippedSrc,
    */
    Representation.ExprSrc,
    Representation.ExprVisitorSrc,
    Representation.IndexSrc,
    Representation.EqSrc,
    Representation.FunSrc,
    Representation.StripSrc,
    Representation.SomeStripSrc,
  )

  "class decls" should "parse" in {
    val parseSrcs = srcs ++ List(
    )
    parseSrcs.foreach(parser.parseClassDecl(_).get)
  }

  "class decls" should "typecheck" in {
    val decls = srcs.map(parser.parseClassDecl(_).get)
    new Typechecker().addClassDecls(decls)
  }
}