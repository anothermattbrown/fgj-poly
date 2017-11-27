import FGJU.{Representation, Typechecker, parser}
import org.scalatest._
import FGJU.Conversions._

class TestRepresentation extends FlatSpec with Matchers {
  "SupertypeOf" should "typecheck" in {
    val supertypeOf = parser.parseClassDecl(Representation.SupertypeOfSrc).get
    new Typechecker().addClassDecl(supertypeOf).tcClassDecl("SupertypeOf")

  }
  "TypeApp" should "typecheck" in {
    print(parser.parseClassDecl(Representation.TypeAppSrc))
    val cd = parser.parseClassDecl(Representation.TypeAppSrc).get
    new Typechecker().addClassDecl(cd).tcClassDecl("TypeApp")
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