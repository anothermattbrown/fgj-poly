import FGJU._
import org.scalatest._
import FGJU.Conversions._
import Representation._

class TestRepresentation extends FlatSpec with Matchers {
  "SupertypeOf" should "typecheck" in {
    val supertypeOf = parser.parseClassDecl(SupertypeOfSrc)
    new Typechecker().addClassDecl(supertypeOf).tcClassDecl("SupertypeOf")

  }
  "TypeApp" should "typecheck" in {
    val cd = parser.parseClassDecl(TypeAppSrc)
    new Typechecker().addClassDecl(cd).tcClassDecl("TypeApp")
  }
  "TypeApp" should "do instantiations" in {
    val ASrc = "class A<T:*> {}"
    val BSrc = "class B{}"
    val TestSrc =
      """class Test {
        | A<B> go() {
        |   return new TypeApp().<+ *, λT:*.A<T>, B> apply(/\T. new A<T>());
        | }
        |}
      """.stripMargin
    val cds = List(TypeAppSrc, ASrc, BSrc, TestSrc).map(parser.parseClassDecl)
    val tc = new Typechecker().addClassDecls(cds)
    List[Ident]("A","B","Test").foreach(tc.tcClassDecl)
  }

  "UnderTAbs" should "typecheck" in {
    val fun = parser.parseClassDecl(FunSrc)
    val cd = parser.parseClassDecl(UnderTAbsSrc)
    new Typechecker().addClassDecls(List(fun,cd)).tcClassDecl("UnderTAbs")
  }
  "KindApp" should "typecheck" in {
    val cd = parser.parseClassDecl(KindAppSrc)
    new Typechecker().addClassDecl(cd).tcClassDecl("KindApp")
  }

  val srcs = List(
    ("SupertypeOf", SupertypeOfSrc),
    ("Expr",        ExprSrc),
    ("VarExpr",     VarExprSrc),
    ("ThisExpr",    ThisExprSrc),
    ("GetFieldExpr", GetFieldSrc),
    ("CallMethodExpr", CallMethodSrc),
    ("NewObjectExpr", NewObjectSrc),
    ("ExprVisitor", ExprVisitorSrc),
    ("BoundExpr",   BoundExprSrc),
    ("Exprs",       ExprsSrc),
    ("Pair",        PairSrc),
    ("Index",       IndexSrc),
    ("IndexVisitor", IndexVisitorSrc),
    ("IndexZ",       IndexZSrc),
    ("IndexS",       IndexSSrc),
    ("Eq",          EqSrc),
    ("Refl",        ReflSrc),
    ("Fun",         FunSrc),
    ("Class",       ClassSrc),
    ("Obj",         ObjSrc),
  )

  it should "parse all classes" in {
    srcs.foreach({case (nm,src) =>
      try {
        parser.parseClassDecl(src)
      } catch {
        case e : Exception =>
          throw new Exception(s"error parsing $nm", e)
      }
    })
  }

  it should "typecheck all classes" in {
    val nms = srcs.map(_._1)
    val cds = srcs.map(p => parser.parseClassDecl(p._2))
    new Typechecker().addClassDecls(cds)
  }
}