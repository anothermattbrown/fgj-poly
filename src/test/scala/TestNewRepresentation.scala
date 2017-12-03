import FGJU.NewRepresentation._
import FGJU.{Typechecker, parser}
import org.scalatest.{FlatSpec, Matchers}

class TestNewRepresentation extends FlatSpec with Matchers {

  val classDecls = List(
    ("Sub",            SubSrc),
    ("SubRefl",        SubReflSrc),
    ("SubTrans",       SubTransSrc),
    ("SubPairDepth",        SubPairDepthSrc),
    ("SubPairWidth",        SubPairWidthSrc),
    ("Expr",        ExprSrc),
    /*
    ("VarExpr",     VarExprSrc),
    ("ThisExpr",    ThisExprSrc),
    ("GetFieldExpr", GetFieldSrc),
    ("CallMethodExpr", CallMethodSrc),
    */
    ("NewExpr", NewExprSrc),
    ("CallExpr", CallExprSrc),
    ("ExprVisitor", ExprVisitorSrc),
    ("Pair",        PairSrc),
    ("Nil",         NilSrc),
    ("Index",       IndexSrc),
    ("IndexZ",      IndexZSrc),
    ("IndexS",      IndexSSrc),
    ("Eq",          EqSrc),
    ("Refl",        ReflSrc),
    ("Fun",         FunSrc),
    ("Class",       ClassSrc),
    ("FunsNil",     FunsNilSrc),
    ("FunsCons",    FunsConsSrc),
    ("Exprs",       ExprsSrc),
    ("ExprsVisitor", ExprsVisitorSrc),
    ("NilExprs",    NilExprsSrc),
    ("ConsExprs",   ConsExprsSrc),
    ("BoundExpr",   BoundExprSrc),
    ("BoundExprVisitor", BoundExprVisitorSrc),
    ("SomeBoundExpr", SomeBoundExprSrc),
    ("ExprBinder",    ExprBinderSrc),
    ("Lazy",          LazySrc),
    ("Constructor",   ConstructorSrc),
    ("BindMethodsNil", BindMethodsNilSrc),
    ("BindMethodsCons", BindMethodsConsSrc),
    ("EvalExpr",        EvalExprSrc),
    ("EvalExprs",       EvalExprsSrc),
    ("EvalBoundExpr", EvalBoundExprSrc),

  )

  it should "parse all classes" in {
    classDecls.foreach({case (nm,src) =>
      try {
        parser.parseClassDecl(src)
      } catch {
        case e : Exception =>
          throw new Exception(s"error parsing $nm", e)
      }
    })
  }

  it should "typecheck all classes" in {
    val cds = classDecls.map(p => parser.parseClassDecl(p._2))
    new Typechecker().addClassDecls(cds)
  }

  val examples : List[(String,String)] = List(
    ("Example1", Example1),
    ("Example2", Example2),
  )

  it should "typecheck all examples" in {
    val cds = classDecls.map(p => parser.parseClassDecl(p._2))
    val tc = new Typechecker().addClassDecls(cds)

    examples.foreach({case (nm,src) =>
      val stx = try {
        parser.parseExpr(src)
      } catch {
        case e : Exception =>
          throw new Exception(s"error parsing $nm", e)
      }

      try {
        val ty = tc.tcExpr(stx)
        print(s"$nm type: $ty")
      } catch {
        case e : Exception =>
          throw new Exception(s"error typechecking $nm", e)
      }
    })
  }
}
