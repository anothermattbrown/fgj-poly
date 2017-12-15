import FGJU.Representation2._
import FGJU.{Typechecker, parser}
import org.scalatest.{FlatSpec, Matchers}

class TestRepresentation2 extends FlatSpec with Matchers {

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
    ("Example3", Example3),
    ("Example4", Example4),
    ("Example5", Example5),
    ("Example6", Example6),
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
