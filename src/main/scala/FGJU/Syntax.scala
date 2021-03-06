package FGJU

case class Ident(nm : String, id : Int) {
  override def toString: String = nm + id
}

object freshen {
  def apply(i:Ident) : Ident = i match { case Ident(nm,_) => Ident(nm,uniqueId()) }
}

object uniqueId {
  var counter : Int = 0
  def apply() : Int = {
    counter += 1
    counter
  }
}

object Conversions {
  implicit def stringToIdent(nm: String) = Ident(nm, 0)
  implicit def stringMapToIdentMap[A](m : Map[String,A]) : Map[Ident,A] = m.map({case (k,v) => (stringToIdent(k),v)})
  implicit def stringToType(nm:String) = TVar(nm)
}

sealed trait Type
case object Top extends Type
case class TVar(nm:Ident) extends Type
//case class TClass(nm: Ident, params: List[Either[Kind,Type]]) extends Type
// quantification of base types (kind *) has an upper bound.
// quantification of type constructors (kind k1 -> k2) does not have an upper bound.
case class TForallTy(nm : Ident, kindOrBound:Either[Kind,Type], bdy: Type) extends Type
case class TForallK(nm : Ident, bdy: Type) extends Type
case class TTAbs(nm : Ident, kindOrBound : Either[Kind,Type], bdy:Type) extends Type
case class TTApp(t1 : Type, t2 : Type) extends Type
case class TKAbs(nm : Ident, bdy:Type) extends Type
case class TKApp(t : Type, k : Kind) extends Type

sealed trait Kind
case object Star extends Kind
case class KVar(nm : Ident) extends Kind
case class KArr(k1 : Kind, k2 : Kind) extends Kind
case class KForall(nm:Ident, k:Kind) extends Kind

sealed trait Expr
case object This extends Expr
case class New(nm:Ident, gParams:List[Either[Kind,Type]], params : List[Expr]) extends Expr
case class Var(nm: Ident) extends Expr
case class Field(e: Expr, nm: String) extends Expr
case class Call(e: Expr, gParams: List[Either[Kind,Type]], nm: String, params: List[Expr]) extends Expr
case class TAbs(nm : Ident, kindOrBound:Either[Kind,Type], e : Expr) extends Expr
case class KAbs(nm : Ident, e : Expr) extends Expr
case class TApp(e:Expr, t : Type) extends Expr
case class KApp(e:Expr, k : Kind) extends Expr

// syntactic sugar. desugar KLet and TLet using KAbs and TAbs.
// desugar Let using a built-in Fun class (worry about that later)
case class KLet(nm:Ident, k:Kind, bdy:Expr) extends Expr
case class TLet(nm:Ident, k:Kind, t:Type, bdy:Expr) extends Expr
case class Let(nm:Ident, t:Type, e:Expr, bdy:Expr) extends Expr

case class ClassDecl(params: List[GVarDecl],
                     nm: Ident,
                     superClass: Type,
                     fields: List[(String,Type)],
                     methods: List[MethodDecl])

case class VarDecl(nm: Ident, ty: Type)

case class GVarDecl(nm: Ident, ann : GenericAnnotation)

sealed trait GenericAnnotation
object GAKind extends GenericAnnotation
case class GAType(kindOrBound : Either[Kind,Type]) extends GenericAnnotation

case class MethodDecl(tParams: List[GVarDecl], retTy: Type, nm: String, params: List[VarDecl], bdy: Expr)

class Program(classDecls: List[ClassDecl], expr: Expr)

object foldTypeApps {
  def apply(nm: Ident, params: List[Either[Kind, Type]]): Type =
    params.foldLeft[Type](TVar(nm))({
      case (t1, Left(k)) => TKApp(t1, k)
      case (t1, Right(p)) => TTApp(t1, p)
    })
}

object unfoldTypeApps {
  def apply(t: Type): Option[(Ident, List[Either[Kind, Type]])] = t match {
    case TVar(nm) => Some(nm, List())
    case TTApp(t1, param) =>
      unfoldTypeApps(t1).map({
        case (nm, params) => (nm, params ++ List(Right(param)))
      })
    case TKApp(t1, param) =>
      unfoldTypeApps(t1).map({
        case (nm, params) => (nm, params ++ List(Left(param)))
      })
    case _ => None
  }
}
