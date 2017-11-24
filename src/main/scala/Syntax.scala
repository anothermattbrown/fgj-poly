package FGJPoly {

  sealed trait Type
  case object Top extends Type
  case class TClass(nm: String, params: List[Type]) extends Type
  case class TForall(tVars: List[TVarDecl], ty: Type) extends Type

  sealed trait Expr
  case object This extends Expr
  case class Var(nm: String) extends Expr
  case class Field(obj: Expr, nm: String) extends Expr
  case class Call(obj: Expr, tParams: List[Type], nm: String, params: List[Expr]) extends Expr
  case class Cast(ty:Type, e:Expr) extends Expr

  case class ClassDecl(params: List[TVarDecl],
                       nm: String,
                       superClass: Type,
                       fields: List[VarDecl],
                       methods: List[MethodDecl])

  case class VarDecl(nm: String, ty: Type)

  case class TVarDecl(nm: String, upperBound: Option[Type])

  case class MethodDecl(tParams: List[TVarDecl], retTy: Type, nm: String, params: List[VarDecl], bdy: Expr)

  class Program(classDecls: List[ClassDecl], expr: Expr)

}