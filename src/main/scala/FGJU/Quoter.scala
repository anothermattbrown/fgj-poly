package FGJU

import Representation2._

class Quoter(cEnv: Map[Ident, ClassDecl] = Map(),
             kEnv: Set[Ident] = Set(),
             tEnv: Map[Ident, Either[Kind, Type]] = Map(),
             tDefs : Map[Ident,(Kind,Type)] = Map(),
             kDefs : Map[Ident,Kind] = Map(),
             env : Map[Ident, Type] = Map(),
             varOrder : List[Ident] = List(),
             thisType: Option[Type] = None)
  extends Typechecker(cEnv, kEnv, tEnv, tDefs, kDefs, env, thisType) {

  // check invariants
  assert(Set() ++ varOrder == env.keySet)

  val thisTypeSrc : Option[String] = thisType.map(translateType)
  val envTypes : List[String] = varOrder.map(i => translateType(env(i)))

  // override Typechecker methods
  override def addTypeDef(nm: Ident, kind: Kind, defn: Type) : Quoter = {
    val tc : Typechecker = super.addTypeDef(nm, kind, defn)
    new Quoter(cEnv, kEnv, tEnv, tc.tDefs, kDefs, env, varOrder, thisType)
  }

  override def addTypeVar(nm: Ident, kindOrBound: Either[Kind, Type]) : Quoter = {
    val tc : Typechecker = super.addTypeVar(nm, kindOrBound)
    new Quoter(cEnv, kEnv, tc.tEnv, tDefs, kDefs, env, varOrder, thisType)
  }

  override def addVarDecls(decls: List[VarDecl]) : Quoter = {
    val tc : Typechecker = super.addVarDecls(decls)
    new Quoter(cEnv, kEnv, tEnv, tDefs, kDefs, tc.env, varOrder ++ decls.map(d => d.nm), thisType)
  }

  override def addClassDecls(cds: List[ClassDecl]): Quoter = {
    val tc = super.addClassDecls(cds)
    new Quoter(tc.cEnv, kEnv, tEnv, tDefs, kDefs, env, varOrder, thisType)
  }

  override def setThisType(ty: Type): Quoter = {
    new Quoter(cEnv, kEnv, tEnv, tDefs, kDefs, env, varOrder, Some(ty))
  }

  // new translation methods

  def translateClass(cd : ClassDecl) : Expr = {
    null
  }

  def translateType(t : Type) : String = t match {
    case Top => "Pair<Nil,Nil>"
    case TVar(x) => x.nm
  }

  def tupleType(l : List[String]) : String = l.foldRight("Nil")((hd, tl) => s"Pair<$hd,$tl>")

  def newIndex(n : Int, t : List[String]) : String = {
    val hdTy = t.head
    val tlTy = tupleType(t.tail)
    return n match {
      case 0 =>
        s"new IndexZ<${hdTy},${tlTy}>()"
      case _ =>
        val idx = newIndex(n - 1, t.tail)
        s"new IndexS<${hdTy},${tlTy},${t(n)}>($idx)"
    }
  }

  def newVarExpr(i : Ident) : String = {
    var n = varOrder.indexOf(i)
    var t = translateType(env(i))
    var idx = newIndex(n,envTypes)
    s"new VarExpr<${thisTypeSrc.get},${tupleType(envTypes)},$t>($idx)"
  }

  def translateExpr(e : Expr) : Expr = e match {
    case Var(x) => null // newVarExpr(
  }
}
