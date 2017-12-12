package FGJU

import Representation2._
import scala.collection.immutable.{ListMap, ListSet}
import Printer._

class Quoter(cEnv: ListMap[Ident, ClassDecl] = ListMap(),
             kEnv: ListSet[Ident] = ListSet(),
             tEnv: ListMap[Ident, Either[Kind, Type]] = ListMap(),
             tDefs : ListMap[Ident,(Kind,Type)] = ListMap(),
             kDefs : ListMap[Ident,Kind] = ListMap(),
             env : ListMap[Ident, Type] = ListMap(),
             thisType: Option[Type] = None)
  extends Typechecker(cEnv, kEnv, tEnv, tDefs, kDefs, env, thisType) {

  val thisTypeSrc : Option[String] = thisType.map(quoteType)
  val envNames : List[Ident] = List() ++ env.keys
  val envTypes : List[String] = List() ++ env.map(p => quoteType(p._2))

  // override Typechecker methods
  override def addTypeDef(nm: Ident, kind: Kind, defn: Type) : Quoter = {
    val tc : Typechecker = super.addTypeDef(nm, kind, defn)
    new Quoter(cEnv, kEnv, tEnv, tc.tDefs, kDefs, env, thisType)
  }

  override def addTypeVar(nm: Ident, kindOrBound: Either[Kind, Type]) : Quoter = {
    val tc : Typechecker = super.addTypeVar(nm, kindOrBound)
    new Quoter(cEnv, kEnv, tc.tEnv, tDefs, kDefs, env, thisType)
  }

  override def addVarDecls(decls: List[VarDecl]) : Quoter = {
    val tc : Typechecker = super.addVarDecls(decls)
    new Quoter(cEnv, kEnv, tEnv, tDefs, kDefs, tc.env, thisType)
  }

  override def addClassDecls(cds: List[ClassDecl]): Quoter = {
    val tc = super.addClassDecls(cds)
    new Quoter(tc.cEnv, kEnv, tEnv, tDefs, kDefs, env, thisType)
  }

  override def setThisType(ty: Type): Quoter = {
    new Quoter(cEnv, kEnv, tEnv, tDefs, kDefs, env, Some(ty))
  }

  // new quotation methods
  def quoteClass(cd : ClassDecl) : Expr = {
    null
  }

  def quoteMethodSig(m : MethodSig) : String = {
    val paramTypes : String = tupleType(m.paramTypes.map(quoteType))
    val retType : String = quoteType(m.retTy)
    m.tParams.foldRight(s"BoundExpr<$paramTypes,$retType>")({
      case (GVarDecl(nm, GAType(Left(k))),s) => s"<$nm:${pprintKind(k)}>$s"
      case (GVarDecl(nm, GAKind),s) => s"<+$nm>$s"
    })
  }

  def isObjectType(t: Type) : Boolean = unfoldTypeApps(t) match {
    case Some((nm,_)) => cEnv contains(nm)
    case None => false
  }

  def quoteType(t : Type) : String = t match {
    case Top => "Pair<Nil,Nil>"
    case TVar(x) if tEnv contains(x) => x.nm
    case TForallTy(nm,Left(k),bdy) => s"<$nm:${pprintKind(k)}>${quoteType(bdy)}"
    case TForallK(nm,bdy) => s"<+$nm>${quoteType(bdy)}"
    case TTAbs(nm,Left(k),bdy) => s"λ$nm:${pprintKind(k)}.${quoteType(bdy)}"
    case TKAbs(nm,bdy) => s"Λ$nm.${quoteType(bdy)}"
    case _ if isObjectType(t) =>
      val fieldTypes  : String = tupleType(getFields(t).map(p => quoteType(p._2)))
      val methodTypes : String = tupleType(getMethods(t).map(quoteMethodSig))
      s"Pair<$fieldTypes,$methodTypes>"
    case TTApp(t1,t2) => s"${quoteType(t1)}<${quoteType(t2)}>"
    case TKApp(t1,k)  => s"${quoteType(t1)}<+${pprintKind(k)}>"
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
    var n = envNames.indexOf(i)
    var t = quoteType(env(i))
    var idx = newIndex(n,envTypes)
    s"new VarExpr<${thisTypeSrc.get},${tupleType(envTypes)},$t>($idx)"
  }

  def quoteExpr(e : Expr) : Expr = e match {
    case Var(x) => null // newVarExpr(
  }
}
