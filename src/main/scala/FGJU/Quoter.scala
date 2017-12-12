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

  override def addKindVar(nm: Ident): Quoter = {
    val tc : Typechecker = super.addKindVar(nm)
    new Quoter(cEnv, tc.kEnv, tEnv, tDefs, kDefs, env, thisType)
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
  def quoteGVarDecl(gv : GVarDecl, bdy : String) : String = gv match {
    case GVarDecl(nm, GAType(Left(k))) => s"Λ$nm:${pprintKind(k)}.$bdy"
    case GVarDecl(nm, GAKind) => s"Λ+$nm.$bdy"
  }
  def quoteTypeGVarDecl(gv : GVarDecl, bdy : String) : String = gv match {
    case GVarDecl(nm, GAType(Left(k))) => s"<$nm:${pprintKind(k)}>$bdy"
    case GVarDecl(nm, GAKind) => s"<+$nm>$bdy"
  }

  def classType(cd : ClassDecl) : (Type,Quoter) = {
    cd.params.foldLeft[(Type,Quoter)](TVar(cd.nm), this)({
      case ((t,q), GVarDecl(nm, GAType(kindOrBound))) => (TTApp(t, TVar(nm)), q.addTypeVar(nm,kindOrBound))
      case ((t,q), GVarDecl(nm, GAKind)) => (TKApp(t, KVar(nm)), q.addKindVar(nm))
    })
  }

  def quoteFieldsTupleType(t : Type) : String = tupleType(getFields(t).map(p => quoteType(p._2)))
  def quoteMethodTypes(t : Type) : List[String] = {
    val fieldsTy = quoteFieldsTupleType(t)
    getMethods(t).map(s => s"Fun<$fieldsTy,${quoteMethodSig(s)}>")
  }
  def quoteMethodsTupleTy(t : Type) : String = tupleType(quoteMethodTypes(t))

  def quoteClass(cd : ClassDecl) : String = {
    val (t,q) = classType(cd)
    val fieldsTupleTy = q.quoteFieldsTupleType(t)
    val methodTys = q.quoteMethodTypes(t)
    val methodsTupleTy = q.tupleType(methodTys)
    val superTy = q.quoteType(q.getParentType(t))
    val methods = cd.methods.map(q.quoteMethod)
    val methodsTuple = q.tuple(methods,methodTys)
    val sub = q.quoteSubtypeClass(t)
    cd.params.foldRight(s"new Class<$fieldsTupleTy,$methodsTupleTy,$superTy>($methodsTuple,$sub)")(q.quoteGVarDecl)
  }

  def quoteMethodSig(m : MethodSig) : String = {
    val paramTypes : String = tupleType(m.paramTypes.map(quoteType))
    val retType : String = quoteType(m.retTy)
    m.tParams.foldRight(s"BoundExpr<$paramTypes,$retType>")(quoteTypeGVarDecl)
  }

  def quoteMethod(m : MethodDecl) : String = ""

  def quoteSubtypeClass(t : Type) : String = {
    val p = getParentType(t)
    val fieldsTupleType = quoteFieldsTupleType(t)
    val methodsTupleType = quoteMethodsTupleTy(t)
    val parentFieldsTupleType : String = quoteFieldsTupleType(p)
    val parentMethodsTupleType : String = quoteMethodsTupleTy(p)
    val fieldSub = quoteSubtypeClassFields(t)
    val methodSub = quoteSubtypeClassMethods(t)
    s"new SubPairDepth<$fieldsTupleType,$methodsTupleType,$parentFieldsTupleType,$parentMethodsTupleType>($fieldSub,$methodSub)"
  }

  def quoteSubtypeClassFields(t: Type) : String = {
    val fieldTys = getFields(t)
    val parent = getParentType(t)
    val parentFieldTys = getFields(getParentType(t))

    // fieldTys is an extension of parentFieldTys.
    // Just need to compose SubPairWidth n times, where fieldTys.length = parentFieldTys + n

    // fieldTys should not be shorter than parentFieldTys
    assert(fieldTys.length >= parentFieldTys.length)

    // fieldTys should be a left-extension of parentFieldTys
    val n = fieldTys.length - parentFieldTys.length
    assert(fieldTys.drop(n).zip(parentFieldTys).forall({
      case ((nm1, t1), (nm2, t2)) => nm1 == nm2 && alphaEquivTy(t1, t2)
    }))

    val parentFieldsTupleTy = quoteFieldsTupleType(parent)
    val extraFieldTys = fieldTys.take(n).map(p => quoteType(p._2))
    quoteSubPairWidths(extraFieldTys, parentFieldsTupleTy)
  }

  def quoteSubtypeClassMethods(t : Type) = throw new Exception("TODO: quoteSubtypeClassMethods")

  def quoteSubPairWidths(extraFieldTys: List[String], parentFieldsTupleTy: String) : String = {
    val refl = s"new SubRefl<$parentFieldsTupleTy>()"
    extraFieldTys.foldRight[(String,String)]((parentFieldsTupleTy,refl))({
      case (ty,(midTy,midSub)) => (
        s"Pair<$ty,$midTy>",
        s"new SubTrans<Pair<$ty,$midTy>,$midTy,$parentFieldsTupleTy>(new SubPairWidth<$ty,$midTy>(),$midSub)")
    })._2
  }

  def quoteSubPairDepth(A1 : String, B1 : String, A2 : String, B2 : String, subA : String, subB : String) : String =
    s"new SubPairDepth<$A1,$B1,$A2,$B2>($subA,$subB)"

  def quoteSubPairDepths(subTys : List[String], supTys : List[String], subs : List[String]) : String = (subTys,supTys,subs) match {
    case (Nil, Nil, Nil) => s"new SubRefl<Nil>()"
    case (subTyHd::subTyTl, supTyHd::supTyTl, subsHd::subsTl) =>
      quoteSubPairDepth(subTyHd,tupleType(subTyTl),supTyHd,tupleType(supTyTl),subsHd,quoteSubPairDepths(subTyTl,supTyTl,subsTl))
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
  def tuple(vs : List[String], ts : List[String]) : String = (vs,ts) match {
    case (Nil, Nil) => "new Nil()"
    case (hd :: tl, hdTy :: tlTys) => s"new Pair<$hdTy,${tupleType(tlTys)}>($hd,${tuple(tl,tlTys)})"
  }

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
