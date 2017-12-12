package FGJU

import Representation2._
import scala.collection.immutable.{ListMap, ListSet}

class Quoter(cEnv: ListMap[Ident, ClassDecl] = ListMap(),
             kEnv: ListSet[Ident] = ListSet(),
             tEnv: ListMap[Ident, Either[Kind, Type]] = ListMap(),
             tDefs : ListMap[Ident,(Kind,Type)] = ListMap(),
             kDefs : ListMap[Ident,Kind] = ListMap(),
             env : ListMap[Ident, Type] = ListMap(),
             thisType: Option[Type] = None)
  extends Typechecker(cEnv, kEnv, tEnv, tDefs, kDefs, env, thisType) {

  val thisTypeSrc : Option[String] = thisType.map(translateType)
  val envNames : List[Ident] = List() ++ env.keys
  val envTypes : List[String] = List() ++ env.map(p => translateType(p._2))

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

  // new translation methods

  def translateClass(cd : ClassDecl) : Expr = {
    null
  }

  def translateType(t : Type) : String = t match {
    case Top => "Pair<Nil,Nil>"
    case TVar(x) if tEnv contains(x) => x.nm
    case TVar(x) if cEnv contains(x) => {
      val cd = cEnv(x)
      /*
      val fieldsTypes : String = tupleType(cd.fields)
      s"Pair<${fieldTypes},${methodTypes}>"
      */
      null
    }
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
    var t = translateType(env(i))
    var idx = newIndex(n,envTypes)
    s"new VarExpr<${thisTypeSrc.get},${tupleType(envTypes)},$t>($idx)"
  }

  def translateExpr(e : Expr) : Expr = e match {
    case Var(x) => null // newVarExpr(
  }
}
