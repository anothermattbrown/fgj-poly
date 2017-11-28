package FGJU

class Typechecker(cEnv: Map[Ident, ClassDecl] = Map(),
                  kEnv: Set[Ident] = Set(),
                  tEnv: Map[Ident, Either[Kind, Type]] = Map(),
                  env: Map[Ident, Type] = Map(),
                  thisType: Option[Type] = None) {
  def assertKindIsWellFormed(k: Kind): Unit = k match {
    case Star => ()
    case KVar(nm) if kEnv contains nm => ()
    case KVar(nm) => throw new Exception("kind variable not in scope " + nm)
    case KArr(k1, k2) => List(k1, k2).foreach(assertKindIsWellFormed)
    case KForall(nm, k) => addKindVar(nm).assertKindIsWellFormed(k)
  }

  /*
  def assertTypeIsWellFormed(ty: Type): Unit = ty match {
    case Top => ()
    case TVar(nm) if tEnv contains nm => return
    case TVar(nm)
    case TClass(nm, List()) => {
      if (tEnv.contains(nm))
        return
      if (!cEnv.contains(nm))
        throw new Exception("undeclared type " + nm)
      if (cEnv(nm).params.nonEmpty)
        throw new Exception("incorrect number of type parameters for type " + nm)
    }
    case TClass(nm, actuals) => {
      val c: ClassDecl = cEnv getOrElse(nm, throw new Exception("unknown class " + ty))
      val anns = c.params.map(_.ann)
      if (anns.length != actuals.length)
        throw new Exception("incorrect number of types parameters for type " + nm)
      else
        anns.zip(actuals).foreach({
          case (GAKind, Left(k)) => assertKindIsWellFormed(k)
          case (GAKind, Right(t)) => throw new Exception("type where kind is expected" + t)
          case (GAType(_), Left(k)) => throw new Exception("kind where type is expected" + k)
          case (GAType(Left(k)), Right(t)) => assert(tcType(ty) == k, "class type parameter has wrong kind")
          case (GAType(Right(sup)), Right(sub)) => assertIsSubtypeOf(sub, sup)
        })
    }
    case TForallTy(nm, kindOrBound, ty) => addTypeVar(nm, kindOrBound).assertTypeIsWellFormed(ty)
  }
  */

  def addTypeVar(nm: Ident, kindOrBound: Either[Kind, Type]): Typechecker = {
    kindOrBound match {
      case Left(k) => assertKindIsWellFormed(k)
      case Right(t) => assert(tcType(t) == Star, "addTypeVar: superclass must have kind Star")
    }
    new Typechecker(cEnv, kEnv, tEnv + (nm -> kindOrBound), env, thisType)
  }

  def addKindVar(nm: Ident): Typechecker = new Typechecker(cEnv, kEnv + nm, tEnv, env, thisType)

  // subst1 is newer than subst2. apply subst1 to each type in subst2, then extend the resulting
  // substitution with subst1's entries
  def composeSubsts(subst1: Map[Ident, Type], subst2: Map[Ident, Type]): Map[Ident, Type] = {
    subst2.mapValues(substTy(Map(), subst1, _)) ++ subst1
  }

  def instantiateGVars(decls: List[GVarDecl], params: List[Either[Kind, Type]]): (Map[Ident, Kind], Map[Ident, Type]) = {
    if(decls.length != params.length)
      throw new Exception("instantiateGVars: wrong number of generic parameters")

    val bindings: List[(GVarDecl, Either[Kind, Type])] = decls.zip(params)
    bindings.foldLeft(Map[Ident, Kind](), Map[Ident, Type]()) {
      case ((kSubst, tSubst), (GVarDecl(nm, GAKind), Left(k))) =>
        assertKindIsWellFormed(k)
        (kSubst + (nm -> k), tSubst)
      case ((kSubst, tSubst), (GVarDecl(nm, GAType(kindOrBound)), Right(t))) =>
        kindOrBound match {
          case Left(k) =>
            val k1 = substKind(kSubst, k)
            assertKindIsWellFormed(k1)
            assert(tcType(t) == k1, "Type " + t + " does not have expected kind " + k1)
          case Right(sup) =>
            val sup1 = substTy(kSubst, tSubst, sup)
            assert(tcType(sup1) == Star, "Upper bound " + sup1 + " does not have kind *")
            assertIsSubtypeOf(t, sup1)
        }
        (kSubst, tSubst + (nm -> t))
    }
  }

  def foldTypeApps(nm:Ident, params : List[Either[Kind,Type]]) =
    params.foldLeft[Type](TVar(nm))({
      case (t1,Left(k)) => TKApp(t1,k)
      case (t1,Right(p)) => TTApp(t1,p)
    })

  def unfoldTypeApps(t:Type) : (Ident,List[Either[Kind,Type]]) = t match {
    case TVar(nm) => (nm,List())
    case TTApp(t1,param) =>
      val (nm,params) = unfoldTypeApps(t1)
      (nm,params ++ List(Right(param)))
    case TKApp(t1,param) =>
      val (nm,params) = unfoldTypeApps(t1)
      (nm,params ++ List(Left(param)))
  }

  def getParentType(t: Type): Type = t match {
    case Top                => throw new Exception("Top has no parent type")
    case TForallTy(_, _, _) => throw new Exception("Forall types have no parent types")
    case TForallK(_,_)      => throw new Exception("Forall types have no parent types")
    case _ =>
      val (nm,params) = unfoldTypeApps(t)
      val classDecl = cEnv.getOrElse(nm, throw new Exception("undeclared class " + nm))
      val (kSubst, tSubst) = instantiateGVars(classDecl.params, params)
      substTy(kSubst, tSubst, classDecl.superClass)
  }

  def substKind(kSubst: Map[Ident, Kind], k: Kind): Kind = k match {
    case Star => Star
    case KVar(nm) => kSubst getOrElse(nm, k)
    case KArr(k1, k2) => KArr(substKind(kSubst, k1), substKind(kSubst, k2))
    case KForall(nm, k1) =>
      val nm1 = freshen(nm)
      KForall(nm1, substKind(kSubst + (nm -> KVar(nm1)), k1))
  }

  def normalizeTy(t: Type, tSubst: Map[Ident, Type] = Map(), kSubst: Map[Ident, Kind] = Map()): Type = t match {
    case TVar(nm) => tSubst getOrElse(nm, t)
    case TTApp(t1, t2) => normalizeTy(t1, tSubst, kSubst) match {
      case TTAbs(nm, _, bdy) =>
        val t2nf = normalizeTy(t2, tSubst, kSubst)
        normalizeTy(bdy, tSubst + (nm -> t2nf), kSubst)
    }
    case TKApp(t, k) => normalizeTy(t, tSubst, kSubst) match {
      case TKAbs(nm, bdy) => normalizeTy(bdy, tSubst, kSubst + (nm -> k))
    }
    case TTAbs(nm, kindOrBound, bdy) =>
      val nm1 = freshen(nm)
      val kindOrBound1 = kindOrBound match {
        case Left(k) => Left(substKind(kSubst, k))
        case Right(t) => Right(normalizeTy(t, tSubst, kSubst))
      }
      TTAbs(nm1, kindOrBound, normalizeTy(bdy, tSubst + (nm -> TVar(nm1)), kSubst))
    case TForallTy(nm, kindOrBound, bdy) =>
      val nm1 = freshen(nm)
      val kindOrBound1 = kindOrBound match {
        case Left(k) => Left(substKind(kSubst, k))
        case Right(t) => Right(normalizeTy(t, tSubst, kSubst))
      }
      TForallTy(nm1, kindOrBound, normalizeTy(bdy, tSubst + (nm -> TVar(nm1)), kSubst))
    case TKAbs(nm, bdy) =>
      val nm1 = freshen(nm)
      TKAbs(nm1, normalizeTy(bdy, tSubst, kSubst + (nm -> KVar(nm1))))
    case TForallK(nm, bdy) =>
      val nm1 = freshen(nm)
      TForallK(nm1, normalizeTy(bdy, tSubst, kSubst + (nm -> KVar(nm1))))
  }

  def assertIsSubtypeOf(sub: Type, sup: Type): Unit = {
    // precondition: sub and sup are both valid types
    if (sub == sup) return
    sub match {
      case TVar(nm) if tEnv contains (nm) =>
        val kindOrBound: Either[Kind, Type] = tEnv(nm)
        val parent: Type = kindOrBound.getOrElse(throw new Exception("assertSubtypeOf: type variable is not kind *"))
        assertIsSubtypeOf(parent, sup)
      case TForallTy(_, _, _) => throw new Exception("Forall types are not subtypes of any type\n sub: " + sub + "\n sup: " + sup)
      case TForallK(_, _) => throw new Exception("Forall types are not subtypes of any type\n sub: " + sub + "\n sup: " + sup)
      case _ => assertIsSubtypeOf(getParentType(sub), sup)
    }
  }

  def addClassDecl(cd: ClassDecl): Typechecker = addClassDecls(List(cd))

  def addClassDecls(ds: List[ClassDecl]): Typechecker = {
    // check classes weren't already declared.
    ds.foreach(d => {
      if (cEnv contains (d.nm))
        throw new Exception("class " + d.nm + " already declared")
    })

    val tc = new Typechecker(cEnv ++ ds.map(d => d.nm -> d), kEnv, tEnv, env, thisType)

    // typecheck last, so all the recursion/mutual recursion will work
    ds.foreach(d => tc.tcClassDecl(d.nm))

    tc
  }

  def addGVarDecl(d: GVarDecl): Typechecker =
    d.ann match {
      case GAKind => addKindVar(d.nm)
      case GAType(Left(k)) =>
        assertKindIsWellFormed(k)
        addTypeVar(d.nm, Left(k))
      case GAType(Right(upperBound)) =>
        assert(tcType(upperBound) == Star)
        addTypeVar(d.nm, Right(upperBound))
    }

  def addTVarDecls(decls: List[GVarDecl]): Typechecker = {
    decls.foldLeft(this)({ case (tc, d) => tc.addGVarDecl(d) })
  }

  def addVarDecls(decls: List[VarDecl]): Typechecker = {
    decls.foreach(d => assert(tcType(d.ty) == Star))
    new Typechecker(cEnv, kEnv, tEnv, env ++ decls.map(d => d.nm -> d.ty), thisType)
  }

  def setThisType(ty: Type): Typechecker = new Typechecker(cEnv, kEnv, tEnv, env, Some(ty))

  def classKind(d : ClassDecl) : Kind =
    d.params.foldRight[Kind](Star)({
      case (GVarDecl(nm,GAKind),k) => KForall(nm,k)
      case (GVarDecl(_,GAType(Left(k1))),k2) => KArr(k1,k2)
      case (GVarDecl(_,GAType(Right(_))),k) => KArr(Star,k)
    })

  // Does kind-checking, but doesn't check subtype constraints on type parameters
  def tcType(t: Type): Kind = t match {
    case Top => Star
    case TVar(nm) if tEnv contains nm => tEnv(nm) match {
      case Left(k) => k
      case Right(sup) => Star
    }
    case TVar(nm) if cEnv contains nm => classKind(cEnv(nm))
    case TVar(nm) => throw new Exception("tcType: undeclared type " + nm)
    case TTApp(t1,t2) => (tcType(t1), tcType(t2)) match {
      case (KArr(a1,r),a2) if a1 == a2 => r
      case (k1,k2) => throw new Exception("tcType TTApp error: k1=" + k1 + ", k2=" + k2)
    }
    case TKApp(t1,k) =>
      assertKindIsWellFormed(k)
      tcType(t1) match {
        case KForall(nm,bdy) => substKind(Map(nm -> k),bdy)
      }
    case TForallTy(nm, kindOrBound, bdy) =>
      assert(addTypeVar(nm, kindOrBound).tcType(bdy) == Star, "Forall type body failed to kind-check")
      Star
    case TForallK(nm, bdy) =>
      assert(addKindVar(nm).tcType(bdy) == Star, "Forall kind body failed to kind-check")
      Star
  }

  def tcExpr(e: Expr): Type = e match {
    case Var(nm) => env getOrElse(nm, throw new Exception("undeclared variable " + nm))
    case Field(obj, nm) => lookupFieldType(tcExpr(obj), nm)
    case This => thisType.get
    case New(cNm,gParams,params) =>
      val cd = cEnv(cNm)
      val (kSubst,tSubst) = instantiateGVars(cd.params,gParams)

      // check we have the right number of constructor parameters
      assert(params.length == cd.fields.length, "tcExpr: wrong number of constructor parameters")

      // now check the types of constructor parameters
      cd.fields.map(fd => substTy(kSubst,tSubst,fd._2)).zip(params).foreach({
        case (t, e) => assertIsSubtypeOf(tcExpr(e),t)
      })

      foldTypeApps(cNm,gParams)

    case Call(e, actualTys, nm, actuals) =>
      val m = lookupMethodSig(tcExpr(e), nm)
      assert(
        actualTys.length == m.tParams.length,
        "wrong number of type parameters in call: " + Call(e, actualTys, nm, actuals)
      )
      val (kSubst, tSubst) = instantiateGVars(m.tParams, actualTys)

      // check we have the right number of parameters
      assert(actuals.length == m.paramTypes.length)
      var expectedTypes = m.paramTypes.map(substTy(kSubst, tSubst, _))
      var actualTypes = actuals.map(tcExpr(_))
      actualTypes.zip(expectedTypes).foreach { case (sub, sup) => assertIsSubtypeOf(sub, sup) }

      substTy(kSubst, tSubst, m.retTy)
  }

  // require the decl to be in cEnv for recursion
  def tcClassDecl(nm: Ident): Unit = {
    val c: ClassDecl = cEnv(nm)

    val tcOuter = c.params.foldLeft(this)({
      case (tc, GVarDecl(nm, ann)) => ann match {
        case GAKind => tc.addKindVar(nm)
        case GAType(kindOrBound) => tc.addTypeVar(nm, kindOrBound)
      }
    })

    assert(tcOuter.tcType(c.superClass) == Star, "tcClassDecl: superClass must have kind *")

    val tcInner = tcOuter.setThisType(foldTypeApps(c.nm, c.params.map({
      case GVarDecl(nm, GAKind) => Left(KVar(nm))
      case GVarDecl(nm, GAType(_)) => Right(TVar(nm))
    })))

    c.fields.foreach({ case (nm, ty) =>
      assert(tcInner.tcType(ty) == Star, "tcClassDecl: field " + nm + " type does not have kind *: " + ty)
    })

    c.methods.foreach(tcInner.tcMethod)
  }

  def tcMethod(m: MethodDecl): Unit = {
    // add type parameters to the context. this checks bounds are well-formed
    val tc1 = addTVarDecls(m.tParams)
    try {
      val retTyKind : Kind = tc1.tcType(m.retTy)
      if(retTyKind != Star)
        throw new Exception("tcMethod: return type " + m.retTy + " does not have kind *: " + retTyKind)
    } catch {
      case e : Exception =>
        throw new Exception("tcMethod: return type " + m.retTy + " failed to type-check\n" + e)
    }
    val tc2 = tc1.addVarDecls(m.params)
    try {
      val bdyTy: Type = tc2.tcExpr(m.bdy)
      if (bdyTy != m.retTy)
        throw new Exception("tcMethod: method body does not have expected type: " + m.retTy)
    } catch {
      case e : Exception =>

    }
  }

  def either[A1, A2, B1, B2](f: A1 => A2, g: B1 => B2): Either[A1, B1] => Either[A2, B2] = {
    case Left(a) => Left(f(a))
    case Right(b) => Right(g(b))
  }

  def substTy(kSubst: Map[Ident, Kind], tSubst: Map[Ident, Type], ty: Type): Type = ty match {
    case Top => Top
    case TVar(nm) => tSubst getOrElse(nm, ty) // type variable cannot have params
    case TForallTy(nm, kindOrBound, bdy) =>
      val kindOrBound1: Either[Kind, Type] = kindOrBound match {
        case Left(k) => Left(substKind(kSubst, k))
        case Right(t) => Right(substTy(kSubst, tSubst, t))
      }
      TForallTy(nm, kindOrBound1, substTy(kSubst, tSubst - nm, bdy))
    case TForallK(nm, bdy) => TForallK(nm, substTy(kSubst - nm, tSubst, bdy))
    case TTAbs(nm, kindOrBound, bdy) =>
      val kindOrBound1: Either[Kind, Type] = kindOrBound match {
        case Left(k) => Left(substKind(kSubst, k))
        case Right(t) => Right(substTy(kSubst, tSubst, t))
      }
      TTAbs(nm, kindOrBound1, substTy(kSubst, tSubst - nm, bdy))
    case TKAbs(nm, bdy) => TKAbs(nm, substTy(kSubst - nm, tSubst, bdy))
    case TTApp(t1,t2) => TTApp(substTy(kSubst,tSubst,t1), substTy(kSubst,tSubst,t2))
    case TKApp(t,k) => TKApp(substTy(kSubst,tSubst,t), substKind(kSubst,k))
  }

  def lookupFieldType(ty: Type, fNm: String): Type = {
    // Don't support field access on quantified types.
    val (nm,params) = unfoldTypeApps(ty)
    val classDecl = cEnv(nm)

    if (classDecl.params.length != params.length)
      throw new Exception("lookupFieldType: wrong number of class type parameters")

    val (kSubst, tSubst) = instantiateGVars(classDecl.params, params)
    val fieldTy = (Map() ++ classDecl.fields)(fNm)
    substTy(kSubst, tSubst, fieldTy)
  }

  case class MethodSig(tParams: List[GVarDecl], retTy: Type, paramTypes: List[Type])

  def lookupMethodSig(ty: Type, mNm: String): MethodSig = {
    // Don't support field access on quantified types.
    val (nm,params) = unfoldTypeApps(ty)
    val classDecl = cEnv(nm)

    if (classDecl.params.length != params.length)
      throw new Exception("lookupFieldType: wrong number of class type parameters")
    val (kSubst, tSubst) = instantiateGVars(classDecl.params, params)
    val md = classDecl.methods.filter(m => m.nm == mNm).head
    val sig = MethodSig(md.tParams, md.retTy, md.params.map(_.ty))
    substMethodSig(kSubst, tSubst, sig)
  }

  def substMethodSig(kSubst: Map[Ident, Kind], tSubst: Map[Ident, Type], m: MethodSig): MethodSig = {
    val gParams = m.tParams.map({
      case GVarDecl(nm, GAKind) => GVarDecl(nm, GAKind)
      case GVarDecl(nm, GAType(Left(k))) => GVarDecl(nm, GAType(Left(substKind(kSubst, k))))
      case GVarDecl(nm, GAType(Right(t))) => GVarDecl(nm, GAType(Right(substTy(kSubst, tSubst, t))))
    })
    val (kSubst1, tSubst1) = gParams.foldLeft[(Map[Ident, Kind], Map[Ident, Type])](kSubst, tSubst)({
      case ((kSubst, tSubst), GVarDecl(nm, GAKind)) => (kSubst - nm, tSubst)
      case ((kSubst, tSubst), GVarDecl(nm, GAType(_))) => (kSubst, tSubst - nm)
    })
    val retTy = substTy(kSubst1, tSubst1, m.retTy)
    val paramTypes = m.paramTypes.map(substTy(kSubst1, tSubst1, _))
    MethodSig(gParams, retTy, paramTypes)
  }
}