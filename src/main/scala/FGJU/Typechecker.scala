package FGJU

class Typechecker(cEnv: Map[Ident, ClassDecl] = Map(),
                  kEnv: Set[Ident] = Set(),
                  tEnv: Map[Ident, Either[Kind, Type]] = Map(),
                  tDefs : Map[Ident,(Kind,Type)] = Map(),
                  kDefs : Map[Ident,Kind] = Map(),
                  env: Map[Ident, Type] = Map(),
                  thisType: Option[Type] = None) {
  // getters
  def cEnv() : Map[Ident,ClassDecl] = cEnv
  def env() : Map[Ident,Type] = env
  def tEnv() : Map[Ident,Either[Kind,Type]] = tEnv
  def tDefs() : Map[Ident,(Kind,Type)] = tDefs

  def assertKindIsWellFormed(k: Kind): Unit = k match {
    case Star => ()
    case KVar(nm) if (kEnv contains nm) || (kDefs contains nm) => ()
    case KVar(nm) => throw new Exception("kind variable not in scope " + nm)
    case KArr(k1, k2) => List(k1, k2).foreach(assertKindIsWellFormed)
    case KForall(nm, k) => addKindVar(nm).assertKindIsWellFormed(k)
  }

  def addTypeVar(nm: Ident, kindOrBound: Either[Kind, Type]): Typechecker = {
    kindOrBound match {
      case Left(k) => assertKindIsWellFormed(k)
      case Right(t) => assert(tcType(t) == Star, "addTypeVar: superclass must have kind Star")
    }
    new Typechecker(cEnv, kEnv, tEnv + (nm -> kindOrBound), tDefs, kDefs, env, thisType)
  }

  def addTypeDef(nm:Ident, kind:Kind, defn:Type) : Typechecker = {
    assertKindIsWellFormed(kind)
    val expKind = substKind(kDefs, kind)
    val defKind = substKind(kDefs, tcType(defn))

    assert(alphaEquivK(defKind, expKind), s"addTypeDef $nm: type $defn has kind $defKind, not the expected kind $expKind")
    // make sure tDefs is idempotent, by expanding any defs in the new defn
    val defn1 = substTy(Map(), tDefs.mapValues(_._2), defn)
    new Typechecker(cEnv, kEnv, tEnv - nm, tDefs + (nm -> (kind,defn1)), kDefs, env, thisType)
  }

  def addKindVar(nm: Ident): Typechecker = new Typechecker(cEnv, kEnv + nm, tEnv, tDefs, kDefs, env, thisType)

  def addKindDef(nm : Ident, k:Kind) : Typechecker = {
    assertKindIsWellFormed(k)
    val k1 = substKind(kDefs,k)
    new Typechecker(cEnv, kEnv, tEnv, tDefs, kDefs + (nm -> k1), env, thisType)
  }

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
            val expected = substKind(kSubst, k)
            assertKindIsWellFormed(expected)
            val got = tcType(t)
            assert(alphaEquivK(got, expected), s"Type $t does not have expected kind $expected. It has kind $got")
          case Right(sup) =>
            val sup1 = substTy(kSubst, tSubst, sup)
            assert(tcType(sup1) == Star, "Upper bound " + sup1 + " does not have kind *")
            assertIsSubtypeOf(t, sup1)
        }
        (kSubst, tSubst + (nm -> t))
    }
  }

  def getParentType(t: Type): Type = t match {
    case Top                =>
      throw new Exception("Top has no parent type")
    case TForallTy(_, _, _) => Top // throw new Exception("Forall types have no parent types")
    case TForallK(_,_)      => Top // throw new Exception("Forall types have no parent types")
    case _ =>
      val (nm,params) = unfoldTypeApps(t)
      if(cEnv contains nm) {
        try {
          val classDecl = cEnv(nm)
          val (kSubst, tSubst) = instantiateGVars(classDecl.params, params)
          return normalizeTy(substTy(kSubst, tSubst, classDecl.superClass))
        } catch {
          case e :Exception =>
            throw new Exception(s"error getting parent type of class ${nm.nm}", e)
        }
      } else if(tEnv contains nm) {
        tEnv(nm) match {
          case Left(k) => return Top
          case Right(sup) => return sup
        }
      }
      throw new Exception("getParentType: unknown type: " + nm)
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
    case Top => Top
    case TVar(nm) => tSubst getOrElse(nm, t)
    case TTApp(t1, t2) =>
      val t2nf = normalizeTy(t2, tSubst, kSubst)
      normalizeTy(t1, tSubst, kSubst) match {
        case TTAbs(nm, _, bdy) =>
          normalizeTy(bdy, tSubst + (nm -> t2nf), kSubst)
        case t1nf => TTApp(t1nf,t2nf)
      }
    case TKApp(t, k) =>
      val k1 = substKind(kSubst,k)
      normalizeTy(t, tSubst, kSubst) match {
        case TKAbs(nm, bdy) => normalizeTy(bdy, tSubst, kSubst + (nm -> k1))
        case t1 => TKApp(t1,k1)
      }
    case TTAbs(nm, kindOrBound, bdy) =>
      val kindOrBound1 = kindOrBound match {
        case Left(k) => Left(substKind(kSubst, k))
        case Right(t) => Right(normalizeTy(t, tSubst, kSubst))
      }
      val nm1 = freshen(nm)
      TTAbs(nm1, kindOrBound, normalizeTy(bdy, tSubst + (nm -> TVar(nm1)), kSubst))
    case TForallTy(nm, kindOrBound, bdy) =>
      val kindOrBound1 = kindOrBound match {
        case Left(k) => Left(substKind(kSubst, k))
        case Right(t) => Right(normalizeTy(t, tSubst, kSubst))
      }
      val nm1 = freshen(nm)
      TForallTy(nm1, kindOrBound, normalizeTy(bdy, tSubst + (nm -> TVar(nm1)), kSubst))
    case TKAbs(nm, bdy) =>
      val nm1 = freshen(nm)
      TKAbs(nm1, normalizeTy(bdy, tSubst, kSubst + (nm -> KVar(nm1))))
    case TForallK(nm, bdy) =>
      val nm1 = freshen(nm)
      TForallK(nm1, normalizeTy(bdy, tSubst, kSubst + (nm -> KVar(nm1))))
  }

  def alphaEquivK(k1 : Kind, k2 : Kind, kMap : Map[Ident,Ident] = Map()) : Boolean = (k1,k2) match {
    case (Star,Star) => true
    case (KVar(nm1),KVar(nm2)) => kMap.getOrElse(nm1,nm1) == nm2
    case (KArr(l1,r1),KArr(l2,r2)) => alphaEquivK(l1,l2,kMap) && alphaEquivK(r1,r2,kMap)
    case (KForall(nm1,bdy1), KForall(nm2,bdy2)) => alphaEquivK(bdy1,bdy2,kMap + (nm1 -> nm2))
    case _ =>
      throw new Exception("alphaEquivK: match error")
  }

  def alphaEquivKindOrBound(kb1 : Either[Kind,Type],kb2 : Either[Kind,Type],tMap : Map[Ident,Ident] = Map(),kMap : Map[Ident,Ident] = Map()) : Boolean =
    (kb1,kb2) match {
      case (Left(Star),Right(Top)) => true
      case (Right(Top),Left(Star)) => true
      case (Left(k1),Left(k2)) => alphaEquivK(k1,k2,kMap)
      case (Right(t1),Right(t2)) => alphaEquivTy(t1,t2,tMap,kMap)
      case _ => throw new Exception("alphaEquivKindOrBound: not equivalent.\n" + kb1 + "\n" + kb2)
    }

  // precondition: normal form types
  def alphaEquivTy(t1 : Type, t2 : Type, tMap : Map[Ident,Ident] = Map(), kMap : Map[Ident,Ident] = Map()) : Boolean = (t1,t2) match {
    case (Top,Top) => true
    case (TVar(nm1),TVar(nm2)) => tMap.getOrElse(nm1,nm1) == nm2
    case (TTAbs(nm1,kindOrBound1,bdy1), TTAbs(nm2,kindOrBound2,bdy2)) =>
      alphaEquivKindOrBound(kindOrBound1,kindOrBound2,tMap,kMap) && alphaEquivTy(bdy1,bdy2,tMap + (nm1 -> nm2), kMap)
    case (TTApp(f1,a1),TTApp(f2,a2)) =>
      alphaEquivTy(f1,f2,tMap,kMap) && alphaEquivTy(a1,a2,tMap,kMap)
    case (TKAbs(nm1,bdy1),TKAbs(nm2,bdy2)) =>
      alphaEquivTy(bdy1,bdy2,tMap,kMap + (nm1 -> nm2))
    case (TKApp(f1,k1),TKApp(f2,k2)) =>
      alphaEquivTy(f1,f2,tMap,kMap) && alphaEquivK(k1,k2,kMap)
    case (TForallTy(nm1,kindOrBound1,bdy1),TForallTy(nm2,kindOrBound2,bdy2)) =>
      alphaEquivKindOrBound(kindOrBound1,kindOrBound2,tMap,kMap) && alphaEquivTy(bdy1,bdy2,tMap + (nm1 -> nm2), kMap)
    case (TForallK(nm1,bdy1), TForallK(nm2,bdy2)) =>
      alphaEquivTy(bdy1,bdy2,tMap,kMap + (nm1 -> nm2))
    case _ => false
  }

  def assertAlphaEquivMethodSig(m1 : MethodSig, m2 : MethodSig) : Unit = {
    assert(m1.nm == m2.nm)
    assert(m1.tParams.length == m2.tParams.length)
    assert(m1.paramTypes.length == m2.paramTypes.length)

    def mkForall(gParams : List[GVarDecl], t:Type) : Type = {
      gParams.foldLeft[Type](t)({
        case (t,GVarDecl(nm,GAKind)) => TForallK(nm,t)
        case (t,GVarDecl(nm,GAType(kindOrBound))) => TForallTy(nm,kindOrBound,t)
      })
    }

    assert(alphaEquivTy(mkForall(m1.tParams,m1.retTy),
                        mkForall(m2.tParams,m2.retTy)))

    for((t1,t2) <- m1.paramTypes.zip(m2.paramTypes)) {
      assert(alphaEquivTy(mkForall(m1.tParams,t1),
                          mkForall(m2.tParams,t2)))
    }
  }

  def assertIsSubtypeOf(sub1: Type, sup1: Type): Unit = {
    // first, expand any letType definitions
    val tDefsSubst = tDefs.mapValues(_._2)
    val sub = substTy(Map(), tDefsSubst, sub1)
    val sup = substTy(Map(), tDefsSubst, sup1)

    // precondition: sub and sup are both valid types
    if (alphaEquivTy(sub, sup)) return ()
    /*
    if(sub.isInstanceOf[TVar]) {
      var TVar(nm) = sub.asInstanceOf[TVar]
      if(tDefs contains nm) {
        assertIsSubtypeOf(sub,tDefs(nm)._2)
        return ()
      }
    }
    */
    //if (sup == Top) return ()
    sub match {
        /*
      case TVar(nm) if tDefs contains nm =>
        assertIsSubtypeOf(tDefs(nm)._2,sup)
        */
      case TVar(nm) if tEnv contains nm =>
        val kindOrBound: Either[Kind, Type] = tEnv(nm)
        val parent: Type = kindOrBound match {
          case Right(t) => t
          case Left(Star) => Top
          case Left(k) => throw new Exception(s"assertSubtypeOf: type variable $nm is not kind *: " + kindOrBound)
        }
        assertIsSubtypeOf(parent, sup)
      case TForallTy(nm1, kindOrBound1, bdySub) => sup match {
        case Top => ()
        case TForallTy(nm2, kindOrBound2, bdySup) =>
          assert(alphaEquivKindOrBound(kindOrBound1,kindOrBound2))
          val nm=freshen(nm1)
          val bdySub1 = substTy(Map(),Map(nm1 -> TVar(nm)), bdySub)
          val bdySup1 = substTy(Map(),Map(nm2 -> TVar(nm)), bdySup)
          addTypeVar(nm,kindOrBound1).assertIsSubtypeOf(bdySub1, bdySup1)
      }
      case TForallK(nm1, bdySub) => sup match {
        case Top => ()
        case TForallK(nm2,bdySup) =>
          val nm = freshen(nm1)
          val bdySub1 = substTy(Map(nm1 -> KVar(nm)), Map(), bdySub)
          val bdySup1 = substTy(Map(nm2 -> KVar(nm)), Map(), bdySup)
          addKindVar(nm).assertIsSubtypeOf(bdySub1, bdySup1)
      }

      case _ => {
        try {
          assertIsSubtypeOf(getParentType(sub), sup)
        } catch {
          case e : Exception =>
            throw new Exception(s"$sub is not a subtype of $sup", e)
        }
      }
    }
  }

  def addClassDecl(cd: ClassDecl): Typechecker = addClassDecls(List(cd))

  def addClassDecls(ds: List[ClassDecl]): Typechecker = {
    // check classes weren't already declared.
    ds.foreach(d => {
      if (cEnv contains d.nm)
        throw new Exception("class " + d.nm + " already declared")
    })

    val tc = new Typechecker(cEnv ++ ds.map(d => d.nm -> d), kEnv, tEnv, tDefs, kDefs, env, thisType)

    // typecheck last, so all the (mutual) recursion will work
    ds.map(_.nm).foreach(nm =>
      try {
        tc.tcClassDecl(nm)
      } catch {
        case e : Exception =>
          throw new Exception(s"addClassDecls: error typechecking $nm", e)
        case e : AssertionError =>
          throw new Exception(s"addClassDecls: error typechecking $nm", e)
      }
    )

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

  def addGVarDecls(decls: List[GVarDecl]): Typechecker = {
    decls.foldLeft(this)({ case (tc, d) => tc.addGVarDecl(d) })
  }

  def addVarDecls(decls: List[VarDecl]): Typechecker = {
    decls.foreach(d => assert(tcType(d.ty) == Star))
    new Typechecker(cEnv, kEnv, tEnv, tDefs, kDefs, env ++ decls.map(d => d.nm -> d.ty), thisType)
  }

  def setThisType(ty: Type): Typechecker = new Typechecker(cEnv, kEnv, tEnv, tDefs, kDefs, env, Some(ty))

  def classKind(d : ClassDecl) : Kind =
    d.params.foldRight[Kind](Star)({
      case (GVarDecl(nm,GAKind),k) => KForall(nm,k)
      case (GVarDecl(_,GAType(Left(k1))),k2) => KArr(k1,k2)
      case (GVarDecl(_,GAType(Right(_))),k) => KArr(Star,k)
    })

  // Does kind-checking, but doesn't check subtype constraints on type parameters
  def tcType(t: Type): Kind = t match {
    case Top => Star
    case TVar(nm) if tDefs contains nm => substKind(kDefs,tDefs(nm)._1)
    case TVar(nm) if tEnv contains nm => tEnv(nm) match {
      case Left(k) =>
        val k1 = substKind(kDefs,k)
        k1
      case Right(sup) => Star
    }
    case TVar(nm) if cEnv contains nm => classKind(cEnv(nm))
    case TVar(nm) => throw new Exception("tcType: undeclared type " + nm)
    case TTAbs(nm,kindOrBound,bdy) =>
      // TODO: either remove bounds on type abstractions, or somehow add bounds to the kind language
      val k1 = kindOrBound match {
        case Left(k) => substKind(kDefs,k)
        case Right(t) => Star
      }
      val k2 = addTypeVar(nm,kindOrBound).tcType(bdy)
      KArr(k1,k2)
    case TTApp(t1,t2) =>
      val k1 = tcType(t1)
      val k2 = tcType(t2)
      (k1,k2) match {
      case (KArr(a1,r),a2) if alphaEquivK(a1,a2) => r
      case _ => throw new Exception(s"""tcType TTApp error
                                       |t1 = $t1
                                       |k1 = $k1
                                       |t2 = $t2
                                       |k2 = $k2
                                       |""".stripMargin)
    }
    case TKAbs(nm,bdy) => KForall(nm, addKindVar(nm).tcType(bdy))
    case TKApp(t1,k) =>
      assertKindIsWellFormed(k)
      val t1k = tcType(t1)
      val t1kClosed = substKind(kDefs,t1k)
      val kClosed = substKind(kDefs,k)
      t1kClosed match {
        case KForall(nm,bdy) => substKind(Map(nm -> kClosed),bdy)
      }
    case TForallTy(nm, kindOrBound, bdy) =>
      assert(addTypeVar(nm, kindOrBound).tcType(bdy) == Star, "Forall type body failed to kind-check")
      Star
    case TForallK(nm, bdy) =>
      assert(addKindVar(nm).tcType(bdy) == Star, "Forall kind body failed to kind-check")
      Star
    case _ => throw new Exception("tcType: no case for " + t)
  }

  def instantiateClass(cNm: Ident, gParams: List[Either[Kind, Type]]) : (ClassDecl, Map[Ident,Kind], Map[Ident,Type]) = {
    val cd = cEnv(cNm)
    val (kSubst,tSubst) =
      try {
        instantiateGVars(cd.params, gParams)
      } catch {
        case e : Exception =>
          throw new Exception(s"instantiateClass: error instantiating $cNm", e)
      }
    (cd,kSubst,tSubst)
  }

  def getFields(t : Type) : List[(String,Type)] = t match {
    case Top => List()
    case TVar(_) | TTApp(_,_) | TKApp(_,_) =>
      val (cNm, params) = unfoldTypeApps(t)
      val (cd, kSubst, tSubst) = instantiateClass(cNm, params)

      val fields = cd.fields.map(p => (p._1, substTy(kSubst,tSubst,p._2)))
      val parentFields = getFields(getParentType(t))
      parentFields ++ fields
    case _ =>
      throw new Exception(s"getFields: type $t has no fields")
  }

  def tcExpr(e: Expr): Type = e match {
    case Var(nm) => env getOrElse(nm, throw new Exception("undeclared variable " + nm))
    case Field(obj, nm) => lookupFieldType(tcExpr(obj), nm)
    case This => thisType.get
    case New(cNm,gParams,params) =>
      // type of the new object
      val oTy = normalizeTy(foldTypeApps(cNm,gParams))

      // get the list of all fields (from class cNm and superclasses)
      val fields = getFields(oTy)

      // check we have the right number of constructor parameters
      if(params.length != fields.length)
        throw new Exception("tcExpr: wrong number of constructor parameters")

      // now check the types of constructor parameters
      fields.zip(params).foreach({
        case ((nm,t), e) =>
          val eTy = tcExpr(e)
          val fTy = normalizeTy(t)
          try {
            assertIsSubtypeOf(eTy, fTy)
          } catch {
            case exn : Exception =>
              throw new Exception(
                s"""constructor parameter is not a subtype of the declared field type.
                   |Class name: ${cNm.nm}
                   |Field name: $nm
                   |Field type: $fTy
                   |Parameter expr: $e
                   |Parameter type: $eTy
                 """.stripMargin,
                exn
              )
          }
      })

      oTy

    case Call(e, actualTys, nm, actuals) =>
      val tyE = tcExpr(e)
      val m = lookupMethodSig(tyE, nm).getOrElse(
        throw new Exception(s"unknown method $nm on type $tyE")
      )
      assert(
        actualTys.length == m.tParams.length,
        "wrong number of type parameters in call: " + Call(e, actualTys, nm, actuals)
      )
      val (kSubst, tSubst) = instantiateGVars(m.tParams, actualTys)

      // check we have the right number of parameters
      assert(actuals.length == m.paramTypes.length, s"tcExpr/call: wrong number of parameters for call to $nm")
      var expectedTypes = m.paramTypes.map(substTy(kSubst, tSubst, _))
      var actualTypes = actuals.map(tcExpr)
      actualTypes.map(normalizeTy(_)).zip(expectedTypes.map(normalizeTy(_))).foreach {
        case (sub, sup) =>
          try {
            assertIsSubtypeOf(sub, sup)
          } catch {
            case e : Exception =>
              throw new Exception(s"method call $nm argument subtype check failed", e)
          }
      }

      normalizeTy(substTy(kSubst, tSubst, m.retTy))
    case TAbs(nm,kindOrBound,bdy) =>
      kindOrBound match {
        case Left(k) => assertKindIsWellFormed(k)
        case Right(t) => assert(tcType(t) == Star)
      }
      TForallTy(nm,kindOrBound,addTypeVar(nm,kindOrBound).tcExpr(bdy))
    case TApp(e1,t) =>
      tcExpr(e1) match {
        case TForallTy(nm,kindOrBound,bdy) =>
          kindOrBound match {
            case Left(k) => assert(tcType(t) == k)
            case Right(sup) => assertIsSubtypeOf(t,sup)
          }
          substTy(Map(),Map(nm -> t),bdy)
        case e1Ty =>
          throw new Exception("tcExpr/TApp: subexpression does not have forall-type type: " + e1Ty)
      }
    case KAbs(nm,bdy) => TForallK(nm, addKindVar(nm).tcExpr(bdy))
    case KApp(e1,k) =>
      assertKindIsWellFormed(k)
      tcExpr(e1) match {
        case TForallK(nm,bdy) => substTy(Map(nm -> k), Map(), bdy)
        case e1Ty =>
          throw new Exception("tcExpr/KApp: subexpression does not have forall-kind type: " + e1Ty)
      }
    case KLet(nm,k,bdy) =>
      val tc = addKindDef(nm,k)
      val bdyT = tc.tcExpr(bdy)
      substTy(Map(nm -> k), Map() , bdyT)
    case TLet(nm,k,t,bdy) =>
      val bdyT = addTypeDef(nm,k,t).tcExpr(bdy)
      substTy(Map(),Map(nm -> t), bdyT)
    case Let(nm,t,e,bdy) =>
      assert(tcType(t) == Star)
      val eTy = tcExpr(e)
      assertIsSubtypeOf(eTy,t)
      addVarDecls(List(VarDecl(nm,t))).tcExpr(bdy)
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

    assert(tcOuter.tcType(c.superClass) == Star, s"tcClassDecl: superClass ${c.superClass} does not have kind *")

    val tcInner = tcOuter.setThisType(foldTypeApps(c.nm, c.params.map({
      case GVarDecl(nm, GAKind) => Left(KVar(nm))
      case GVarDecl(nm, GAType(_)) => Right(TVar(nm))
    })))

    c.fields.foreach({ case (nm, ty) =>
      assert(tcInner.tcType(ty) == Star, "tcClassDecl: field " + nm + " type does not have kind *: " + ty)
    })

    // typecheck methods
    c.methods.foreach(tcInner.tcMethod)

    // check validity of method overrides
    val classType : Type = c.params.foldLeft[Type](TVar(c.nm))({
      case (ty, GVarDecl(nm,GAKind))    => TKApp(ty,KVar(nm))
      case (ty, GVarDecl(nm,GAType(_))) => TTApp(ty,TVar(nm))
    })

    c.methods.foreach({md =>
      val sig = tcOuter.lookupMethodSig(classType, md.nm).get
      tcOuter.lookupMethodSig(c.superClass,md.nm).foreach({superSig =>
        tcOuter.assertValidMethodSigOverride(sig,superSig)
      })
    })
  }

  // precondition: both MethodSigs have been freshened.
  def assertValidMethodSigOverride(subSig : MethodSig, superSig : MethodSig) : Unit = {
    // check the generic parameters
    assert(subSig.tParams.length == superSig.tParams.length,
      "assertValidMethodSigOverride: overriding methods must have the same number of generic parameters"
    )

    // rename subSig's generic params to match superSig's names.
    val (kRename,tRename) = subSig.tParams.zip(superSig.tParams).foldLeft[(Map[Ident,Ident], Map[Ident,Ident])](Map(),Map())({
      case ((kRename,tRename), (GVarDecl(nm1,GAKind), GVarDecl(nm2,GAKind))) =>
        (kRename + (nm1 -> nm2), tRename)
      case ((kRename,tRename), (GVarDecl(nm1,GAType(kb1)), GVarDecl(nm2,GAType(kb2)))) =>
        if(!alphaEquivKindOrBound(kb1,kb2,tRename,kRename))
          throw new Exception("kind or bounds not alpha equivalent")
        (kRename, tRename + (nm1 -> nm2))
    })

    // type checker with superSig's generic params in scope.
    val tc = this.addGVarDecls(superSig.tParams)

    val kSubst = kRename.mapValues(KVar)
    val tSubst = tRename.mapValues(TVar)

    // check covariance of return types
    tc.assertIsSubtypeOf(
      normalizeTy(substTy(kSubst,tSubst,subSig.retTy)),
      normalizeTy(superSig.retTy))

    assert(subSig.paramTypes.length == superSig.paramTypes.length,
      s"assertValidMethodSigOverride: overriding methods must have the same number of parameters"
    )

    // check contravariance of argument types
    try {
      for ((subT, supT) <- subSig.paramTypes.map(substTy(kSubst,tSubst,_)).zip(superSig.paramTypes)) {
        tc.assertIsSubtypeOf(supT, subT)
      }
    } catch {
      case e : Exception =>
        throw new Exception(s"contravariance check of method arguments failed\nsubSig.paramTypes=${subSig.paramTypes}\nsuperSig.paramTypes=${superSig.paramTypes}")
    }
  }

  def tcMethod(m: MethodDecl): Unit = {
    // add type parameters to the context. this checks bounds are well-formed
    val tc1 = addGVarDecls(m.tParams)
    try {
      val retTyKind : Kind = tc1.tcType(m.retTy)
      if(retTyKind != Star)
        throw new Exception("tcMethod: return type " + m.retTy + " does not have kind *: " + retTyKind)
    } catch {
      case e : Exception =>
        throw new Exception("tcMethod: return type " + m.retTy + " failed to type-check\n" + e)
    }
    val tc2 =
      try { tc1.addVarDecls(m.params) }
      catch {
        case e : Exception =>
          throw new Exception(s"error adding variable declarations for method ${m.nm}", e)
      }
    val bdyTy =
      try { tc2.tcExpr(m.bdy) }
      catch {
        case e : Exception =>
          throw new Exception(s"error typechecking method ${m.nm} body", e)
      }
    val bdyTyNf = normalizeTy(bdyTy)
    val retTyNf = normalizeTy(m.retTy)
    try {
      tc2.assertIsSubtypeOf(bdyTyNf,retTyNf)
    } catch {
      case e : Exception =>
        e.printStackTrace()
        throw new Exception(s"tcMethod: error typechecking method ${m.nm} body: " + e)
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
      val nm1 = freshen(nm)
      TForallTy(nm1, kindOrBound1, substTy(kSubst, tSubst + (nm -> TVar(nm1)), bdy))
    case TForallK(nm, bdy) =>
      val nm1 = freshen(nm)
      TForallK(nm1, substTy(kSubst + (nm -> KVar(nm1)), tSubst, bdy))
    case TTAbs(nm, kindOrBound, bdy) =>
      val kindOrBound1: Either[Kind, Type] = kindOrBound match {
        case Left(k) => Left(substKind(kSubst, k))
        case Right(t) => Right(substTy(kSubst, tSubst, t))
      }
      val nm1 = freshen(nm)
      TTAbs(nm1, kindOrBound1, substTy(kSubst, tSubst + (nm -> TVar(nm1)), bdy))
    case TKAbs(nm, bdy) =>
      val nm1 = freshen(nm)
      TKAbs(nm1, substTy(kSubst + (nm -> KVar(nm1)), tSubst, bdy))
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

  case class MethodSig(tParams: List[GVarDecl], retTy: Type, nm : String, paramTypes: List[Type])

  def methodSig(md : MethodDecl) : MethodSig = {
    MethodSig(md.tParams, md.retTy, md.nm, md.params.map(_.ty))
  }

  def lookupMethodSig(ty: Type, mNm: String): Option[MethodSig] = {
    if(ty == Top) return None

    // Don't support field access on quantified types.
    val (nm,params) = unfoldTypeApps(ty)
    val cd = cEnv(nm)

    if (cd.params.length != params.length)
      throw new Exception("lookupMethodSig: wrong number of class type parameters")
    val (kSubst, tSubst) = instantiateGVars(cd.params, params)
    cd.methods.find(m => m.nm == mNm)
      .map(methodSig)
      .map(substMethodSig(kSubst,tSubst,_))
      .orElse(lookupMethodSig(getParentType(ty),mNm))
  }

  def substMethodSig(kSubst: Map[Ident, Kind], tSubst: Map[Ident, Type], m: MethodSig): MethodSig = {
    /*
    val gParams = m.tParams.map({
      case GVarDecl(nm, GAKind) => GVarDecl(nm, GAKind)
      case GVarDecl(nm, GAType(Left(k))) => GVarDecl(nm, GAType(Left(substKind(kSubst, k))))
      case GVarDecl(nm, GAType(Right(t))) => GVarDecl(nm, GAType(Right(substTy(kSubst, tSubst, t))))
    })
    */
    val (gParams,kSubst1, tSubst1) = m.tParams.foldLeft[(List[GVarDecl], Map[Ident, Kind], Map[Ident, Type])](List(), kSubst, tSubst)({
      case ((decls, kSubst, tSubst), GVarDecl(nm, GAKind)) =>
        val nm1 = freshen(nm)
        (decls ++ List(GVarDecl(nm1,GAKind)), kSubst + (nm -> KVar(nm1)), tSubst)
      case ((decls, kSubst, tSubst), GVarDecl(nm, GAType(ann))) =>
        val nm1 = freshen(nm)
        val ann1 = ann match {
          case Left(k) => Left(substKind(kSubst,k))
          case Right(t) => Right(substTy(kSubst,tSubst,t))
        }
        (decls ++ List(GVarDecl(nm1,GAType(ann1))),kSubst, tSubst + (nm -> TVar(nm1)))
    })
    val retTy = substTy(kSubst1, tSubst1, m.retTy)
    val paramTypes = m.paramTypes.map(substTy(kSubst1, tSubst1, _))
    MethodSig(gParams, retTy, m.nm, paramTypes)
  }
}