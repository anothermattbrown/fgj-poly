package FGJPoly {


  class Typechecker(cEnv : Map[Ident,ClassDecl] = Map(),
                    kEnv : Set[Ident] = Set(),
                    tEnv : Map[Ident,Either[Kind,Type]] = Map(),
                    env : Map[Ident,Type] = Map(),
                    thisType : Option[Type] = None) {
    def assertTypeIsWellFormed(ty : Type) : Unit = ty match {
      case Top => ()
      case TClass(nm,List()) => {
        if(tEnv.contains(nm))
          return
        if(!cEnv.contains(nm))
          throw new Exception("undeclared type " + nm)
        if(cEnv(nm).params.nonEmpty)
          throw new Exception("incorrect number of type parameters for type " + nm)
      }
      case TClass(nm,actuals) => {
        val c : ClassDecl = cEnv getOrElse(nm, throw new Exception("unknown class " + ty))
        val kindOrBounds = c.params.map(_.kindOrBound)
        if(kindOrBounds.length != actuals.length)
          throw new Exception("incorrect number of types parameters for type " + nm)
        else
          actuals.zip(kindOrBounds).foreach({
            case (ty,Left(k)) => assert(tcType(ty) == k, "class type parameter has wrong kind")
            case (sub,Right(sup)) => assertIsSubtypeOf(sub,sup)
          })
      }
      case TForallTy(nm,kindOrBound,ty) => addTypeVar(nm,kindOrBound).assertTypeIsWellFormed(ty)
    }

    def addTypeVar(nm : Ident, kindOrBound : Either[Kind,Type]) : Typechecker =
      new Typechecker(cEnv, kEnv, tEnv + (nm -> kindOrBound), env, thisType)
    def addKindVar(nm : Ident) : Typechecker = new Typechecker(cEnv, kEnv + nm, tEnv, env, thisType)

    // subst1 is newer than subst2. apply subst1 to each type in subst2, then extend the resulting
    // substitution with subst1's entries
    def composeSubsts(subst1 : Map[Ident,Type], subst2 : Map[Ident,Type]) : Map[Ident,Type] = {
      subst2.mapValues(substTy(subst1,_)) ++ subst1
    }

    def getParentType(t : Type) : Type = t match {
      case Top => throw new Exception("Top has no parent type")
      case TClass(nm,params) => {
        val classDecl = cEnv.getOrElse(nm,throw new Exception("undeclared class " + nm))
        val subst : Map[Ident,Type] = Map() ++ classDecl.params.map(_.nm).zip(params)
        substTy(subst,classDecl.superClass)
      }
      case TForallTy(_,_,_) => throw new Exception("Forall types have no parent types")
    }

    def substKind(kSubst : Map[Ident,Kind], k : Kind) : Kind = k match {
      case Star => Star
      case KVar(nm) => kSubst getOrElse(nm,k)
      case KArr(k1,k2) => KArr(substKind(kSubst,k1),substKind(kSubst,k2))
      case KForall(nm,k1) => {
        val nm1 = freshen(nm)
        KForall(nm1,substKind(kSubst + (nm -> KVar(nm1)), k1))
      }
    }

    def normalizeTy (t:Type, tSubst : Map[Ident,Type] = Map(), kSubst : Map[Ident,Kind] = Map()) : Type = t match {
      case TClass(nm, List()) => tSubst get(nm) getOrElse(t)
      case TTApp(t1,t2) => normalizeTy(t1,tSubst,kSubst) match {
        case TTAbs(nm,_,bdy) => {
          val t2nf = normalizeTy(t2,tSubst,kSubst)
          normalizeTy(bdy,tSubst + (nm -> t2nf),kSubst)
        }
      }
      case TKApp(t,k) => normalizeTy(t,tSubst,kSubst) match {
        case TKAbs(nm,bdy) => normalizeTy(bdy,tSubst,kSubst + (nm -> k))
      }
      case TTAbs(nm,kindOrBound,bdy) => {
        val nm1 = freshen(nm)
        val kindOrBound1 = kindOrBound match {
          case Left(k)  => Left(substKind(kSubst,k))
          case Right(t) => Right(normalizeTy(t,tSubst,kSubst))
        }
        TTAbs(nm1,kindOrBound,normalizeTy(bdy,tSubst + (nm -> TClass(nm1,List())),kSubst))
      }
      case TForallTy(nm,kindOrBound,bdy) => {
        val nm1 = freshen(nm)
        val kindOrBound1 = kindOrBound match {
          case Left(k)  => Left(substKind(kSubst,k))
          case Right(t) => Right(normalizeTy(t,tSubst,kSubst))
        }
        TForallTy(nm1,kindOrBound,normalizeTy(bdy,tSubst + (nm -> TClass(nm1,List())),kSubst))
      }
      case TKAbs(nm,bdy) => {
        val nm1 = freshen(nm)
        TKAbs(nm1,normalizeTy(bdy,tSubst,kSubst + (nm -> KVar(nm1))))
      }
      case TForallK(nm,bdy) => {
        val nm1 = freshen(nm)
        TForallK(nm1,normalizeTy(bdy,tSubst,kSubst + (nm -> KVar(nm1))))
      }
    }

    def assertIsSubtypeOf(sub : Type, sup : Type) : Unit = {
      // precondition: sub and sup are both valid types
      if(sub == sup) return
      sub match {
        case TClass(nm,List()) if tEnv contains(nm) => {
          val kindOrBound : Either[Kind,Type] = tEnv get(nm) get
          val parent : Type = kindOrBound.getOrElse(throw new Exception("assertSubtypeOf: type variable is not kind *"))
          assertIsSubtypeOf(parent, sup)
        }
        case TClass(nm,params) => assertIsSubtypeOf(getParentType(sub), sup)
        case TForallTy(_,_,_)  => throw new Exception("Forall types are not subtypes of any type\n sub: " + sub + "\n sup: " + sup)
        case TForallK(_,_)     => throw new Exception("Forall types are not subtypes of any type\n sub: " + sub + "\n sup: " + sup)
      }
    }

    def addClassDecl(cd : ClassDecl) : Typechecker = addClassDecls(List(cd))
    def addClassDecls(ds : List[ClassDecl]) : Typechecker = {
      // check classes weren't already declared.
      ds.foreach(d => {
        if(cEnv contains(d nm))
          throw new Exception("class " + d.nm + " already declared")
      })

      val tc = new Typechecker(cEnv ++ ds.map(d => d.nm -> d), kEnv, tEnv, env, thisType)

      // typecheck last, so all the recursion/mutual recursion will work
      ds.foreach(d => {
        tc.tcClassDecl(d nm)
      })

      tc
    }

    def addTVarDecl(d : TVarDecl) : Typechecker = {
      d.kindOrBound.foreach(assertTypeIsWellFormed(_))
      new Typechecker(cEnv, kEnv, tEnv + (d.nm -> d.kindOrBound), env, thisType)
    }
    def addTVarDecls(decls: List[TVarDecl]) : Typechecker = {
      decls.foldLeft(this)({case (tc,d) => tc.addTVarDecl(d)})
    }

    def addVarDecls(decls: List[VarDecl]) : Typechecker = {
      decls.foreach(d => assertTypeIsWellFormed(d.ty))
      new Typechecker(cEnv, kEnv, tEnv, env ++ decls.map(d => d.nm -> d.ty), thisType)
    }

    def setThisType(ty : Type) : Typechecker = new Typechecker(cEnv, kEnv, tEnv, env, Some(ty))

    def tcType(t : Type) : Kind = t match{
      case TForallTy(nm,kindOrBound,bdy) => {
        assert(addTypeVar(nm,kindOrBound).tcType(bdy) == Star, "Forall type body failed to kind-check")
        Star
      }
      case TForallK(nm,bdy) => {
        assert(addKindVar(nm).tcType(bdy) == Star, "Forall kind body failed to kind-check")
        Star
      }

    }
    def tcExpr(e : Expr) : Type = e match {
      case Var(nm) => env get nm getOrElse(throw new Exception("undeclared variable " + nm))
      case Field(obj,nm) => lookupFieldType(tcExpr(obj),nm)
      case This => thisType get
      case Call(e,actualTys,nm,actuals) => {
        val m = lookupMethodSig(tcExpr(e),nm)
        assert(
          actualTys.length == m.tParams.length,
          "wrong number of type parameters in call: " + Call(e,actualTys,nm,actuals)
        )
        // check type parameter bounds
        m.tParams.zip(actualTys).foreach { case (vd,ty) => vd.kindOrBound.foreach(assertIsSubtypeOf(ty,_)) }
        val subst = Map() ++ m.tParams.map(_.nm).zip(actualTys)

        // check we have the right number of parameters
        assert(actuals.length == m.paramTypes.length)
        var expectedTypes = m.paramTypes.map(substTy(subst,_))
        var actualTypes = actuals.map(tcExpr(_))
        actualTypes.zip(expectedTypes).foreach { case (sub,sup) => assertIsSubtypeOf(sub,sup) }

        substTy(subst,m.retTy)
      }
    }

    // require the decl to be in cEnv for recursion
    def tcClassDecl(nm : Ident) : Unit = {
      val c : ClassDecl = cEnv get(nm) get
      // todo: check superclass, bounds are well-formed
      // todo: check field types are well-formed
      val tc = addTVarDecls(c.params).setThisType(TClass(c.nm,c.params.map(d => TClass(d.nm,List()))))
      c.methods.foreach(tc.tcMethod(_))
    }

    def tcMethod(m : MethodDecl) : Unit = {
      // add type parameters to the context. this checks bounds are well-formed
      val tc1 = addTVarDecls(m.tParams)
      tc1.assertTypeIsWellFormed(m.retTy)
      val tc2 = tc1.addVarDecls(m.params)
      tc2.tcExpr(m.bdy)
    }

    def substTy(subst : Map[Ident,Type], ty : Type) : Type = ty match {
      case Top => Top
      case TClass(nm,List())  => subst get nm getOrElse(ty)  // type variable cannot have params
      case TClass(nm,params)  => TClass(nm, params map(substTy(subst,_))) // class with params cannot be a type variable
      case TForallTy(nm,kindOrBound,bdy) => TForallTy(nm,kindOrBound.map(substTy(subst,_)),substTy(subst - nm, bdy))
      case TForallK(nm,bdy) => TForallK(nm,substTy(subst,bdy))
    }

    def lookupFieldType(ty : Type, nm : String) : Type = {
      // Don't support field access on quantified types.
      val ty1 : TClass = ty.asInstanceOf[TClass]
      val classDecl = cEnv get ty1.nm get

      if(classDecl.params.length != ty1.params.length)
        throw new Exception("lookupFieldType: wrong number of class type parameters")
      val subst : Map[Ident,Type] = Map() ++ classDecl.params.map(_.nm).zip(ty1.params)
      val fieldTy = classDecl.fields.filter(vd => vd.nm == nm)(0).ty
      substTy(subst,fieldTy)
    }

    case class MethodSig(tParams : List[TVarDecl], retTy : Type, paramTypes : List[Type])

    def lookupMethodSig(ty : Type, nm : String) : MethodSig = {
      // Don't support field access on quantified types.
      val ty1 : TClass = ty.asInstanceOf[TClass]
      val classDecl = cEnv get ty1.nm get

      if(classDecl.params.length != ty1.params.length)
        throw new Exception("lookupFieldType: wrong number of class type parameters")
      val subst : Map[Ident,Type] = Map() ++ classDecl.params.map(_.nm).zip(ty1.params)
      val md = classDecl.methods.filter(m => m.nm == nm)(0)
      val sig = MethodSig(md.tParams,md.retTy,md.params.map(_.ty))
      substMethodSig(subst,sig)
    }

    def substMethodSig(subst: Map[Ident, Type], m: MethodSig) : MethodSig = {
      val subst1 = subst -- m.tParams.map(vd => vd.nm)
      val retTy = substTy(subst1, m.retTy)
      val paramTypes = m.paramTypes.map(substTy(subst1,_))
      MethodSig(m.tParams, retTy, paramTypes)
    }
  }

}