package FGJPoly {

  class Typechecker(cEnv : Map[String,ClassDecl] = Map(),
                    tEnv : Map[String,Type] = Map(),
                    env : Map[String,Type] = Map(),
                    thisType : Option[Type] = None) {
    def assertTypeIsWellFormed(ty : Type) : Unit = ty match {
      case Top => ()
      case TClass(nm,List()) => {
        if(tEnv.contains(nm))
          return
        if(!cEnv.contains(nm))
          throw new Exception("undeclared type " + nm)
        if(cEnv.get(nm).get.params.length != 0)
          throw new Exception("incorrect number of type parameters for type " + nm)
      }
      case TClass(nm,actuals) => {
        val c : ClassDecl = cEnv get nm getOrElse({
          throw new Exception("unknown class " + ty)
        })
        val upperBounds = c.params.map(_.upperBound)
        if(upperBounds.length != actuals.length)
          throw new Exception("incorrect number of types parameters for type " + nm)
        else
          actuals.zip(upperBounds).foreach(_ match {
            case (_,None) => ()
            case (sub,Some(sup)) => assertIsSubtypeOf(sub,sup)
          })
      }
      case TForall(params,ty) => updateTEnv(_ ++ params.map(d => d.nm -> d.upperBound.getOrElse(Top))).assertTypeIsWellFormed(ty)
    }

    def updateTEnv(f : Map[String,Type] => Map[String,Type]) : Typechecker = new Typechecker(cEnv, f(tEnv), env, thisType)

    def unifySubtype(ftvs : Set[String], sub : Type, sup : Type) : Map[String,Type] = {
      // find assignments to ftvs occurring in sub that makes it a subtype of sup.

      // if sub is a type variable, then assign it.
      // if sub is a class, then
      (sub,sup) match {
        // not sure we need this case...
        case (TClass(nm, List()), sup) if ftvs contains(nm) => Map(nm -> sup)
        case (Top,Top) => Map()
        case (Top,_) => throw new Exception("Top is not a subtype of any type")
        case (TClass(nm1, params1), TClass(nm2,params2)) if nm1 == nm2 => unifyAll(ftvs, params1, params2)
        case _ => {
          try {
            unifySubtype(ftvs, getParentType(sub), sup)
          } catch {
            case e : Exception => throw new Exception(sub + " is not a subtype of " + sup)
          }
        }
      }
    }

    def unifyAll(ftvs : Set[String], tys1 : List[Type], tys2 : List[Type]) : Map[String,Type] =
      (tys1,tys2) match {
        case (hd1::tl1, hd2::tl2) => {
          val subst1 = unifyAll(ftvs, tl1, tl2)
          val subst2 = unify(ftvs, substTy(subst1,hd1), substTy(subst1,hd2))
          composeSubsts(subst2, subst1)
        }
        case (Nil,Nil) => Map()
      }

    def unify(ftvs : Set[String], ty1 : Type, ty2 : Type) : Map[String,Type] = (ty1,ty2) match {
      case (TClass(nm, List()),_) if ftvs contains(nm) => Map(nm -> ty2)
      case (TClass(nm1, params1),TClass(nm2,params2)) if nm1 == nm2 => unifyAll(ftvs, params1, params2)
      case (Top,Top) => Map()
      case _ => throw new Exception("unify failed")
    }

    // subst1 is newer than subst2. apply subst1 to each type in subst2, then extend the resulting
    // substitution with subst1's entries
    def composeSubsts(subst1 : Map[String,Type], subst2 : Map[String,Type]) : Map[String,Type] = {
      subst2.mapValues(substTy(subst1,_)) ++ subst1
    }

    def getParentType(t : Type) : Type = t match {
      case Top => throw new Exception("Top has no parent type")
      case TClass(nm,params) => {
        val classDecl = cEnv.get(nm).getOrElse(throw new Exception("undeclared class " + nm))
        val subst : Map[String,Type] = Map() ++ classDecl.params.map(_.nm).zip(params)
        substTy(subst,classDecl.superClass)
      }
      case TForall(_,_) => throw new Exception("Forall types have no parent types")
    }

    // how do we represent type abstraction?
    // [A] new Nil<A>();  // polymorphic nil value of type [A] List<A>
    // [A] Expr<List<A>>
    // strip functions:
    // class StripExpr<T> {
    //   <A> T strip(Expr<A> e) { ... }
    // }
    // class Strip<T> {
    //   this is useless: just a constant T function
    //   <A> T strip(A e) { ... }
    // }

    def assertIsConvertibleTo(from : Type, to : Type) : Unit = {
      try {
        from match {
          case TForall(_, _) => assertIsInstantiationOf(to, from)
          case _ => assertIsSubtypeOf(from, to)
        }
      }
      catch {
        case e : Exception => throw new Exception(from + " is not convertible to " + to)
      }
    }

    def assertIsInstantiationOf(inst: Type, forall: Type) = (forall,inst) match {
      case (TForall(vs,TClass(nm1,ps1)), TClass(nm2,ps2))
        if nm1 == nm2 && ps1.length == ps2.length => {
          val nms = vs.map(_.nm)
          val upperBounds = Map() ++ vs.map(d => (d.nm,  d.upperBound))
          val subst = unifyAll(Set() ++ nms, ps1, ps2)
          nms.foreach(nm => assertIsSubtypeOf(subst(nm), upperBounds(nm).getOrElse(Top)))
      }
    }

    def assertIsSubtypeOf(sub : Type, sup : Type) : Unit = {
      // precondition: sub and sup are both valid types
      if(sub == sup) return
      if(sup == Top) return
      sub match {
        case TClass(nm,List()) if tEnv contains(nm) => assertIsSubtypeOf(tEnv get(nm) get, sup)
        case TClass(nm,params)  => assertIsSubtypeOf(getParentType(sub), sup)
        case TForall(params,ty) => throw new Exception("forall types are not subtypes of any type\n sub: " + sub + "\n sup: " + sup)
      }
    }

    def addClassDecl(cd : ClassDecl) : Typechecker = addClassDecls(List(cd))
    def addClassDecls(ds : List[ClassDecl]) : Typechecker = {
      // check classes weren't already declared.
      ds.foreach(d => {
        if(cEnv contains(d nm))
          throw new Exception("class " + d.nm + " already declared")
      })

      val tc = new Typechecker(cEnv ++ ds.map(d => d.nm -> d), tEnv, env, thisType)

      // typecheck last, so all the recursion/mutual recursion will work
      ds.foreach(d => {
        tc.tcClassDecl(d nm)
      })

      tc
    }

    def addTVarDecl(d : TVarDecl) : Typechecker = {
      d.upperBound.foreach(assertTypeIsWellFormed(_))
      new Typechecker(cEnv, tEnv + (d.nm -> d.upperBound.getOrElse(Top)), env, thisType)
    }
    def addTVarDecls(decls: List[TVarDecl]) : Typechecker = {
      decls.foldLeft(this)({case (tc,d) => tc.addTVarDecl(d)})
    }

    def addVarDecls(decls: List[VarDecl]) : Typechecker = {
      decls.foreach(d => assertTypeIsWellFormed(d.ty))
      new Typechecker(cEnv, tEnv, env ++ decls.map(d => d.nm -> d.ty), thisType)
    }

    def setThisType(ty : Type) : Typechecker = new Typechecker(cEnv, tEnv, env, Some(ty))

    def tcExpr(e : Expr) : Type = e match {
      case Var(nm) => env get nm getOrElse(throw new Exception("undeclared variable " + nm))
      case Field(obj,nm) => lookupFieldType(tcExpr(obj),nm)
      case This => thisType get
      case Cast(ty,e) => {
        assertTypeIsWellFormed(ty)
        assertIsConvertibleTo(tcExpr(e),ty)
        ty
      }
      case Call(e,actualTys,nm,actuals) => {
        val m = lookupMethodSig(tcExpr(e),nm)
        assert(
          actualTys.length == m.tParams.length,
          "wrong number of type parameters in call: " + Call(e,actualTys,nm,actuals)
        )
        // check type parameter bounds
        m.tParams.zip(actualTys).foreach { case (vd,ty) => assertIsSubtypeOf(ty,vd.upperBound.getOrElse(Top)) }
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
    def tcClassDecl(nm : String) : Unit = {
      val c = cEnv get(nm) get
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

    def substTy(subst : Map[String,Type], ty : Type) : Type = ty match {
      case Top => Top
      case TClass(nm,List())  => subst get nm getOrElse(ty)  // type variable cannot have params
      case TClass(nm,params)  => TClass(nm, params map(substTy(subst,_))) // class with params cannot be a type variable
      case TForall(params,ty) => TForall(params,substTy(subst -- params.map(_.nm), ty))
    }

    def lookupFieldType(ty : Type, nm : String) : Type = {
      // Don't support field access on quantified types.
      val ty1 : TClass = ty.asInstanceOf[TClass]
      val classDecl = cEnv get ty1.nm get

      if(classDecl.params.length != ty1.params.length)
        throw new Exception("lookupFieldType: wrong number of class type parameters")
      val subst : Map[String,Type] = Map() ++ classDecl.params.map(_.nm).zip(ty1.params)
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
      val subst : Map[String,Type] = Map() ++ classDecl.params.map(_.nm).zip(ty1.params)
      val md = classDecl.methods.filter(m => m.nm == nm)(0)
      val sig = MethodSig(md.tParams,md.retTy,md.params.map(_.ty))
      substMethodSig(subst,sig)
    }

    def substMethodSig(subst: Map[String, Type], m: MethodSig) : MethodSig = {
      val subst1 = subst -- m.tParams.map(vd => vd.nm)
      val retTy = substTy(subst1, m.retTy)
      val paramTypes = m.paramTypes.map(substTy(subst1,_))
      MethodSig(m.tParams, retTy, paramTypes)
    }
  }

}