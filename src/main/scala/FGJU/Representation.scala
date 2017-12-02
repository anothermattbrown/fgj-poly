package FGJU

object Representation {
  /*

  Design of representation.

  Objects are represented as a list of constructor arguments,
  and a class.

  A class contains a tuple of methods, a constructor, and
  an upcast function.

  The upcast function works on lists of "bound methods" --
  methods which carry the receiver argument.

  Types are currently encoded by a pair of field and method type.
  This means types with different names may be encoded as the
  same type. Probably not a big deal, but we could add
  a unique identifier (e.g. a type-level nat)

  Classes are embedded into the representation, rather than stored
  in a separate class environment. Using a class environment would probably
  require tying another knot, since there's so much mutual recursion between
  classes.

   */

  /* Example 1:

  class A{}
  class B{ A foo() { return new A(); }}
  new A()

  Classes:
    Z = TOP
    S<Z> = A
    S<S<Z>> = B

  Encoded classes:
    TOP = Class<Z,Nil,Nil,Z>
    A   = Class<S<Z>,Nil,Nil,Z>
    B   = Class<S<S<Z>>,Nil,BMethods,S<Z>>

  BMethods:
    Pair<B_foo,Nil>

  B_foo:
    BoundExpr<Nil,A>
  */

  // TODO: idea! Since Pair isn't injective, we can't decompose it.
  // what else can we do? Always pass around decomposed pairs!

  // Since FGJU doesn't have update (of either fields or methods), we
  // can use the "Recursive Records" encoding described in section
  // 18.3.2 of Abadi-Cardelli


  // try to add type names:
  // Z = Top, S<Z> = A, S<S<Z>> = B
  // the name is a phantom type parameter on Obj and Class
  val Example1b =
    """let TOP : * = Obj<Z,Nil,Nil> in
      |let TOPClass : * = Class<Z,Nil,Nil,TOP> in
      |  new Class<Z,Nil,Nil,TOP> (
      |    new FunsNil<Obj<Z,Nil,Nil>>(),
      |    new SubObj<Nil,Nil,Nil,Nil>(new SubRefl<Nil>(), new SubRefl<Nil>())
      |  )
      |in
      |let AFields : * = Nil in
      |let AMethods : * = Nil in
      |let ASuper : * = TOP in
      |let A : * = Obj<S<Z>,Nil,Nil> in
      |let AClass : Class<Nil,Nil,TOP> =
      |  new Class<Nil,Nil,TOP>(
      |    new FunsNil<Obj<Nil,Nil>>(),
      |    new SubObj<Nil,Nil,Nil,Nil>(new SubRefl<Nil>(), new SubRefl<Nil>())
      |  )
      |in
      |let BFields  : *      = Nil in
      |let TyB_foo  : * -> * = \B:*. Expr<B,Nil,A> in
      |let BMethods : * -> * = \B:*. Pair<TyB_foo<B>,Nil> in
      |let B : * = Obj<Nil,BMethods> in
      |let B_foo_Env : * = Nil in
      |let B_foo : TyB_foo<B> =
      |  new NewExpr<B,B_foo_Env,AFields,AMethods,ASuper>(
      |    AClass,
      |    new NilExprs<B,B_foo_Env>()
      |  )
      |in
      |let bFields : BFields = new Nil() in
      |let bMethods : BMethods<B> =
      |  new Pair<TyB_foo<B>,Nil>(
      |    B_foo,
      |    new Nil()
      |  )
      |in
      |let BClass : Class<BFields,BMethods,A> =
      |  new Class<BFields,BMethods,A>(bFields, bMethods)
      |in
      |new Call
    """.stripMargin

  val FunsNilSrc =
    """class FunsNil<In> extends Fun<In, Nil> {
      |  Nil apply(In o) { return new Nil(); }
      |}
    """.stripMargin

  val FunsConsSrc =
    """class FunsCons<In,OutHd,OutTl>
      |  extends Fun<In, Pair<OutHd, OutTl>> {
      |  Fun<In,OutHd> funHd;
      |  Fun<In,OutTl> funTl;
      |
      |  Pair<OutHd,OutTl> apply(In x) {
      |    return new Pair<OutHd,OutTl>(
      |      this.funHd.apply(x),
      |      this.funTl.apply(x)
      |    );
      |  }
      |} """.stripMargin

  val SupertypeOfSrc =
    """class SupertypeOf<A,B extends A> {
        |  A upcast(B b) { return b; }
        |}
      """.stripMargin
  // Polymorphic type-application function (as in Brown-Palsberg POPL'15)
    val TypeAppSrc =
      """class TypeApp {
        |  <+X,T:X -> *,A:X> T<A> apply(<A:X> T<A> e) { return e<A>; }
        |}
      """.

        stripMargin

    val
    KindAppSrc =

      """class KindApp {
        |  <T:<X>*, +X> T<+X> apply(<+Y> T<+Y> e) { return e<+X>; }
        |}
      """.stripMargin

    val UnderTAbsSrc =

      """class UnderTAbs {
        |  <+X,T:X -> *,R:X -> *> (<A:X> R<A>) apply(<A:X> Fun<T<A>, R<A>> f, <A:X> T<A> x) {
        |    return /\A:X. f<A>.apply(x<A>);
        |  }
        |}
      """.
        stripMargin

  val FunSrc =
      """class Fun<A,R> {
        |  R apply(A a) { return this.apply(a); }
        |}
      """.
        stripMargin

  val PairSrc =
    """class Pair<A,B> {
        |  A fst;
        |  B snd;
        |}
      """.stripMargin
  val NilSrc =
    """class Nil{}"""

  val IndexSrc =
    """class Index<Env,T> {
      |  <R> R accept(IndexVisitor<Env,T,R> v) {
      |    return this.<R>accept(v);
      |  }
      |}
    """.
      stripMargin

  val IndexVisitorSrc =
    """class IndexVisitor<Env,T,R> {
      |   <Env1>   R visitZ(Eq<Env,Pair<T,Env1>> eq) { return this.<Env1>visitZ(eq); }
      |   <A,Env1> R visitS(Eq<Env,Pair<A,Env1>> eq, Index<Env1,T> idx) { return this.<A,Env1>visitS(eq,idx); }
      |}
    """
      .stripMargin

  val IndexZSrc =
    """class IndexZ<T,Env> extends Index<Pair<T,Env>, T> {
      |  <R> R accept(IndexVisitor<Pair<T,Env>,T,R> v) {
      |    return v.<Env>visitZ(new Refl<Pair<T,Env>>());
      |  }
      |}
    """.
      stripMargin

  val IndexSSrc =
    """class IndexS<S,T,Env> extends Index<Pair<S,Env>, T> {
      |  Index<Env,T> idx;
      |  <R> R accept(IndexVisitor<Pair<S,Env>, T, R> v) {
      |    return v.<S,Env>visitS(new Refl<Pair<S,Env>>(), this.idx);
      |  }
      |}
    """.stripMargin
  // Leibniz equality proofs, as in Brown-Palsberg POPL17/18
  val EqSrc =
    """class Eq<A,B> {
      | <F : * -> *> F<B> toRight(F<A> x) { return this.<F>toRight(x); }
      | <F : * -> *> F<A> toLeft(F<B> x) { return this.<F>toLeft(x); }
      |}
    """.stripMargin

  val ReflSrc =
    """class Refl<A> extends Eq<A,A> {
      |  <F : * -> *> F<A> toRight(F<A> x) { return x; }
      |  <F : * -> *> F<A> toLeft(F<A> x) { return x; }
      |}
    """.stripMargin

  val SubSrc =
    """class Sub<A,B> {
      |  B upcast(A a) { return this.upcast(a); }
      |}
    """.stripMargin

  val SubReflSrc =
    """class SubRefl<A> extends Sub<A,A> {
      |  A upcast(A a) { return a; }
      |}
    """.stripMargin

  val SubTransSrc =
    """class SubTrans<A,B,C> extends Sub<A,C> {
      |  Sub<A,B> subAB;
      |  Sub<B,C> subBC;
      |  C upcast(A a) {
      |    return this.subBC.upcast(this.subAB.upcast(a));
      |  }
      |}
    """.stripMargin

  val SubPairDepthSrc =
    """class SubPairDepth<A1,B1,A2,B2> extends Sub<Pair<A1,B1>, Pair<A2,B2>> {
      |  Sub<A1,A2> subA;
      |  Sub<B1,B2> subB;
      |  Pair<A2,B2> upcast(Pair<A1,B1> p) {
      |    return new Pair<A2,B2> (
      |      this.subA.upcast(p.fst),
      |      this.subB.upcast(p.snd)
      |    );
      |  }
      |}
    """.stripMargin

  val SubPairWidthSrc =
    """class SubPairWidth<A,B> extends Sub<Pair<A,B>, B> {
      |  B upcast(Pair<A,B> p) { return p.snd; }
      |}
    """.stripMargin


  val SubEnvConsSrc =
    """class SubEnvCons<Hd,Tl> extends Sub<Pair<Hd,Tl>, Tl> {
      |  Tl upcast(Pair<Hd,Tl> p) { return p.snd; }
      |}
    """.stripMargin

  // turn an ExprVisitor into a Sub
  val SubExprVisitorSrc =
    """class SubExprVisitor<This,Env,T,Sup:* -> *> extends
      |  Sub<Expr<This,Env,T>, Sup<T>> {
      |
      |  ExprVisitor<This,Env,T,Sup> v;
      |
      |  Sup<T> upcast(Expr<This,Env,T> e) {
      |    return e.<Sup>accept(this.v);
      |  }
      |}
    """.stripMargin

  // subtype exression by change the environment
  // (parameter) types. Contravariance.
  val SubExprSrc =
    """class SubExpr<This,Env1,Env2,T> extends
      |    ExprVisitor<This,Env1, T, λT. Expr<This,Env2,T>> {
      |  Sub<Env2,Env1> subEnv;
      |
      |  Expr<This,Env2,T> _this(Sub<This,T> sub) {
      |    return new ThisExpr<This,Env2,T>(sub);
      |  }
      |
      |  <Env0>
      |  Expr<This,Env2,T>
      |  var(Sub<Env1,Env0> subEnv, Index<Env0,T> idx) {
      |    return new VarExpr<This,Env2,Env0,T>(
      |      new SubTrans<Env2,Env1,Env0>(this.subEnv,subEnv),
      |      idx
      |    );
      |  }
      |
      |}
    """.stripMargin
  // TODO: new way of encoding class, objects, and subtyping
  // rather than having each class point to its supertype,
  // use subtype witnesses. these witness two properties: the
  // fields tuple type of a subtype is a subtype of the supertype's
  // fields tuple type. Similar for methods. The tuple subtype
  // witnesses are similar to Index.

  // Encoding of object values. The self-referential knot is tied simultaneously for all objects.
  // this is a classical technique from the object encoding literature. See the Abadi-Cardelli book.
  val ObjSrc =
    """class Obj<Fields,Methods> {
      |  Fields fields;
      |  Fun<Obj<Fields,Methods>, Methods> methods;
      |}
    """.stripMargin

  val ClassSrc =
    """class Class<Fields,Methods,Super> {
      |  Fun<Obj<Fields,Methods>,Methods> methods;
      |  Fun<Obj<Fields,Methods>,Super> upcastFun;
      |
      |  Obj<Fields,Methods> newInstance(Fields fields) {
      |    return new Obj<Fields,Methods>(fields, this.methods);
      |  }
      |}
    """.stripMargin

  val ExprSrc =
    """class Expr<This,Env,T> {
      |  <Ret:* -> *> Ret<T> accept(ExprVisitor<This,Env,T,Ret> v) { return this.<Ret>accept(v); }
      |}
    """.stripMargin

  val VarExprSrc =
    """class VarExpr<This,Env,Env1,T> extends Expr<This,Env,T> {
      |  Sub<Env,Env1> subEnv;
      |  Index<Env1,T> idx;
      |  <Ret:* -> *> Ret<T> accept(ExprVisitor<This,Env,T,Ret> v) {
      |    return v.<Env1>var(this.subEnv, this.idx);
      |  }
      |}
    """.stripMargin

  val ThisExprSrc =
    """class ThisExpr<This,Env,T> extends Expr<This,Env,T> {
      |  Sub<This,T> sub;
      |  <Ret:* -> *> Ret<T> accept(ExprVisitor<This,Env,T,Ret> v) { return v._this(this.sub); }
      |}
    """.stripMargin

  val GetFieldSrc =
    """class GetFieldExpr<This,Env,Fields,Methods,Super,T> extends Expr<This,Env,T> {
      |  Expr<This,Env,Obj<Fields,Methods>> e;
      |  Index<Fields,T> fld;
      |  <Ret:* -> *> Ret<T> accept(ExprVisitor<This,Env,T,Ret> v) { return v.<Fields,Methods,Super>getField(this.e, this.fld); }
      |}
    """.stripMargin

  val CallMethodSrc =
    """class CallMethodExpr<This,Env,Fields,Methods,Super,Args,T> extends Expr<This,Env,T> {
      |  Expr<This,Env,Obj<Fields,Methods>> e;
      |  Index<Methods,BoundExpr<Args,T>> method;
      |  Exprs<This,Env,Args> args;
      |  <Ret : * -> *> Ret<T> accept(ExprVisitor<This,Env,T,Ret> v) {
      |    return v.<Fields,Methods,Super,Args>callMethod(this.e,this.method,this.args);
      |  }
      |}
    """.stripMargin

  val NewObjectSrc =
    """class NewObject<This,Env,Fields,Methods,Super> extends Expr<This,Env,Obj<Fields,Methods>> {
      |  Class<Fields,Methods,Super> _class;
      |  Exprs<This,Env,Fields> fields;
      |
      |  <Ret : * -> *> Ret<Obj<Fields,Methods>> accept(ExprVisitor<This,Env,Obj<Fields,Methods>,Ret> v) {
      |    return v.<Fields,Methods,Super>newObject(
      |      new Refl<Obj<Fields,Methods>>(),
      |      this._class,
      |      this.fields
      |    );
      |  }
      |}
    """.stripMargin

  // expression with the receiver type obscured (via an existential)
  val BoundExprSrc =
    """class BoundExpr<Env,T> {
      |  <Ret> Ret accept(BoundExprVisitor<Env,T,Ret> v) {
      |    return this.<Ret>accept(v);
      |  }
      |}
    """.stripMargin
  val BoundExprVisitorSrc =
    """class BoundExprVisitor<Env,T,Ret> {
      |  <This> Ret boundExpr(This _this, Expr<This,Env,T> e) {
      |    return this.<This>boundExpr(_this,e);
      |  }
      |}
    """.stripMargin
  val SomeBoundExprSrc =
    """class SomeBoundExpr<This,Env,T> extends BoundExpr<Env,T> {
      |  This _this;
      |  Expr<This,Env,T> e;
      |  <Ret> Ret accept(BoundExprVisitor<Env,T,Ret> v) {
      |    return v.<Ret>boundExpr(this._this,this.e);
      |  }
      |}
    """.stripMargin

  val ExprsSrc =
    """class Exprs<This,Env,Ts> {
      |}
    """.stripMargin

  val
  ExprVisitorSrc =
    """class ExprVisitor<This,Env,T,Ret : * -> *> {
        |  <Env1> Ret<T> var(Sub<Env,Env1> subEnv, Index<Env1,T> idx) {
        |    return this.<Env1>var(subEnv,idx);
        |  }
        |  Ret<T> _this(Sub<This,T> sub) { return this._this(sub); }
        |
        |  <Fields,Methods,Super>
        |  Ret<T>
        |  getField(Expr<This,Env,Obj<Fields,Methods>> e,
        |           Index<Fields, T> fld) {
        |    return this.<Fields,Methods,Super>getField(e,fld);
        |  }
        |
        |  <Fields,Methods,Super,As>
        |  Ret<T>
        |  callMethod(Expr<This,Env,Obj<Fields,Methods>> e,
        |             Index<Methods,BoundExpr<As,T>> method,
        |             Exprs<This,Env,As> as) {
        |    return this.<Fields,Methods,Super,As>callMethod(e,method,as);
        |  }
        |
        |  <Fields,Methods,Super>
        |  Ret<T>
        |  newObject(Eq<T,Obj<Fields,Methods>> eq,
        |            Class<Fields,Methods,Super> _class,
        |            Exprs<This,Env,Fields> fields) {
        |    return this.<Fields,Methods,Super>newObject(eq,_class,fields);
        |  }
        |
        |  <Fields,Methods>
        |  Ret<T>
        |  upcast(Expr<This,Env,Obj<Fields,Methods>> e) {
        |    return this.<Fields,Methods>upcast(e);
        |  }
        |
        |  <+X, F : X -> *>
        |  Ret<T>
        |  tAbs(Eq<T, <A:X> F<A>> eq, <A:X> Expr<This,Env,F<A>> e) {
        |    return this.<+X,F>tAbs(eq,e);
        |  }
        |
        |  <+X, F : X -> *, A:X>
        |  Ret<T>
        |  tApp(Eq<T, F<A>> eq, Expr<This,Env,<B:X>F<B>> e) {
        |    return this.<+X,F,A>tApp(eq,e);
        |  }
        |
        |  <F : <K>*>
        |  Ret<T>
        |  kAbs(Eq<T, <+K>F<+K>> eq, <+K> Expr<This,Env,F<+K>> e) {
        |    return this.<F>kAbs(eq,e);
        |  }
        |
        |  <F : <K>*, +K>
        |  Ret<T>
        |  kApp(Eq<T, F<+K>> eq, Expr<This,Env,<+K>F<+K>> e) {
        |    return this.<F,+K>kApp(eq,e);
        |  }
        |}
      """.stripMargin

  // Tagless-final style.
  val SemSrc1 =
    """class Sem<R : * -> * -> * -> *> {
      |  <This,Env>
      |    R<This,Env,This>
      |    _this() { return this.<This,Env>_this(); }
      |
      |  <This,Env,T>
      |    R<This,Env,T>
      |    var(Index<Env,T> idx) { return this.<This,Env,T>var(idx); }
      |
      |  <This,Env, +X, T : X -> *>
      |    R<This,Env,<A:X>T<A>>
      |    tAbs(<A:X> R<This,Env,T<A>> e) {
      |      return this.<This,Env,+X,T>tAbs(e);
      |    }
      |
      |  <This,Env,+X, T : X -> *, A:X>
      |    R<This,Env,T<A>>
      |    tApp(R<This,Env,<B:X>T<B>> e) {
      |      return this.<This,Env,+X,T,A>tApp(e);
      |    }
      |
      |  <This,Env,T : <K>*>
      |    R<This,Env,<+K>T<+K>>
      |    kAbs(<+K> R<This,Env,T<+K>> e) {
      |      return this.<This,Env,T>kAbs(e);
      |    }
      |
      |  <This,Env,T : <K>*, +K>
      |    R<This,Env,T<+K>>
      |    kApp(R<This,Env,<+K>T<+K>> e) {
      |      return this.<This,Env,T,+K>kApp(e);
      |    }
      |}
    """.
      stripMargin
  // Tagless-final style.
  // Gets tricky though: how do we account for the fact that Fields/Methods/Super refer
  // to R? We can make them (* -> *) -> *, and write Fields<R>, etc. Is that sufficient?
  val SemSrc =
  """class Sem<This,Env,R : * -> *> {
      |    R<This>
      |    _this() { return this._this(); }
      |
      |  <T>
      |    R<T>
      |    var(Index<Env,T> idx) { return this.<T>var(idx); }
      |
      |  <Fields,Methods,Super,T>
      |    R<T>
      |    getField(R<Obj<Fields,Methods,Super>> e,
      |             Index<Fields, T> fld) {
      |      return this.<Fields,Methods,Super,T>getField(e,fld);
      |    }
      |
      |  <Fields,Methods,Super,As,T>
      |    R<T>
      |    callMethod(R<Obj<Fields,Methods,Super>> e,
      |               Index<Methods,BoundExpr<As,T>> method,
      |               Tuple<R,As> as) {
      |      return this.<Fields,Methods,Super,As>callMethod(e,method,as);
      |    }
      |
      |  <Fields,Methods,Super>
      |    Obj<Fields,Methods,Super>
      |    newObject(Class<Fields,Methods,Super> _class,
      |              Tuple<R,Fields> fields) {
      |      return this.<Fields,Methods,Super>newObject(_class,fields);
      |    }
      |
      |  <+X, T : X -> *>
      |    R<<A:X>T<A>>
      |    tAbs(<A:X> R<T<A>> e) {
      |      return this.<+X,T>tAbs(e);
      |    }
      |
      |  <+X, T : X -> *, A:X>
      |    R<T<A>>
      |    tApp(R<<B:X>T<B>> e) {
      |      return this.<+X,T,A>tApp(e);
      |    }
      |
      |  <T : <K>*>
      |    R<<+K>T<+K>>
      |    kAbs(<+K> R<T<+K>> e) {
      |      return this.<T>kAbs(e);
      |    }
      |
      |  <T : <K>*, +K>
      |    R<T<+K>>
      |    kApp(R<<+K>T<+K>> e) {
      |      return this.<T,+K>kApp(e);
      |    }
      |}
    """.stripMargin


  /* Need a way to link Q = [X] T and ExpQ = [X] Exp<T>.
       at inst, could have Q ~> T[X:=S] and ExpQ ~> Exp<T[X:=S]>
       but then at tAbs : Exp<Q>, we need an ExpQ.
       how can we link up the ExpQ inside and outside the tAbs?

       Could use another type parameter I guess?
       PExp<[X]T, [X]Exp<T>>
       Then typeAbs would have to use that parameter for Q...
       Probably won't work if we have nested quantifiers/instantiations...

       It seems we need higher kinds. But would that even help us without kind
       polymorphism? Maybe not. That means we'd need an infinite number of representation constructors and
       visitor methods.

       Let's return for a moment to FGJ_omega. We want a polymorphic object. Can we use instead
       a polymorphic method?

       twould be brutal: call would have to thread the type parameters throughout each type.
       <Ret<_>, This<_>, Env<_>, T<_> P> Exp<Ret<P>> call(Exp<This<_>, ...)

       Ok wait. Can I move a term quantifier to a method quantifier? Not sure this would help...

       class Forall {
         <T> method([X]A foo) { return (A[X:=T])foo; }
       }

       Looks like we need both F_omega kinds and first-class polymorphism.
       Plus an infinite number of Under classes.
       class Under_*<T<_>> implements Under<[X]Exp<T<X>>, [X]T<X>> {
         [X]T<X> under([X]Exp<T<X>> thing, [T]Fun<Exp<T>,T> f);
       }

       Aha! We need to get generalization into the convertibility relation also.
                [X]T ~> T[X:=S]
              -------------------
                T[X:=S] ~> [X]T

       Would have to do a check at a generalization cast:
             Gamma |-   e : T[X:=S]
             -------------------------   X not in FTV(Gamma)
             Gamma |-  ([X]T)e : [X]T

       How would typeAbs work then?

       <ExpT ~> Exp<T0>, T0 ~> T>
         Exp<T>
         typeAbs(ExpT e);

       Doesn't really make sense; T0 is an open type, so how are we able to  it?
       Is it really sufficient that its FTVs are not in the term env?
       I don't know; seems fishy
     */

  /*

  <Fields,Methods,Super>
    Ret
    getField(
      Expr<This,Env,Obj<Fields,Methods,Super>> e,
      Index<Fields, T> fld);

  <Fields,Methods,Super,As>
    Ret
    callMethod(
      Expr<This,Env,Obj<Fields,Methods,Super>> e,
      Index<Methods,BoundExpr<As,T>> method,
      Exprs<This,Env,As> as);

  <Fields,Methods,Super>
    Ret
    newObject(
      Iso<T,Obj<Fields,Methods,Super>> iso,
      Class<Fields,Methods,Super> _class,
      Exprs<This,Env,Fields> fields);

  <Fields,Methods>
    Ret
    cast(Expr<This,Env,Obj<Fields,Methods,T>> e);

   */

}