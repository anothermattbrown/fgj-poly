package FGJU
import FGJU.Representation


object NewRepresentation {
  // Old version where I made Methods a type function,
  // to untie the recursive knot. This doesn't work with
  // SubObj though. So instead Methods is a list of BoundExprs.
  // Have to express the knot-tying somewhere else.
  val Example1Old =
  """letType TOP : * = Obj<Nil,FunsNil> in
    |letType TOPClass : * = Class<Nil,FunsNil,TOP> in
    |  new Class<Nil,FunsNil,TOP> (
    |    new FunsNil<Obj<Nil,FunsNil>>(),
    |    new SubObj<Nil,Nil,Nil,Nil>(new SubRefl<Nil>(), new SubRefl<Nil>())
    |  )
    |in
    |letType AFields : * = Nil in
    |letType AMethods : * = Nil in
    |letType ASuper : * = TOP in
    |letType A : * = Obj<Nil,Nil> in
    |letType AClass : Class<Nil,Nil,TOP> =
    |  new Class<Nil,Nil,TOP>(
    |    new FunsNil<Obj<Nil,Nil>>(),
    |    new SubObj<Nil,Nil,Nil,Nil>(new SubRefl<Nil>(), new SubRefl<Nil>())
    |  )
    |in
    |letType BFields  : *      = Nil in
    |letType TyB_foo  : * -> * = \B:*. Expr<B,Nil,A> in
    |letType BMethods : * -> * = \B:*. Pair<TyB_foo<B>,Nil> in
    |letType B : * = Obj<Nil,BMethods> in
    |letType B_foo_Env : * = Nil in
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
    |new NewExpr<TOP,Nil,AFields,AMethods,ASuper>(
    |  AClass,
    |  new NilExprs<TOP,Nil>()
    |)
  """.stripMargin

  /*  class A{}
      class B{ A foo() { return new A(); }}
      new A()
  */
  val Example1 =
    """letType TOP : * = Pair<Nil,Nil> in
      |let TOPClass : Class<Nil,Nil,TOP> =
      |  new Class<Nil,Nil,TOP> (
      |    new BindMethodsNil<TOP>(),
      |    new SubRefl<Pair<Nil,Nil>>()
      |  )
      |in
      |letType AFields : * = Nil in
      |letType AMethods : * = Nil in
      |letType ASuper : * = TOP in
      |letType A : * = Pair<Nil,Nil> in
      |let AClass : Class<Nil,Nil,TOP> =
      |  new Class<Nil,Nil,TOP>(
      |    new BindMethodsNil<A>(),
      |    new SubRefl<Pair<Nil,Nil>>()
      |  )
      |in
      |letType BFields  : * = Nil in
      |letType TyB_foo  : * = BoundExpr<Nil,A> in
      |letType BMethods : * = Pair<TyB_foo,Nil> in
      |letType B : * = Pair<Nil,BMethods> in
      |letType B_foo_Env : * = Nil in
      |let B_foo : Fun<Lazy<B>,TyB_foo> =
      |  new ExprBinder<B,Nil,A>(
      |    new NewExpr<B,B_foo_Env,AFields,AMethods,ASuper>(
      |      AClass,
      |      new NilExprs<B,B_foo_Env>()
      |    )
      |  )
      |in
      |let bFields : BFields = new Nil() in
      |let bMethods : Fun<Lazy<B>,BMethods> =
      |  new BindMethodsCons<B,TyB_foo,Nil>(
      |    B_foo,
      |    new BindMethodsNil<B>()
      |  )
      |in
      |let bUpcast : Sub<B,TOP> =
      |  new SubPairDepth<BFields,BMethods,Nil,Nil>(
      |    new SubRefl<Nil>(),
      |    new SubPairWidth<TyB_foo,Nil>()
      |  )
      |in
      |let BClass : Class<BFields,BMethods,TOP> =
      |  new Class<BFields,BMethods,A>(bMethods,bUpcast)
      |in
      |let a : Expr<TOP,Nil,A> =
      |  new NewExpr<TOP,Nil,AFields,AMethods,ASuper>(
      |    AClass,
      |    new NilExprs<TOP,Nil>()
      |  )
      |in a
    """.stripMargin

  /*  class A{}
      class B{ A foo() { return new A(); }}
      new B().foo()
  */
  val Example2 =
    """letType TOP : * = Pair<Nil,Nil> in
      |let TOPClass : Class<Nil,Nil,TOP> =
      |  new Class<Nil,Nil,TOP> (
      |    new BindMethodsNil<TOP>(),
      |    new SubRefl<Pair<Nil,Nil>>()
      |  )
      |in
      |letType AFields : * = Nil in
      |letType AMethods : * = Nil in
      |letType ASuper : * = TOP in
      |letType A : * = Pair<Nil,Nil> in
      |let AClass : Class<Nil,Nil,TOP> =
      |  new Class<Nil,Nil,TOP>(
      |    new BindMethodsNil<A>(),
      |    new SubRefl<Pair<Nil,Nil>>()
      |  )
      |in
      |letType BSuper   : * = TOP in
      |letType BFields  : * = Nil in
      |letType TyB_foo  : * = BoundExpr<Nil,A> in
      |letType BMethods : * = Pair<TyB_foo,Nil> in
      |letType B : * = Pair<Nil,BMethods> in
      |letType B_foo_Env : * = Nil in
      |let B_foo : Fun<Lazy<B>,TyB_foo> =
      |  new ExprBinder<B,Nil,A>(
      |    new NewExpr<B,B_foo_Env,AFields,AMethods,ASuper>(
      |      AClass,
      |      new NilExprs<B,B_foo_Env>()
      |    )
      |  )
      |in
      |let bFields : BFields = new Nil() in
      |let bMethods : Fun<Lazy<B>,BMethods> =
      |  new BindMethodsCons<B,TyB_foo,Nil>(
      |    B_foo,
      |    new BindMethodsNil<B>()
      |  )
      |in
      |let bUpcast : Sub<B,TOP> =
      |  new SubPairDepth<BFields,BMethods,Nil,Nil>(
      |    new SubRefl<Nil>(),
      |    new SubPairWidth<TyB_foo,Nil>()
      |  )
      |in
      |let BClass : Class<BFields,BMethods,TOP> =
      |  new Class<BFields,BMethods,A>(bMethods,bUpcast)
      |in
      |let bExpr : Expr<TOP,Nil,B> =
      |  new NewExpr<TOP,Nil,BFields,BMethods,BSuper>(
      |    BClass,
      |    new NilExprs<TOP,Nil>()
      |  )
      |in
      |let B_foo_idx : Index<BMethods,TyB_foo> =
      |  new IndexZ<TyB_foo,Nil>()
      |in
      |let aExpr : Expr<TOP,Nil,A> =
      |  new CallExpr<TOP,Nil,BFields,BMethods,BSuper,Nil,A>(
      |    bExpr,
      |    B_foo_idx,
      |    new NilExprs<TOP,Nil>()
      |  )
      |in
      |aExpr
    """.stripMargin

  val ClassSrc =
    """class Class<Fields,Methods,Super> {
      |  Fun<Lazy<Pair<Fields,Methods>>, Methods> methods;
      |  Sub<Pair<Fields,Methods>, Super> upcast;
      |}
    """.stripMargin

  val LazySrc =
    """class Lazy<T> {
      |  T force() {
      |    return this.force();
      |  }
      |}
    """.stripMargin

  val ConstructorSrc =
    """class Constructor<Fields,Methods> extends Lazy<Pair<Fields,Methods>> {
      |  Fields fields;
      |  Fun<Lazy<Pair<Fields,Methods>>, Methods> methods;
      |
      |  Pair<Fields,Methods> force() {
      |    return new Pair<Fields,Methods>(
      |      this.fields,
      |      this.methods.apply(this)
      |    );
      |  }
      |}
    """.stripMargin

  val BindMethodsNilSrc =
    """class BindMethodsNil<O> extends Fun<Lazy<O>,Nil> {
      |  Nil apply(Lazy<O> o) { return new Nil(); }
      |}
    """.stripMargin

  val BindMethodsConsSrc =
    """class BindMethodsCons<O,M,Ms> extends Fun<Lazy<O>,Pair<M,Ms>> {
      |  Fun<Lazy<O>,M> bindM;
      |  Fun<Lazy<O>,Ms> bindMs;
      |  Pair<M,Ms> apply(Lazy<O> o) {
      |    return new Pair<M,Ms>(
      |      this.bindM.apply(o),
      |      this.bindMs.apply(o)
      |    );
      |  }
      |}
    """.stripMargin

  val SubSrc = Representation.SubSrc
  val SubReflSrc = Representation.SubReflSrc
  val SubTransSrc = Representation.SubTransSrc
  val SubPairDepthSrc = Representation.SubPairDepthSrc
  val SubPairWidthSrc = Representation.SubPairWidthSrc
  val EqSrc = Representation.EqSrc
  val ReflSrc = Representation.ReflSrc
  val PairSrc = Representation.PairSrc
  val NilSrc = Representation.NilSrc
  val FunSrc = Representation.FunSrc
  val FunsNilSrc = Representation.FunsNilSrc
  val FunsConsSrc = Representation.FunsConsSrc
  val IndexSrc = "class Index<Env,T> extends Fun<Env,T> {}"
  val IndexZSrc =
    """class IndexZ<Hd,Tl> extends Index<Pair<Hd,Tl>, Hd> {
      |  Hd apply(Pair<Hd,Tl> p) { return p.fst; }
      |}
    """.stripMargin
  val IndexSSrc =
    """class IndexS<Hd,Tl,T> extends Index<Pair<Hd,Tl>, T> {
      |  Index<Tl,T> idx;
      |  T apply(Pair<Hd,Tl> p) { return this.idx.apply(p.snd); }
      |}
    """.stripMargin

  val ExprsSrc =
    """class Exprs<This,Env,Ts> {
      |}
    """.stripMargin
  val NilExprsSrc =
    """class NilExprs<This,Env> extends Exprs<This,Env,Nil> {
      |}
    """.stripMargin


  val ExprSrc =
    """class Expr<This,Env,T> {
      |  <Ret:* -> *> Ret<T> accept(ExprVisitor<This,Env,T,Ret> v) { return this.<Ret>accept(v); }
      |}
    """.stripMargin

  val NewExprSrc =
    """class NewExpr<This,Env,Fields,Methods,Super> extends Expr<This,Env,Pair<Fields,Methods>> {
      |  Class<Fields,Methods,Super> _class;
      |  Exprs<This,Env,Fields> fields;
      |
      |  <Ret : * -> *> Ret<Pair<Fields,Methods>> accept(ExprVisitor<This,Env,Pair<Fields,Methods>,Ret> v) {
      |    return v.<Fields,Methods,Super>_new(
      |      new Refl<Pair<Fields,Methods>>(),
      |      this._class,
      |      this.fields
      |    );
      |  }
      |}
    """.stripMargin

  val CallExprSrc =
    """class CallExpr<This,Env,Fields,Methods,Super,Args,T> extends Expr<This,Env,T> {
      |  Expr<This,Env,Pair<Fields,Methods>> e;
      |  Index<Methods,BoundExpr<Args,T>> method;
      |  Exprs<This,Env,Args> args;
      |  <Ret : * -> *> Ret<T> accept(ExprVisitor<This,Env,T,Ret> v) {
      |    return v.<Fields,Methods,Super,Args>call(this.e,this.method,this.args);
      |  }
      |}
    """.stripMargin


  val ExprVisitorSrc =
    """class ExprVisitor<This,Env,T,Ret : * -> *> {
      |  <Env1> Ret<T> var(Sub<Env,Env1> subEnv, Index<Env1,T> idx) {
      |    return this.<Env1>var(subEnv,idx);
      |  }
      |  Ret<T> _this(Sub<This,T> sub) { return this._this(sub); }
      |
      |  <Fields,Methods,Super>
      |  Ret<T>
      |  field(Expr<This,Env,Pair<Fields,Methods>> e,
      |        Index<Fields, T> fld) {
      |    return this.<Fields,Methods,Super>field(e,fld);
      |  }
      |
      |  <Fields,Methods,Super,As>
      |  Ret<T>
      |  call(Expr<This,Env,Pair<Fields,Methods>> e,
      |       Index<Methods,BoundExpr<As,T>> method,
      |       Exprs<This,Env,As> as) {
      |    return this.<Fields,Methods,Super,As>call(e,method,as);
      |  }
      |
      |  <Fields,Methods,Super>
      |  Ret<T>
      |  _new(Eq<T,Pair<Fields,Methods>> eq,
      |       Class<Fields,Methods,Super> _class,
      |       Exprs<This,Env,Fields> fields) {
      |    return this.<Fields,Methods,Super>_new(eq,_class,fields);
      |  }
      |
      |  <Fields,Methods>
      |  Ret<T>
      |  upcast(Expr<This,Env,Pair<Fields,Methods>> e) {
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
      |  Lazy<This> _this;
      |  Expr<This,Env,T> e;
      |  <Ret> Ret accept(BoundExprVisitor<Env,T,Ret> v) {
      |    return v.<This>boundExpr(this._this.force(),this.e);
      |  }
      |}
    """.stripMargin
  val ExprBinderSrc =
    """class ExprBinder<This,Env,T> extends Fun<Lazy<This>,BoundExpr<Env,T>> {
      |  Expr<This,Env,T> e;
      |  BoundExpr<Env,T> apply(Lazy<This> _this) {
      |    return new SomeBoundExpr<This,Env,T>(_this, this.e);
      |  }
      |}
    """.stripMargin

}
