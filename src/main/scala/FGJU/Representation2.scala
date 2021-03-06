package FGJU
import FGJU.Representation

// TODO next version: use Class<Id,Fields,Methods,Super> as the type indices for
// Expr and Val. Fill out EvalExprVal and EvalExprsVals
// Actually, won't quite work: we will run into the problem that Pair is not
// known by the typechecker to be injective. Given Pair<T1,T2> = Pair<S1,S2>, we
// can't derive that T1=S1 and T2=S2. This problem will arise if we try to use
// an index for Pair<T1,T2> to lookup an Exprs<Pair<T1,T2>>.
// The solution is to make Indices polymorphic: see PolyIndex
// This in turn requires we make Fields have kind (* -> *) -> *


object Representation2 {
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
      |  new CallExpr<TOP,Nil,BFields,BMethods,TyB_foo,Nil,A>(
      |    bExpr,
      |    B_foo_idx,
      |    new NoInstantiation<TyB_foo>(),
      |    new NilExprs<TOP,Nil>()
      |  )
      |in
      |aExpr
    """.stripMargin


  /*  class A{}
      class B{
        <A> A id(A a) { return a; }
      }
      new B().<A>id(new A())
  */
  val Example3 =
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
      |letType TyB_id  : * =
      |  <T> BoundExpr<Pair<T,Nil>,T>
      |in
      |letType BMethods : * = Pair<TyB_id,Nil> in
      |letType B : * = Pair<Nil,BMethods> in
      |let B_foo : Fun<Lazy<B>,TyB_id> =
      |  new TPolyExprBinder<B,+*,\A.Pair<A,Nil>,\A.A,A>(
      |    /\A.
      |    new VarExpr<B,Pair<A,Nil>,A>(
      |      new IndexZ<A,Nil>()
      |    )
      |  )
      |in
      |let bFields : BFields = new Nil() in
      |let bMethods : Fun<Lazy<B>,BMethods> =
      |  new BindMethodsCons<B,TyB_id,Nil>(
      |    B_foo,
      |    new BindMethodsNil<B>()
      |  )
      |in
      |let bUpcast : Sub<B,TOP> =
      |  new SubPairDepth<BFields,BMethods,Nil,Nil>(
      |    new SubRefl<Nil>(),
      |    new SubPairWidth<TyB_id,Nil>()
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
      |let B_id_idx : Index<BMethods,TyB_id> =
      |  new IndexZ<TyB_id,Nil>()
      |in
      |let newAExpr : Expr<TOP,Nil,A> =
      |  new NewExpr<TOP,Nil,AFields,AMethods,ASuper>(
      |    AClass,
      |    new NilExprs<TOP,Nil>()
      |  )
      |in
      |let callExpr : Expr<TOP,Nil,A> =
      |  new CallExpr<TOP,Nil,BFields,BMethods,TyB_id,Pair<A,Nil>,A>(
      |    bExpr,
      |    B_id_idx,
      |    new TypeInstantiation<+*,\T.BoundExpr<Pair<T,Nil>,T>, A>(),
      |    new ConsExprs<TOP,Nil,A,Nil>(
      |      newAExpr,
      |      new NilExprs<TOP,Nil>()
      |    )
      |  )
      |in
      |callExpr
    """.stripMargin

  // TODO example involving upcasting a polymorphic method

  // Challenge: (mutual) recursion in classes. any class can refer to any other class.
  // unlike C, there is no ordering requirement. We need a class table! But the type system is not
  // powerful enough.

  /*

  Looks like we need a kind-polymorphic mu operator:

  Mu : \/X. ((X -> *) -> (X -> *)) -> X -> *

  A = (B -> B)
  B = (A -> A)

  A = \A. \B. B -> B
  B = \A. \B. A -> A

  K2 = (* -> * -> *)
  AB = (\AB:(* -> * -> *) -> *. \f : * -> * -> *. f (A (fst AB) (snd AB)) (B (fst AB) (snd AB)))

  A = Mu<+K2,AB,fst>
  B = Mu<+K2,AB,snd>

   */

  val MuSrc =
    """class Mu<+X,F:((X -> *) -> X -> *),A:X> {
      |  F<λB:X.Mu<+X,F,B>,A> unfold;
      |}
    """.stripMargin

  /* class A { B m(B b) { return b; } }
     class B { A m(A a) { return a; } }
   */
  val Example4 =
    """letType TOP : * = Pair<Nil,Nil> in
      |let TOPClass : Class<Nil,Nil,TOP> =
      |  new Class<Nil,Nil,TOP> (
      |    new BindMethodsNil<TOP>(),
      |    new SubRefl<Pair<Nil,Nil>>()
      |  )
      |in
      |letKind K2 = * -> * -> * in
      |letType getA : K2 = \A:*. \B:*. A in
      |letType getB : K2 = \A:*. \B:*. B in
      |letType _AMethodSigs : * -> * -> * =
      |  \A:*. \B:*.
      |  Pair<BoundExpr<Pair<B,Nil>,B>,Nil>
      |in
      |letType _A : * -> * -> * =
      |  \A:*. \B:*.
      |  Pair<Nil,_AMethodSigs<A,B>>
      |in
      |letType _BMethodSigs : * -> * -> * =
      |  \A:*. \B:*.
      |  Pair<BoundExpr<Pair<A,Nil>,A>,Nil>
      |in
      |letType _B : * -> * -> * =
      |  \A:*. \B:*.
      |  Pair<Nil,_BMethodSigs<A,B>>
      |in
      |letType Classes : (K2 -> *) -> K2 -> * =
      |  \Classes:K2 -> *. \get:K2.
      |  get<_A<Classes<getA>, Classes<getB>>,
      |      _B<Classes<getA>, Classes<getB>>>
      |in
      |letType A : * = Mu<+K2,Classes,getA> in
      |letType B : * = Mu<+K2,Classes,getB> in
      |letType AMethodSigs : * = _AMethodSigs<A,B> in
      |letType BMethodSigs : * = _BMethodSigs<A,B> in
      |let Aunfold : _A<A,B> =
      |  new Pair<Nil,AMethodSigs>(
      |    new Nil(),
      |    new Pair<BoundExpr<Pair<B,Nil>,B>,Nil>(
      |      new SomeBoundExpr<Nil,Pair<B,Nil>,B>(
      |        new Delay<Nil>(new Nil()),
      |        new VarExpr<Nil,Pair<B,Nil>,B>(
      |          new IndexZ<B,Nil>()
      |        )
      |      ),
      |      new Nil()
      |    )
      |  )
      |in
      |let a : A = new Mu<+K2,Classes,getA>(Aunfold) in
      |let Bunfold : _B<A,B> =
      |  new Pair<Nil,BMethodSigs>(
      |    new Nil(),
      |    new Pair<BoundExpr<Pair<A,Nil>,A>,Nil>(
      |      new SomeBoundExpr<Nil,Pair<A,Nil>,A>(
      |        new Delay<Nil>(new Nil()),
      |        new VarExpr<Nil,Pair<A,Nil>,A>(
      |          new IndexZ<A,Nil>()
      |        )
      |      ),
      |      new Nil()
      |    )
      |  )
      |in
      |let b : B = new Mu<+K2,Classes,getB>(Bunfold) in
      |letType AunfoldTy : * = Pair<Nil,AMethodSigs> in
      |
      |let Amethod : Expr<A,Pair<B,Nil>,B> =
      |  new VarExpr<A,Pair<B,Nil>,B>(
      |    new IndexZ<B,Nil>()
      |  )
      |in
      |let Aclass : MuClass<+K2,Classes,getA,Nil,AMethodSigs,TOP> =
      |  new MuClass<+K2,Classes,getA,Nil,AMethodSigs,TOP>(
      |    new Refl<AunfoldTy>(),
      |    new BindMethodsCons<A,BoundExpr<Pair<B,Nil>,B>,Nil>(
      |      new ExprBinder<A,Pair<B,Nil>,B>(Amethod),
      |      new BindMethodsNil<A>()
      |    ),
      |    new SubTop<A>()
      |  )
      |in
      |a
    """.stripMargin

  /*
    A version of Example1 with Mu

    class A{}
    class B{ A foo() { return new A(); }}
    new A()
*/
  val Example5 =
    """letType TOP : * = Pair<Nil,Nil> in
      |let TOPClass : Class<Nil,Nil,TOP> =
      |  new Class<Nil,Nil,TOP> (
      |    new BindMethodsNil<TOP>(),
      |    new SubRefl<Pair<Nil,Nil>>()
      |  )
      |in
      |letKind K2 = * -> * -> * in
      |letType getA : K2 = \A:*. \B:*. A in
      |letType getB : K2 = \A:*. \B:*. B in
      |letType _A : * -> * -> * =
      |  \A:*. \B:*. Pair<Nil,Nil>
      |in
      |letType _BMethodSigs : * -> * -> * =
      |  \A:*. \B:*.
      |  Pair<BoundExpr<Nil,A>,Nil>
      |in
      |letType _B : * -> * -> * =
      |  \A:*. \B:*.
      |  Pair<Nil,_BMethodSigs<A,B>>
      |in
      |letType Classes : (K2 -> *) -> K2 -> * =
      |  \Classes:K2 -> *. \get:K2.
      |  get<_A<Classes<getA>, Classes<getB>>,
      |      _B<Classes<getA>, Classes<getB>>>
      |in
      |letType A : * = Mu<+K2,Classes,getA> in
      |letType AFields : * = Nil in
      |letType AMethods : * = Nil in
      |letType B : * = Mu<+K2,Classes,getB> in
      |letType BMethodSigs : * = _BMethodSigs<A,B> in
      |let AClass : MuClass<+K2,Classes,getA,Nil,Nil,TOP> =
      |  new MuClass<+K2,Classes,getA,Nil,Nil,TOP> (
      |    new Refl<Pair<AFields,AMethods>>(),
      |    new BindMethodsNil<A>(),
      |    new SubTop<A>()
      |  )
      |in
      |letType BFields : * = Nil in
      |letType B_foo_args : * = Nil in
      |letType B_foo_sig  : * = BoundExpr<B_foo_args,A> in
      |letType BMethods : * = BMethodSigs in
      |let B_foo_binder : Fun<Lazy<B>,B_foo_sig> =
      |  new ExprBinder<B,Nil,A>(
      |    new MuNewExpr<+K2,Classes,getA,B,Nil,AFields,AMethods,TOP>(
      |      new Refl<Pair<AFields,AMethods>>(),
      |      AClass,
      |      new NilExprs<B,B_foo_args>()
      |    )
      |  )
      |in
      |let bFields : BFields = new Nil() in
      |let B_method_binders : Fun<Lazy<B>,BMethods> =
      |  new BindMethodsCons<B,B_foo_sig,Nil>(
      |    B_foo_binder,
      |    new BindMethodsNil<B>()
      |  )
      |in
      |letType BUnfoldType : * = Pair<BFields,BMethods> in
      |let subB : Sub<B,TOP> =
      |  new SubTop<B>()
      |in
      |let BClass : MuClass<+K2,Classes,getB,BFields,BMethods,TOP> =
      |  new MuClass<+K2,Classes,getB,BFields,BMethods,TOP>(
      |    new Refl<Pair<BFields,BMethods>>(),
      |    B_method_binders,
      |    subB
      |  )
      |in
      |let b : Expr<TOP,Nil,B> =
      |  new MuNewExpr<+K2,Classes,getB,TOP,Nil,BFields,BMethods,TOP>(
      |    new Refl<Pair<BFields,BMethods>>(),
      |    BClass,
      |    new NilExprs<TOP,Nil>()
      |  )
      |in
      |let B_foo_idx : Index<BMethods,B_foo_sig> =
      |  new IndexZ<B_foo_sig,Nil>()
      |in
      |let a : Expr<TOP,Nil,A> =
      |  new MuCallExpr<+K2,Classes,getB,BFields,BMethods,B_foo_sig,Nil,TOP,Nil,A>(
      |    b,
      |    new Refl<Pair<BFields,BMethods>>(),
      |    B_foo_idx,
      |    new NoInstantiation<B_foo_sig>(),
      |    new NilExprs<TOP,Nil>()
      |  )
      |in
      |a
    """.stripMargin

  /*
  Now let's make sure we can handle generic classes too.

  class A{}
  class B<T>{ T foo(T x) { return x; }}
  new B<T>().foo(new A())

*/
  val Example6 =
    """letType TOP : * = Pair<Nil,Nil> in
      |let TOPClass : Class<Nil,Nil,TOP> =
      |  new Class<Nil,Nil,TOP> (
      |    new BindMethodsNil<TOP>(),
      |    new SubRefl<Pair<Nil,Nil>>()
      |  )
      |in
      |letKind KClasses = * -> (* -> *) -> * in
      |letType getA : KClasses = \A:*. \B:(* -> *). A in
      |letType getB : * -> KClasses = \T:*. \A:*. \B:(* -> *). B<T> in
      |letType _A : * -> (* -> *) -> * =
      |  \A:*. \B:* -> *. Pair<Nil,Nil>
      |in
      |letType _BMethodSigs : * -> (* -> *) -> * -> * =
      |  \A:*. \B:* -> *. \T:*.
      |  Pair<BoundExpr<Pair<T,Nil>,T>,Nil>
      |in
      |letType _B : * -> (* -> *) -> * -> * =
      |  \A:*. \B:* -> *. \T:*.
      |  Pair<Nil,_BMethodSigs<A,B,T>>
      |in
      |letType Classes : (KClasses -> *) -> KClasses -> * =
      |  \Classes:KClasses -> *. \get:KClasses.
      |  get<_A<Classes<getA>, \T:*. Classes<getB<T>>>,
      |      _B<Classes<getA>, \T:*. Classes<getB<T>>>>
      |in
      |letType A : * = Mu<+KClasses,Classes,getA> in
      |letType AFields : * = Nil in
      |letType AMethods : * = Nil in
      |letType B : * -> * = \T:*. Mu<+KClasses,Classes,getB<T>> in
      |letType BMethodSigs : * -> * = \T:*. _BMethodSigs<A,B,T> in
      |let AClass : MuClass<+KClasses,Classes,getA,Nil,Nil,TOP> =
      |  new MuClass<+KClasses,Classes,getA,Nil,Nil,TOP> (
      |    new Refl<Pair<AFields,AMethods>>(),
      |    new BindMethodsNil<A>(),
      |    new SubTop<A>()
      |  )
      |in
      |letType BFields : * = Nil in
      |letType B_foo_args : * -> * = \T:*. Pair<T,Nil> in
      |letType B_foo_sig  : * -> * = \T:*. BoundExpr<B_foo_args<T>,T> in
      |letType BMethods   : * -> * = \T:*. BMethodSigs<T> in
      |let B_foo_binder   : <T:*> Fun<Lazy<B<T>>,B_foo_sig<T>> =
      |  /\T:*.
      |  new ExprBinder<B<T>,Pair<T,Nil>,T>(
      |    new VarExpr<B<T>, Pair<T,Nil>, T> (
      |      new IndexZ<T,Nil>()
      |    )
      |  )
      |in
      |let bFields : BFields = new Nil() in
      |let B_method_binders : <T:*> Fun<Lazy<B<T>>,BMethods<T>> =
      |  /\T:*.
      |  new BindMethodsCons<B<T>,B_foo_sig<T>,Nil>(
      |    B_foo_binder<T>,
      |    new BindMethodsNil<B<T>>()
      |  )
      |in
      |letType BUnfoldType : * = <T:*> Pair<BFields,BMethods<T>> in
      |let subB : <T:*> Sub<B<T>,TOP> =
      |  /\T.
      |  new SubTop<B<T>>()
      |in
      |let BClass : <T> MuClass<+KClasses,Classes,getB<T>,BFields,BMethods<T>,TOP> =
      |  /\T.
      |  new MuClass<+KClasses,Classes,getB<T>,BFields,BMethods<T>,TOP>(
      |    new Refl<Pair<BFields,BMethods<T>>>(),
      |    B_method_binders<T>,
      |    subB<T>
      |  )
      |in
      |let b : Expr<TOP,Nil,B<A>> =
      |  new MuNewExpr<+KClasses,Classes,getB<A>,TOP,Nil,BFields,BMethods<A>,TOP>(
      |    new Refl<Pair<BFields,BMethods<A>>>(),
      |    BClass<A>,
      |    new NilExprs<TOP,Nil>()
      |  )
      |in
      |let B_foo_idx : <T> Index<BMethods<T>,B_foo_sig<T>> =
      |  /\T.
      |  new IndexZ<B_foo_sig<T>,Nil>()
      |in
      |let aExpr : Expr<TOP,Nil,A> =
      |  new MuNewExpr<+KClasses,Classes,getA,TOP,Nil,AFields,AMethods,TOP>(
      |    new Refl<Pair<AFields,AMethods>>(),
      |    AClass,
      |    new NilExprs<TOP,Nil>()
      |  )
      |in
      |let callExpr : Expr<TOP,Nil,A> =
      |  new MuCallExpr<+KClasses,Classes,getB<A>,BFields,BMethods<A>,B_foo_sig<A>,B_foo_args<A>,TOP,Nil,A>(
      |    b,
      |    new Refl<Pair<BFields,BMethods<A>>>(),
      |    B_foo_idx<A>,
      |    new NoInstantiation<B_foo_sig<A>>(),
      |    new ConsExprs<TOP,Nil,A,Nil>(
      |      aExpr, new NilExprs<TOP,Nil>()
      |    )
      |  )
      |in
      |callExpr
    """.stripMargin

  // New class for Mu
  val MuClassSrc =
    """class MuClass<+N,Classes : (N -> *) -> N -> * ,i:N,
      |              Fields,Methods,Super> {
      |  Eq<Classes<Mu<+N,Classes>,i>,Pair<Fields,Methods>> eq;
      |  Fun<Lazy<Mu<+N,Classes,i>>, Methods> methods;
      |  Sub<Mu<+N,Classes,i>, Super> sub;
      |}
    """.stripMargin

  val SubMuSrc =
    """class SubMu<+N,Classes:(N -> *) -> N -> *, subI:N, supI:N>
      |  extends Sub<Mu<+N,Classes,subI>, Mu<+N,Classes,supI>> {
      |  Sub<Classes<Mu<+N,Classes>,subI>, Classes<Mu<+N,Classes>,supI>> subUnfold;
      |}
    """.stripMargin
  /*
  val OSrc =
    """class O<I:* -> *> {
      |  <Ret> Ret accept(OVisitor v) {
      |    return this.<Ret>accept(v);
      |  }
      |}
    """.stripMargin

  val PackOSrc =
    """class PackO<I:* -> *,J:* -> *> {
      |  O<I> sub;
      |  I<O<I>>
      |}
    """.stripMargin

  val OSrc =
    """class O<FI:* -> *, MI:* -> *> {
      |  <Ret> Ret accept(OVisitor v) {
      |    return this.<Ret>accept(v);
      |  }
      |}
    """.stripMargin

  val PackOSrc =
    """class PackO<T,FI:* -> *, MI:* -> *> extends O<FI,MI> {
      |  Sub<T,Obj<FI,MI>> sub;
      |  FI<Obj<FI,MI>> fields;
      |  Fun<T, MI<Obj<FI,MI>>> methods;
      |
      |  <Ret> Ret accept(OVisitor v) {
      |    return v.openO(sub,fields,methods);
      |  }
      |}
    """.stripMargin
    */

  // how should we represent instantiations of generic methods?
  // this version is deep: it allows us to inspect each instantiation.
  // so we can do this if we need to, but it seems to add little value.
  val GenericMethodInstantiationSrc =
    """class GenericMethodInstantiation<T> {
      |  <R> R visit(GenericMethodInstantiationVisitor<T,R> v) {
      |    return this.<R>visit(v);
      |  }
      |}
    """.stripMargin

  val GenericMethodInstantiationVisitorSrc =
    """class GenericMethodInstantiationVisitor<T,R> {
      |  <+K,M:K -> *,A:K>
      |  R instType(Eq<T,M<A>> eq,
      |             GenericMethodInstantiation<<A:K>M<A>> m) {
      |    return this.<+K,M,A>instType(eq,m);
      |  }
      |
      |  <M:<K>*, +K>
      |  R instKind(Eq<T, M<+K>> eq,
      |             GenericMethodInstantiation<<+K>M<K>> m) {
      |    return this.<M,+K>instKind(eq,m);
      |  }
      |
      |  R genericType(T t) { return this.genericType(t); }
      |}
    """.stripMargin

  // here's a shallow representation of generic method instantiation.
  val InstantiationSrc =
    """class Instantiation<P,I> {
      |  I instantiate(P p) {
      |    return this.instantiate(p);
      |  }
      |}
    """.stripMargin

  val NoInstantiationSrc =
    """class NoInstantiation<T> extends Instantiation<T,T> {
      |  T instantiation(T p) { return p; }
      |}
    """.stripMargin

  val TypeInstantiationSrc =
    """class TypeInstantiation<+K, T:K->*, A:K> extends Instantiation<<X:K>T<X>, T<A>> {
      |  T<A> instantiate(<X:K>T<X> p) { return p<A>; }
      |}
    """.stripMargin

  val KindInstantiationSrc =
    """class KindInstantiation<T:<X>*,+K> extends Instantiation<<+X>T<+X>,T<+K>> {
      |  T<+K> instantiate(<+X>T<+X> p) { return p<+K>; }
      |}
    """.stripMargin

  val ClassSrc =
    """class Class<Fields,Methods,Super> {
      |  Fun<Lazy<Pair<Fields,Methods>>, Methods> methods;
      |  Sub<Pair<Fields,Methods>, Super> sub;
      |}
    """.stripMargin

  val LazySrc =
    """class Lazy<T> {
      |  T force() {
      |    return this.force();
      |  }
      |}
    """.stripMargin

  val DelaySrc =
    """class Delay<T> extends Lazy<T> {
      |  T t;
      |  T force() {
      |    return this.t;
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

  val ObjSrc =
    """class Obj<Fields,Methods,Super> {
      |  <SubFields,SubMethods,SubSuper,R>
      |  R accept(ObjVisitor<Fields,Methods,Super,
      |                      SubFields,SubMethods,SubSuper,
      |                      R> v) {
      |    return this.<SubFields,SubMethods,SubSuper,R>accept(v);
      |  }
      |}
    """.stripMargin

  val ObjVisitorSrc =
    """class ObjVisitor<Fields,Methods,Super,
      |                 SubFields,SubMethods,SubSuper, R> {
      |  R visitObj(Class<SubFields,SubMethods,SubSuper> subClass,
      |             Class<Fields,Methods,Super> _class,
      |             ObjCast<SubFields,SubMethods,SubSuper,
      |                     Fields,Methods,Super> cast,
      |             SubFields subFields) {
      |    return this.visitObj(subClass, _class, cast, subFields);
      |  }
      |}
    """.stripMargin

  // Subtype witnesses for quantified types
  val SubForallTySrc =
    """class SubForallTy<+K, SubT:K -> *, SupT:K -> *>
      |  extends Sub<<A:K>SubT<A>, <A:K>SupT<A>> {
      |
      |  <A:K> Sub<SubT<A>, SupT<A>> sub;
      |
      |  (<A:K>SupT<A>) upcast(<A:K>SubT<A> x) {
      |    return
      |      /\A:K.
      |      this.sub<A>.upcast(x<A>);
      |  }
      |}
    """.stripMargin

  val SubForallKSrc =
    """class SubForallK<SubT:<X>*, SupT:<X>*>
      |  extends Sub<<+X>SubT<+X>, <+X>SupT<+X>> {
      |
      |  <+X> Sub<SubT<+X>, SupT<+X>> sub;
      |
      |  (<+X>SupT<+X>) upcast(<+X>SubT<+X> x) {
      |    return
      |      /\+X.
      |      this.sub<+X>.upcast(x<+X>);
      |  }
      |}
    """.stripMargin

  val SubTopSrc =
    """class SubTop<T> extends Sub<T, Pair<Nil,Nil>> {
      |  Pair<Nil,Nil> upcast(T t) { return new Pair<Nil,Nil>(new Nil(), new Nil()); }
      |}
    """.stripMargin


  val PolyIndexSrc =
    "class PolyIndex<F:* -> *, Tup : (* -> *) -> *, T> extends Fun<Tup<F>, F<T>> {}"
  val PolyIndexZSrc =
    """class PolyIndexZ<F:* -> *,Hd,Tl : (* -> *) -> *> extends PolyIndex<F, \F:* -> *. Pair<F<Hd>,Tl<F>>, Hd> {
      |  F<Hd> apply(Pair<F<Hd>, Tl<F>> p) { return p.fst; }
      |}
    """.stripMargin
  val PolyIndexSSrc =
    """class PolyIndexS<F:* -> *,Hd,Tl : (* -> *) -> *,T>
      |  extends PolyIndex<F, \F:* -> *. Pair<F<Hd>,Tl<F>>, T> {
      |
      |  PolyIndex<F,Tl,T> idx;
      |
      |  F<T> apply(Pair<F<Hd>, Tl<F>> p) { return this.idx.apply(p.snd); }
      |}
    """.stripMargin

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
      |  <R> R accept(ExprsVisitor<This,Env,Ts,R> v) {
      |    return this.<R>accept(v);
      |  }
      |}
    """.stripMargin

  val ExprsVisitorSrc =
    """class ExprsVisitor<This,Env,Ts,R> {
      |  R nilExprs(Eq<Ts,Nil> eq) {
      |    return this.nilExprs(eq);
      |  }
      |
      |  <Hd,Tl> R consExprs(Eq<Ts,Pair<Hd,Tl>> eq,
      |                      Expr<This,Env,Hd> hd,
      |                      Exprs<This,Env,Tl> tl) {
      |    return this.<Hd,Tl>consExprs(eq,hd,tl);
      |  }
      |}
    """.stripMargin

  val NilExprsSrc =
    """class NilExprs<This,Env> extends Exprs<This,Env,Nil> {
      |  <R> R accept(ExprsVisitor<This,Env,Nil,R> v) {
      |    return v.nilExprs(new Refl<Nil>());
      |  }
      |}
    """.stripMargin

  val ConsExprsSrc =
    """class ConsExprs<This,Env,Hd,Tl>
      |  extends Exprs<This,Env,Pair<Hd,Tl>> {
      |
      |  Expr<This,Env,Hd> hd;
      |  Exprs<This,Env,Tl> tl;
      |
      |  <R> R accept(ExprsVisitor<This,Env,Pair<Hd,Tl>,R> v) {
      |    return v.<Hd,Tl>consExprs(
      |      new Refl<Pair<Hd,Tl>>(),
      |      this.hd, this.tl
      |    );
      |  }
      |}
    """.stripMargin

  val ExprSrc =
    """class Expr<This,Env,T> {
      |  <Ret> Ret accept(ExprVisitor<This,Env,T,Ret> v) { return this.<Ret>accept(v); }
      |}
    """.stripMargin

  val VarExprSrc =
    """class VarExpr<This,Env,T> extends Expr<This,Env,T> {
      |  Index<Env,T> idx;
      |  <Ret> Ret accept(ExprVisitor<This,Env,T,Ret> v) {
      |    return v.var(this.idx);
      |  }
      |}
    """.stripMargin

  val NewExprSrc =
    """class NewExpr<This,Env,Fields,Methods,Super> extends Expr<This,Env,Pair<Fields,Methods>> {
      |  Class<Fields,Methods,Super> _class;
      |  Exprs<This,Env,Fields> fields;
      |
      |  <Ret> Ret accept(ExprVisitor<This,Env,Pair<Fields,Methods>,Ret> v) {
      |    return v.<Fields,Methods,Super>_new(
      |      new Refl<Pair<Fields,Methods>>(),
      |      this._class,
      |      this.fields
      |    );
      |  }
      |}
    """.stripMargin

  val MuNewExprSrc =
    """class MuNewExpr<+N,Classes:(N->*)->N->*,i:N,
      |                This,Env,Fields,Methods,Super> extends Expr<This,Env,Mu<+N,Classes,i>> {
      |  Eq<Classes<Mu<+N,Classes>,i>,Pair<Fields,Methods>> eqUnfold;
      |  MuClass<+N,Classes,i,Fields,Methods,Super> _class;
      |  Exprs<This,Env,Fields> fields;
      |
      |  <Ret> Ret accept(ExprVisitor<This,Env,Mu<+N,Classes,i>,Ret> v) {
      |    return v.<+N,Classes,i,Fields,Methods,Super>muNew(
      |      new Refl<Mu<+N,Classes,i>>(),
      |      this.eqUnfold,
      |      this._class,
      |      this.fields
      |    );
      |  }
      |}
    """.stripMargin

  val CallExprSrc =
    """class CallExpr<This,Env,Fields,Methods,M,Args,T> extends Expr<This,Env,T> {
      |  Expr<This,Env,Pair<Fields,Methods>> e;
      |  Index<Methods,M> method;
      |  Instantiation<M,BoundExpr<Args,T>> inst;
      |  Exprs<This,Env,Args> args;
      |  <Ret> Ret accept(ExprVisitor<This,Env,T,Ret> v) {
      |    return v.<Fields,Methods,M,Args>call(this.e,this.method,this.inst,this.args);
      |  }
      |}
    """.stripMargin

  val MuCallExprSrc =
    """class MuCallExpr<+N,Classes:(N->*)->N->*,i:N,Fields,Methods,M,Args,This,Env,T>
      |  extends Expr<This,Env,T> {
      |  Expr<This,Env,Mu<+N,Classes,i>> e;
      |  Eq<Classes<Mu<+N,Classes>,i>, Pair<Fields,Methods>> eqUnfold;
      |  Index<Methods,M> method;
      |  Instantiation<M,BoundExpr<Args,T>> inst;
      |  Exprs<This,Env,Args> args;
      |  <Ret> Ret accept(ExprVisitor<This,Env,T,Ret> v) {
      |    return v.<+N,Classes,i,Fields,Methods,M,Args>muCall(
      |      this.e, this.eqUnfold, this.method, this.inst, this.args
      |    );
      |  }
      |}
    """.stripMargin



  // TODO generalize cast. subtype is not always a class, since we
  // have subtyping rules for quantified types too. So we should
  // allow casting based on an arbitrary Sub<Subtype,Supertype> witness.

  val ExprVisitorSrc =
    """class ExprVisitor<This,Env,T,Ret> {
      |  Ret var(Index<Env,T> idx) {
      |    return this.var(idx);
      |  }
      |  Ret _this(Sub<This,T> sub) { return this._this(sub); }
      |
      |  <Fields,Methods>
      |  Ret
      |  field(Expr<This,Env,Pair<Fields,Methods>> e,
      |        Index<Fields, T> fld) {
      |    return this.<Fields,Methods>field(e,fld);
      |  }
      |
      |  <+N,Classes:(N->*)->N->*,i:N,Fields,Methods>
      |  Ret
      |  muField(Expr<This,Env,Mu<+N,Classes,i>> e,
      |          Eq<Classes<Mu<+N,Classes>,i>, Pair<Fields,Methods>> eqUnfold,
      |          Index<Fields,T> idx) {
      |    return this.<+N,Classes,i,Fields,Methods>muField(e,eqUnfold,idx);
      |  }
      |
      |  <Fields,Methods,M,As>
      |  Ret
      |  call(Expr<This,Env,Pair<Fields,Methods>> e,
      |       Index<Methods,M> method,
      |       Instantiation<M,BoundExpr<As,T>> inst,
      |       Exprs<This,Env,As> as) {
      |    return this.<Fields,Methods,M,As>call(e,method,inst,as);
      |  }
      |
      |  <+N,Classes:(N->*)->N->*,i:N,Fields,Methods,M,Args>
      |  Ret
      |  muCall(Expr<This,Env,Mu<+N,Classes,i>> e,
      |         Eq<Classes<Mu<+N,Classes>,i>, Pair<Fields,Methods>> eqUnfold,
      |         Index<Methods,M> method,
      |         Instantiation<M,BoundExpr<Args,T>> inst,
      |         Exprs<This,Env,Args> args) {
      |    return this.<+N,Classes,i,Fields,Methods,M,Args>muCall(e,eqUnfold,method,inst,args);
      |  }
      |
      |  <Fields,Methods,Super>
      |  Ret
      |  _new(Eq<T,Pair<Fields,Methods>> eq,
      |       Class<Fields,Methods,Super> _class,
      |       Exprs<This,Env,Fields> fields) {
      |    return this.<Fields,Methods,Super>_new(eq,_class,fields);
      |  }
      |
      |  <+N,Classes:(N->*)->N->*,i:N,Fields,Methods,Super>
      |  Ret
      |  muNew(Eq<T,Mu<+N,Classes,i>> eq,
      |        Eq<Classes<Mu<+N,Classes>,i>,Pair<Fields,Methods>> eqUnfold,
      |        MuClass<+N,Classes,i,Fields,Methods,Super> _class,
      |        Exprs<This,Env,Fields> fields) {
      |    return this.<+N,Classes,i,Fields,Methods,Super>muNew(eq,eqUnfold,_class,fields);
      |  }
      |
      |  <Fields,Methods,Super>
      |  Ret
      |  upcast(Eq<T,Super> eq,
      |         Class<Fields,Methods,Super> _class,
      |         Expr<This,Env,Pair<Fields,Methods>> e) {
      |    return this.<Fields,Methods,Super>upcast(eq,_class,e);
      |  }
      |
      |  <+X, F : X -> *>
      |  Ret
      |  tAbs(Eq<T, <A:X> F<A>> eq, <A:X> Expr<This,Env,F<A>> e) {
      |    return this.<+X,F>tAbs(eq,e);
      |  }
      |
      |  <+X, F : X -> *, A:X>
      |  Ret
      |  tApp(Eq<T, F<A>> eq, Expr<This,Env,<B:X>F<B>> e) {
      |    return this.<+X,F,A>tApp(eq,e);
      |  }
      |
      |  <F : <K>*>
      |  Ret
      |  kAbs(Eq<T, <+K>F<+K>> eq, <+K> Expr<This,Env,F<+K>> e) {
      |    return this.<F>kAbs(eq,e);
      |  }
      |
      |  <F : <K>*, +K>
      |  Ret
      |  kApp(Eq<T, F<+K>> eq, Expr<This,Env,<+K>F<+K>> e) {
      |    return this.<F,+K>kApp(eq,e);
      |  }
      |}
    """.stripMargin

  val CastSrc =
    """class Cast<Sub,Sup> {
      |  <R> R accept(CastVisitor<Sub,Sup,R> v) {
      |    return this.<R>accept(v);
      |  }
      |}
    """.stripMargin

  val CastVisitorSrc =
    """class CastVisitor<Sub,Sup,R> {
      |  <Fields,Methods>
      |  R cast(Eq<Sub,Pair<Fields,Methods>> eq,
      |         Class<Fields,Methods,Sup> _class) {
      |    return this.<Fields,Methods>cast(eq,_class);
      |  }
      |
      |  <Fields,Methods,Parent>
      |  R casts(Eq<Sub,Pair<Fields,Methods>> eq,
      |          Class<Fields,Methods,Parent> _class,
      |          Cast<Parent,Sup> cast) {
      |    return this.<Fields,Methods,Parent>casts(eq,_class,cast);
      |  }
      |}
    """.stripMargin

  val EvalCastSrc =
    """class EvalCast<S,T> extends CastVisitor<S,T,Sub<S,T>> {
      |  <Fields,Methods>
      |  Sub<S,T> cast(Eq<S,Pair<Fields,Methods>> eq,
      |                Class<Fields,Methods,T> _class) {
      |    return eq.<\X.Sub<X,T>>toLeft(_class.sub);
      |  }
      |
      |  <Fields,Methods,Parent>
      |  Sub<S,T> casts(Eq<S,Pair<Fields,Methods>> eq,
      |                 Class<Fields,Methods,Parent> _class,
      |                 Cast<Parent,T> cast) {
      |    return new SubTrans<S,Parent,T>(
      |      eq.<\X.Sub<X,Parent>>toLeft(_class.sub),
      |      cast.<Sub<Parent,T>>accept(
      |        new EvalCast<Parent,T>()
      |      )
      |    );
      |  }
      |}
    """.stripMargin

  val ObjCastSrc =
    """class ObjCast<SubFs,SubMs,SubS,SupFs,SupMs,SupS> {
      |  <R> R accept(ObjCastVisitor<SubFs,SubMs,SubS,SupFs,SupMs,SupS,R> v) {
      |    return this.<R>accept(v);
      |  }
      |}
    """.stripMargin

  val ObjCastVisitorSrc =
    """class ObjCastVisitor<SubFs,SubMs,SubS,SupFs,SupMs,SupS,R> {
      |  R refl(Eq<SubFs,SupFs> eqFs,
      |         Eq<SubMs,SupMs> eqMs,
      |         Eq<SubS,SupS> eqSs) {
      |    return this.castRefl(eqFs,eqMs,eqSs);
      |  }
      |
      |  <MidFs,MidMs,MidS>
      |  R trans(Eq<SubS,Obj<MidFs,MidMs,MidS>> eq,
      |          Class<SubFs,SubMs,Obj<MidFs,MidMs,MidS>> _class,
      |          ObjCast<MidFs,MidMs,MidS,SupFs,SupMs,SupS> cast) {
      |    return this.<MidFs,MidMs,MidS>casts(eq,_class,cast);
      |  }
      |}
    """.stripMargin

  val EvalObjCastSrc =
    """class EvalObjCast<SubFs,SubMs,SubS,SupFs,SupMs,SupS>
      |  extends ObjCastVisitor<SubFs,SubMs,SubS,SupFs,SupMs,SupS,
      |          Fun<Pair<SubFs,SubMs>, Pair<SupFs,SupMs>>> {
      |  Fun<Pair<SubFs,SubMs>, Pair<SupFs,SupMs>>
      |  refl(Eq<SubFs,SupFs> eqFs,
      |       Eq<SubMs,SupMs> eqMs,
      |       Eq<SubS,SupS> eqSs) {
      |    return
      |      eqFs.<\T.Fun<Pair<SubFs,SubMs>, Pair<T,SupMs>>>toRight(
      |      eqMs.<\T.Fun<Pair<SubFs,SubMs>, Pair<SubFs,T>>>toRight(
      |        new IdFun<Pair<SubFs,SubMs>>()
      |      ));
      |  }
      |
      |  <MidFs,MidMs,MidS>
      |  Fun<Pair<SubFs,SubMs>, Pair<SupFs,SupMs>>
      |  trans(Eq<SubS,Obj<MidFs,MidMs,MidS>> eq,
      |        Class<SubFs,SubMs,Pair<MidFs,MidMs>> _class,
      |        ObjCast<MidFs,MidMs,MidS,SupFs,SupMs,SupS> cast) {
      |    return
      |      let f1 : Fun<Pair<SubFs,SubMs>, Pair<MidFs,MidMs>> =
      |        _class.sub
      |      in
      |      let f2 : Fun<Pair<MidFs,MidMs>, Pair<SupFs,SupMs>> =
      |        cast.<Fun<Pair<MidFs,MidMs>, Pair<SupFs,SupMs>>>accept(
      |          new EvalObjCast<MidFs,MidMs,MidS,SupFs,SupMs,SupS>()
      |        )
      |      in
      |      new ComposeFun<Pair<SubFs,SubMs>, Pair<MidFs,MidMs>, Pair<SupFs,SupMs>>(
      |        f1,f2
      |      );
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
      |  <This,SupEnv,SubT>
      |  Ret
      |  boundExpr(Lazy<This> _this,
      |            Expr<This,SupEnv,SubT> e,
      |            Sub<Env,SupEnv> subEnv,
      |            Sub<SubT, T> subT) {
      |    return this.<This,SupEnv,SubT>boundExpr(_this,e,subEnv,subT);
      |  }
      |}
    """.stripMargin


  val SomeBoundExprSrc =
    """class SomeBoundExpr<This,Env,T> extends BoundExpr<Env,T> {
      |  Lazy<This> _this;
      |  Expr<This,Env,T> e;
      |  <Ret> Ret accept(BoundExprVisitor<Env,T,Ret> v) {
      |    return v.<This,Env,T>boundExpr(
      |      this._this,
      |      this.e,
      |      new SubRefl<Env>(),
      |      new SubRefl<T>()
      |    );
      |  }
      |}
    """.stripMargin

  val BoundExprSubSrc =
  """class BoundExprSub<This,SupEnv,SubT,Env,T> extends BoundExpr<Env,T> {
    |  Lazy<This> _this;
    |  Expr<This,SupEnv,SubT> e;
    |  Sub<Env,SupEnv> subEnv;
    |  Sub<SubT,T> subT;
    |
    |  <Ret> Ret accept(BoundExprVisitor<Env,T,Ret> v) {
    |    return v.<This,SupEnv,SubT>boundExpr(
    |      this._this,
    |      this.e,
    |      this.subEnv,
    |      this.subT
    |    );
    |  }
    |}
  """.stripMargin


  val UpcastBoundExprSrc =
    """class UpcastBoundExpr<SubEnv,SupEnv,SubT,SupT>
      |  extends BoundExprVisitor<SupEnv, SubT, BoundExpr<SubEnv,SupT>> {
      |
      |  Sub<SubEnv,SupEnv> subEnv;
      |  Sub<SubT,SupT> subT;
      |
      |  <This,SupEnv2,SubT2>
      |  BoundExpr<SubEnv,SupT>
      |  boundExpr(Lazy<This> _this,
      |            Expr<This,SupEnv2,SubT2> e,
      |            Sub<SupEnv,SupEnv2> subEnv2,
      |            Sub<SubT2,SubT> subT2) {
      |    return new BoundExprSub<This,SupEnv2,SubT2,SubEnv,SupT>(
      |      _this, e,
      |      new SubTrans<SubEnv,SupEnv,SupEnv2>(this.subEnv,subEnv2),
      |      new SubTrans<SubT2,SubT,SupT>(subT2,this.subT)
      |    );
      |  }
      |}
    """.stripMargin

  val SubBoundExprSrc =
    """class SubBoundExpr<SubEnv,SupEnv,SubT,SupT>
      |  extends Sub<BoundExpr<SupEnv,SubT>, BoundExpr<SubEnv,SupT>> {
      |  Sub<SubEnv, SupEnv> subEnv;
      |  Sub<SubT, SupT> subT;
      |
      |  BoundExpr<SubEnv,SupT> upcast(BoundExpr<SupEnv,SubT> be) {
      |    return be.<BoundExpr<SubEnv,SupT>>accept(
      |      new UpcastBoundExpr<SubEnv,SupEnv,SubT,SupT>(this.subEnv,this.subT)
      |    );
      |  }
      |}
    """.stripMargin

  val TPolyExprBinderSrc =
    """class TPolyExprBinder<This,+K,Env:K -> *,T:K -> *,A:K>
      |  extends Fun<Lazy<This>,<A:K> BoundExpr<Env<A>,T<A>>> {
      |  <A:K> Expr<This,Env<A>,T<A>> e;
      |  (<A:K> BoundExpr<Env<A>,T<A>>) apply(Lazy<This> _this) {
      |    return /\A:K. new SomeBoundExpr<This,Env<A>,T<A>>(_this, this.e<A>);
      |  }
      |}
    """.stripMargin

  val KPolyExprBinderSrc =
    """class KPolyExprBinder<This,Env:<K>*,T:<K>*,+K>
      |  extends Fun<Lazy<This>,<+K> BoundExpr<Env<+K>,T<+K>>> {
      |  <+K> Expr<This,Env<+K>,T<+K>> e;
      |  (<+K> BoundExpr<Env<+K>,T<+K>>) apply(Lazy<This> _this) {
      |    return /\+K. new SomeBoundExpr<This,Env<+K>,T<+K>>(_this, this.e<+K>);
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


  val EvalBoundExprSrc =
    """class EvalBoundExpr<Env,T> extends BoundExprVisitor<Env,T,T> {
      |  Env env;
      |
      |  <This,SupEnv,SubT>
      |  T
      |  boundExpr(Lazy<This> _this,
      |            Expr<This,SupEnv,SubT> e,
      |            Sub<Env,SupEnv> subEnv,
      |            Sub<SubT,T> subT) {
      |    return subT.upcast(
      |      e.<SubT>accept(
      |        new EvalExpr<This,SupEnv,SubT>(
      |          _this.force(),
      |          subEnv.upcast(this.env)
      |        )
      |      )
      |    );
      |  }
      |}
    """.stripMargin

  val EvalExprSrc =
    """class EvalExpr<This,Env,T> extends ExprVisitor<This,Env,T,T> {
      |  This _this;
      |  Env env;
      |
      |  T var(Index<Env, T> idx) {
      |    return idx.apply(this.env);
      |  }
      |
      |  T _this(Sub<This,T> sub) {
      |    return sub.upcast(this._this);
      |  }
      |
      |  <Fields,Methods>
      |  T
      |  field(Expr<This,Env,Pair<Fields,Methods>> e,
      |        Index<Fields,T> idx) {
      |    return
      |      idx.apply(
      |        e.<Pair<Fields,Methods>>accept(
      |          new EvalExpr<This,Env,Pair<Fields,Methods>>(
      |            this._this, this.env
      |          )
      |        ).fst
      |      );
      |  }
      |
      |  <Fields,Methods,M,As>
      |  T call(Expr<This,Env,Pair<Fields,Methods>> e,
      |         Index<Methods,M> method,
      |         Instantiation<M,BoundExpr<As,T>> inst,
      |         Exprs<This,Env,As> as) {
      |    return
      |      let p : Pair<Fields,Methods> =
      |        e.<Pair<Fields,Methods>>accept(
      |          new EvalExpr<This,Env,Pair<Fields,Methods>>(
      |            this._this, this.env
      |          )
      |        )
      |      in
      |      let be : BoundExpr<As,T> =
      |        inst.instantiate(method.apply(p.snd))
      |      in
      |      be.<T>accept(
      |        new EvalBoundExpr<As,T>(
      |          as.<As>accept(
      |            new EvalExprs<This,Env,As>(
      |              this._this,this.env
      |            )
      |          )
      |        )
      |      );
      |  }
      |
      |  <Fields,Methods,Super>
      |  T
      |  _new(Eq<T,Pair<Fields,Methods>> eq,
      |       Class<Fields,Methods,Super> _class,
      |       Exprs<This,Env,Fields> fields) {
      |    return eq.<\T.T>toLeft(
      |      new Constructor<Fields,Methods>(
      |        fields.<Fields>accept(
      |          new EvalExprs<This,Env,Fields>(
      |            this._this, this.env
      |          )
      |        ),
      |        _class.methods
      |      ).force()
      |    );
      |  }
      |
      |  <Fields,Methods,Super>
      |  T
      |  upcast(Eq<T,Super> eq,
      |         Class<Fields,Methods,Super> _class,
      |         Expr<This,Env,Pair<Fields,Methods>> e) {
      |    return eq.<\T.T>toLeft(
      |      _class.sub.upcast(
      |        e.<Pair<Fields,Methods>>accept(
      |          new EvalExpr<This,Env,Pair<Fields,Methods>>(
      |            this._this, this.env
      |          )
      |        )
      |      )
      |    );
      |  }
      |
      |  <+X, F:X -> *>
      |  T
      |  tAbs(Eq<T, <A:X> F<A>> eq, <A:X> Expr<This,Env,F<A>> e) {
      |    return eq.<\T.T>toLeft(
      |      /\A:X.
      |      e<A>.<F<A>>accept(
      |        new EvalExpr<This,Env,F<A>>(
      |          this._this, this.env
      |        )
      |      )
      |    );
      |  }
      |
      |  <+X, F:X -> *, A:X>
      |  T
      |  tApp(Eq<T, F<A>> eq, Expr<This,Env,<B:X>F<B>> e) {
      |    return eq.<\T.T>toLeft(
      |      e.<<B:X>F<B>>accept(
      |        new EvalExpr<This,Env,<B:X>F<B>>(
      |          this._this, this.env
      |        )
      |      )<A>
      |    );
      |  }
      |
      |  <F:<K>*>
      |  T
      |  kAbs(Eq<T, <+K>F<+K>> eq, <+K> Expr<This,Env,F<+K>> e) {
      |    return eq.<\T.T>toLeft(
      |      /\+K.
      |      e<+K>.<F<+K>>accept(
      |        new EvalExpr<This,Env,F<+K>>(
      |          this._this, this.env
      |        )
      |      )
      |    );
      |  }
      |
      |  <F:<K>*, +X>
      |  T
      |  kApp(Eq<T, F<+X>> eq, Expr<This,Env,<+X>F<+X>> e) {
      |    return eq.<\T.T>toLeft(
      |      e.<<+X>F<+X>>accept(
      |        new EvalExpr<This,Env,<+X>F<+X>>(
      |          this._this, this.env
      |        )
      |      )<+X>
      |    );
      |  }
      |}
    """.stripMargin

  val EvalExprsSrc =
    """class EvalExprs<This,Env,Ts> extends ExprsVisitor<This,Env,Ts,Ts> {
      |  This _this;
      |  Env env;
      |
      |  Ts nilExprs(Eq<Ts,Nil> eq) {
      |    return eq.<\T:*.T>toLeft(new Nil());
      |  }
      |
      |  <Hd,Tl> Ts consExprs(Eq<Ts,Pair<Hd,Tl>> eq,
      |                       Expr<This,Env,Hd> hd,
      |                       Exprs<This,Env,Tl> tl) {
      |    return eq.<\T:*.T>toLeft(
      |      new Pair<Hd,Tl>(
      |        hd.<Hd>accept(
      |          new EvalExpr<This,Env,Hd>(this._this, this.env)
      |        ),
      |        tl.<Tl>accept(
      |          new EvalExprs<This,Env,Tl>(this._this, this.env)
      |        )
      |      )
      |    );
      |  }
      |}
    """.stripMargin

  val classDecls = List(
    ("Mu", MuSrc),
    ("MuClass", MuClassSrc),
    ("SubMu", SubMuSrc),
    ("Sub",            SubSrc),
    ("SubRefl",        SubReflSrc),
    ("SubTrans",       SubTransSrc),
    ("SubPairDepth",        SubPairDepthSrc),
    ("SubPairWidth",        SubPairWidthSrc),
    ("SubForallTy",         SubForallTySrc),
    ("SubForallK",          SubForallKSrc),
    ("SubTop",              SubTopSrc),
    ("Expr",        ExprSrc),
    ("VarExpr",     VarExprSrc),
    /*
    ("ThisExpr",    ThisExprSrc),
    ("GetFieldExpr", GetFieldSrc),
    ("CallMethodExpr", CallMethodSrc),
    */
    ("NewExpr", NewExprSrc),
    ("MuNewExpr", MuNewExprSrc),
    ("CallExpr", CallExprSrc),
    ("MuCallExpr", MuCallExprSrc),
    ("ExprVisitor", ExprVisitorSrc),
    ("Pair",        PairSrc),
    ("Nil",         NilSrc),
    ("Index",       IndexSrc),
    ("IndexZ",      IndexZSrc),
    ("IndexS",      IndexSSrc),
    ("Eq",          EqSrc),
    ("Refl",        ReflSrc),
    ("Fun",         FunSrc),
    ("Class",       ClassSrc),
    ("FunsNil",     FunsNilSrc),
    ("FunsCons",    FunsConsSrc),
    ("Exprs",       ExprsSrc),
    ("ExprsVisitor", ExprsVisitorSrc),
    ("NilExprs",    NilExprsSrc),
    ("ConsExprs",   ConsExprsSrc),
    ("BoundExpr",   BoundExprSrc),
    ("BoundExprVisitor", BoundExprVisitorSrc),
    ("SomeBoundExpr", SomeBoundExprSrc),
    ("BoundExprSub", BoundExprSubSrc),
    ("UpcastBoundExpr", UpcastBoundExprSrc),
    ("SubBoundExpr",    SubBoundExprSrc),
    ("ExprBinder",    ExprBinderSrc),
    ("TPolyExprBinder", TPolyExprBinderSrc),
    ("KPolyExprBinder", KPolyExprBinderSrc),
    ("Lazy",          LazySrc),
    ("Delay",         DelaySrc),
    ("Constructor",   ConstructorSrc),
    ("BindMethodsNil", BindMethodsNilSrc),
    ("BindMethodsCons", BindMethodsConsSrc),
    ("EvalExpr",        EvalExprSrc),
    ("EvalExprs",       EvalExprsSrc),
    ("EvalBoundExpr", EvalBoundExprSrc),

    ("Instantiation", InstantiationSrc),
    ("NoInstantiation", NoInstantiationSrc),
    ("TypeInstantiation", TypeInstantiationSrc),
    ("KindInstantiation", KindInstantiationSrc),

    ("PolyIndex", PolyIndexSrc),
    ("PolyIndexZ", PolyIndexZSrc),
    ("PolyIndexS", PolyIndexSSrc),

    ("Cast", CastSrc),
    ("CastVisitor", CastVisitorSrc),
    ("EvalCast", EvalCastSrc),
  )
}
