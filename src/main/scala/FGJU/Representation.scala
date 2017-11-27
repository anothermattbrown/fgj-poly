package FGJU

object Representation {
    val SupertypeOfSrc =
      """class SupertypeOf<A,B extends A> {
        |  A upcast(B b) { return b; }
        |}
      """.stripMargin

    val ExprSrc =
      """class Expr<This,Env,T> {
        |  <Ret> Ret accept(ExprVisitor<This,Env,T,Ret> v) { return this.<Ret>accept(v); }
        |}
      """.stripMargin

    // Polymorphic type-application function (as in Brown-Palsberg POPL'15)
    val TypeAppSrc =
      """class TypeApp<+X,T:X -> *> {
        |  <A:X> T<A> apply(<A:X> T<A> e) { return e<A>; }
        |}
      """.stripMargin

    val KindAppSrc =
      """class KindApp<T:<X>*> {
        |  <+X> T<+X> apply(<+Y> T<+Y> e) { return e<+X>; }
        |}
      """.stripMargin

    /*
    val StrippedVisitorSrc =
      """class StrippedVisitor<This,Env,Ret> {
        |  <A> Ret visitStripped(Expr<This,Env,A> e) { return this.<A>visitStripped(e); }
        |}
      """.stripMargin

    val StrippedSrc =
      """class Stripped<This,Env> {
        |  <Ret> Ret accept(StrippedVisitor<This,Env,Ret> v) { return this.<Ret>accept(v); }
        |}
      """.stripMargin

    val SomeStrippedSrc =
      """class SomeStripped<A,This,Env> extends Stripped<This,Env> {
        |  Expr<This,Env,A> strippedExpr;
        |  <Ret> Ret accept(StrippedVisitor<This,Env,Ret> v) { return v.<A>visitStripped(this.strippedExpr); }
        |}
      """.stripMargin
      */

    val FunSrc =
      """class Fun<A,R> {
        |  R apply(A a) { return this.apply(a); }
        |}
      """.stripMargin

    val StripSrc =
      """class Poly<P,PExp,This,Env> {
        |  <Ret> Ret strip(Q q, [T] Fun<Expr<This,Env,T>, Ret> f) { return this.<Ret>strip(q,f); }
        |  P under(Q q, [T] Fun<Expr<This,Env,T>, T> f) { return this.under(q,f); }
        |}
      """.stripMargin
    val SomeStripSrc =
      """class SomePoly<This,Env,T,P ~> T,PExp ~> Expr<This,Env,T>> extends Poly<P,PExp,This,Env> {
        |  <Ret> Ret strip(PExp q, [T] Fun<Expr<This,Env,T>, Ret> f) {
        |    return ((Fun<Expr<This,Env,T>, Ret>)f).apply((Expr<This,Env,T>)q);
        |  }
        |}
      """.stripMargin

    val IndexSrc =
      """class Index<Env,T> {
        |}
      """.stripMargin

    val EqSrc =
      """class Eq<A,B> {
        |}
      """.stripMargin

    val ExprVisitorSrc =
      """class ExprVisitor<This,Env,T,Ret> {
        |  Ret var(Index<Env,T> idx) { return this.var(idx); }
        |  Ret _this(Eq<T,This> eq) { return this._this(eq); }
        |  <TStripped,ExpT ~> Exp<This,Env,TStripped>>
        |    Ret
        |    typeAbs(ExpT e) { return this.<TStripped,ExpT>typeAbs(e); }
        |  <Q ~> T>
        |    Ret
        |    typeInst(Expr<This,Env,Q> e) {
        |      return this.<Q>typeInst(e);
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
  }


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