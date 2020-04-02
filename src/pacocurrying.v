Set Implicit Arguments.

Set Universe Polymorphism.

Inductive paco_sigT@{u v} {A : Type@{u}} (T : A -> Type@{v}) : Type :=
  paco_existT { paco_projT1 : A; paco_projT2 : T paco_projT1 }.

Lemma paco_sigT_curry {A : Type} {T : A -> Type} {U : forall x : A, T x -> Prop} :
  (forall xy : paco_sigT T, U (paco_projT1 xy) (paco_projT2 xy)) -> 
  forall (x : A) (y : T x), U x y.
Proof.
  exact (fun H x y => H (paco_existT _ x y)).
Qed.

Lemma paco_sigT_curry_ {A : Type} {T : A -> Type} {U : paco_sigT T -> Prop} :
  (forall xy : paco_sigT T, U xy) ->
  (forall (x : A) (y : T x), U (paco_existT _ x y)).
Proof.
  exact (fun H _ _ => H _).
Qed.

Lemma paco_sigT_uncurry {A : Type} {T : A -> Type} {U : paco_sigT T -> Prop} :
  (forall (x : A) (y : T x), U (paco_existT _ x y)) ->
  forall xy : paco_sigT T, U xy.
Proof.
  intros H []; apply H.
Qed.

Lemma paco_sigT_uncurry_ {A : Type} {T : A -> Type} {U : forall x : A, T x -> Prop} :
  (forall (x : A) (y : T x), U x y) ->
  (forall xy : paco_sigT T, U (paco_projT1 xy) (paco_projT2 xy)).
Proof.
  exact (fun H _ => H _ _).
Qed.

Ltac fresh_hyp :=
  lazymatch goal with
  | [ |- forall y, _ ] => fresh y
  | _ => fresh
  end.

Ltac uncurry_goal :=
  let x := fresh_hyp in
  tryif intros x then
    uncurry_goal;
    revert x;
    apply paco_sigT_curry;
    try lazymatch goal with
    | [ |- forall (_ : paco_sigT ?H), _ ] =>
      let I := eval cbv beta in (fun x => H x) in
      idtac I;
      change (paco_sigT H) with (paco_sigT I)
    end
  else
    apply (fun pf => pf I).

Ltac curry_goal :=
  lazymatch goal with
  | [ |- True -> _ ] => cbn [ paco_projT1 paco_projT2 ]; intros _
  | [ |- forall _ : paco_sigT (fun y => _), _ ] =>
    tryif apply paco_sigT_uncurry then
      let y := fresh y in
      intros y;
      curry_goal;
      revert y
    else idtac
  end.

(* Tuple of types *)
Inductive arity@{u} : Type :=
| arity0
| arityS : forall A : Type@{u}, (A -> arity) -> arity
.
Arguments arityS : clear implicits.

Fixpoint tuple@{u} (t : arity@{u}) : Type@{u} :=
  match t with
  | arity0 => unit
  | arityS A t => paco_sigT (fun x : A => tuple (t x))
  end.

(* From: [A0, A1, ...]
   To:   [forall (x0 : A0) (x1 : A1 x0) ..., P x0 x1 ...] *)
Fixpoint Forall (t : arity) : (tuple t -> Prop) -> Prop :=
  match t with
  | arity0 => fun f => f tt
  | arityS A t => fun f =>
    forall x : A, Forall (t x) (fun u => f (paco_existT _ x u))
  end.

(* From: [A0, A1, ...]
   To:   [forall (x0 : A0) (x1 : A1 x0) ..., T] *)
Fixpoint Pi@{u v w} (t : arity@{u}) : (tuple t -> Type@{v}) -> Type@{w} :=
  match t with
  | arity0 => fun f => f tt
  | arityS A t => fun f => forall x : A, Pi (t x) (fun u => f (paco_existT _ x u))
  end.

Definition funtype@{u v w} (t : arity@{u}) (r : Type@{v}) : Type@{w} :=
  Pi@{u v w} t (fun _ => r).

Fixpoint uncurry@{u v w} {r : Type@{v}} (t : arity) :
  funtype@{u v w} t r -> tuple t -> r :=
  match t with
  | arity0 => fun y _ => y
  | arityS A t => fun f u => uncurry (t _) (f (paco_projT1 u)) (paco_projT2 u)
  end.

Arguments uncurry {r} [t].

Fixpoint curry {r : Type} (t : arity) :
  (tuple t -> r) -> funtype t r :=
  match t with
  | arity0 => fun f => f tt
  | arityS A t => fun f x => curry (t x) (fun u => f (paco_existT _ x u))
  end.

Arguments curry {r} [t].

Definition rel@{u v} (t : arity) : Type@{v} :=
  funtype@{u v v} t Prop.

(* From: [A0, A1, ...]
   To:   [forall (x0 : A0) (x1 : A1) ..., Type] *)
Definition crel@{u v} (t : arity) : Type@{v} :=
  funtype@{u v v} t Type@{u}.

Fixpoint snoctype@{u v} (t : arity) : crel@{u v} t -> arity :=
  match t with
  | arity0 => fun A => arityS A (fun _ => arity0)
  | arityS A t => fun T => arityS A (fun x => snoctype (t x) (T x))
  end.

Fixpoint const {r : Type} (y : r) (t : arity) : funtype t r :=
  match t with
  | arity0 => y
  | arityS A t => fun x => const y (t x)
  end.

Fixpoint tyfun_adj (t : arity) :
  forall (T : crel t),
    funtype (snoctype t T) arity ->
    funtype t arity :=
  match t with
  | arity0 => fun A t => arityS A t
  | arityS A t => fun T f x => tyfun_adj (t x) (T x) (f x)
  end.

Fixpoint _tyforall (t : arity) (f : funtype t arity -> Type) (n : nat) : Type :=
  match n with
  | O => f (const arity0 t)
  | S n => forall T : crel t, _tyforall (snoctype t T) (fun g => f (tyfun_adj t T g)) n
  end.

Definition tyforall : (arity -> Type) -> nat -> Type :=
  @_tyforall arity0.

Fixpoint _propforall (t : arity) (f : funtype t arity -> Prop) (n : nat) : Prop :=
  match n with
  | O => f (const arity0 t)
  | S n => forall T : crel t, _propforall (snoctype t T) (fun g => f (tyfun_adj t T g)) n
  end.

Definition propforall : (arity -> Prop) -> nat -> Prop :=
  @_propforall arity0.

Lemma Forall_forall (t : arity) (P : tuple t -> Prop) :
  Forall t P <-> forall u, P u.
Proof.
  induction t; cbn.
  - split; [ destruct u | ]; trivial.
  - split.
    + intros I [x y]; specialize (I x). eapply H with (u := y); trivial.
    + intros I x; apply H; trivial.
Qed.

From Paco Require Import paco_internal.

Lemma iff_forall {A} (P Q : A -> Prop) :
  (forall x, P x <-> Q x) -> (forall x, P x) <-> (forall x, Q x).
Proof.
  intros H; split; intros I x; apply H; trivial.
Qed.

Definition _rel@{u} (t : arity@{u}) : Type@{u} := tuple t -> Prop.

Require Setoid.

Lemma uncurry_curry : forall {t : arity} (r : _rel t) (u : tuple t),
  uncurry (curry r) u <-> r u.
Proof.
  induction t; cbn; intros.
  - destruct u; reflexivity.
  - destruct u as [x y]; cbn; apply H.
Qed.

Section INTERNAL.

Universe u.
Context {t : arity@{u}}.

Definition le (r r' : rel t) : Prop :=
  Forall t (fun u : tuple t => uncurry r u -> uncurry r' u).

Definition monotone (gf : rel t -> rel t) : Prop :=
  forall r r' : rel t, le r r' -> le (gf r) (gf r').

Definition _le (r r' : _rel t) : Prop :=
  forall u, r u -> r' u.

Definition _monotone (gf : _rel t -> _rel t) : Prop :=
  forall r r' : _rel t, _le r r' -> _le (gf r) (gf r').

Lemma uncurry_le (r r' : rel t)
  : _le (uncurry r) (uncurry r') <-> le r r'.
Proof.
  symmetry.
  apply Forall_forall.
Qed.

Lemma curry_le (r r' : _rel t)
  : le (curry r) (curry r') <-> _le r r'.
Proof.
  etransitivity; [ apply Forall_forall | ].
  apply iff_forall; intros u.
  rewrite 2 uncurry_curry.
  reflexivity.
Qed.

Lemma Transitive_le_ (r r' r'' : _rel t) :
  _le r r' -> _le r' r'' -> _le r r''.
Proof.
  firstorder.
Qed.

Lemma Transitive_le (x y z : rel t) :
  le x y -> le y z -> le x z.
Proof.
  rewrite <- 3 uncurry_le.
  apply Transitive_le_.
Qed.

Definition uncurry_relT (gf : rel t -> rel t) : _rel t -> _rel t :=
  fun r => uncurry (gf (curry r)).

Definition curry_relT (gf : _rel t -> _rel t) : rel t -> rel t :=
  fun r => curry (gf (uncurry r)).

Lemma uncurry_relT_le (gf gf' : rel t -> rel t) (r r' : _rel t) :
  _le (uncurry_relT gf r) (uncurry_relT gf' r') <->
  le (gf (curry r)) (gf' (curry r')).
Proof.
  apply uncurry_le.
Qed.

Lemma curry_relT_le (gf gf' : _rel t -> _rel t) (r r' : rel t) :
  le (curry_relT gf r) (curry_relT gf' r') <->
  _le (gf (uncurry r)) (gf' (uncurry r')).
Proof.
  apply curry_le.
Qed.

Lemma uncurry_monotone (gf : rel t -> rel t)
  : monotone gf -> _monotone (uncurry_relT gf).
Proof.
  unfold monotone, _monotone. intros.
  rewrite uncurry_relT_le. apply H. apply curry_le. assumption.
Qed.

Lemma curry_monotone (gf : _rel t -> _rel t)
  : _monotone gf -> monotone (curry_relT gf).
Proof.
  unfold monotone, _monotone. intros.
  rewrite curry_relT_le. apply H. apply uncurry_le. assumption.
Qed.

Definition union (r r' : rel t) : rel t :=
  curry (fun u => uncurry r u \/ uncurry r' u).

Lemma _union_monotone (r1 r1' r2 r2' : _rel t) :
  _le r1 r1' -> _le r2 r2' -> _le (fun u => r1 u \/ r2 u) (fun u => r1' u \/ r2' u).
Proof.
  intros HL HR.
  intros ? []; [ left | right ]; auto.
Qed.

Lemma union_monotone (r1 r1' r2 r2' : rel t) :
  le r1 r1' -> le r2 r2' -> le (union r1 r2) (union r1' r2').
Proof.
  unfold union.
  intros HL HR.
  apply curry_le, _union_monotone; apply uncurry_le; assumption.
Qed.

Definition le_relT (gf gf' : rel t -> rel t) : Prop :=
  forall r, le (gf r) (gf' r).

Definition _paco (gf : rel t -> rel t) (r : rel t) : rel t :=
  curry (paco (uncurry_relT gf) (uncurry r)).

Definition _upaco (gf : rel t -> rel t) (r : rel t) : rel t :=
  union (_paco gf r) r.

Lemma paco_mon_gen (gf gf' : rel t -> rel t) (r r' : rel t) :
  le_relT gf gf' -> le r r' -> le (_paco gf r) (_paco gf' r').
Proof.
  intros Hgf Hr. apply curry_le. red. apply _paco_mon_gen.
  - intro; apply uncurry_relT_le, Hgf.
  - apply uncurry_le; assumption.
Qed.

Lemma curry_le_r (r : rel t) (r' : _rel t) :
  _le (uncurry r) r' <-> le r (curry r').
Proof.
  unfold le. rewrite Forall_forall.
  apply iff_forall. intros u. rewrite uncurry_curry.
  reflexivity.
Qed.

Theorem _paco_acc: forall (gf : rel t -> rel t) (rr : rel t)
  l r (OBG: forall rr (INC: le r rr) (CIH: le l rr), le l (_paco gf rr)),
  le l (_paco gf r).
Proof.
  intros. apply curry_le_r.
  eapply _paco_acc. intros.
  apply curry_le_r. apply curry_le_r in INC. apply curry_le_r in CIH.
  specialize (OBG _ INC CIH). unfold _paco in OBG.
  eapply Transitive_le; [ apply OBG | ].
  apply curry_le.
  red; apply paco_internal._paco_mon_gen; trivial. apply uncurry_curry.
Qed.

End INTERNAL.

(*
Fixpoint telesig (t : telescope) : Type :=
  match t with
  | @tscp A f => paco_sigT (fun x : A => telesig (f x))
  | tscp0 _ => True
  end.

Fixpoint teleprop (t : telescope) : telesig t -> Prop :=
  match t with
  | @tscp A f => fun h => teleprop (f (paco_projT1 h)) (paco_projT2 h)
  | tscp0 P => fun h => P
  end.

Fixpoint teleforall (t : telescope) : Prop :=
  match t with
  | @tscp A f => forall a : A, teleforall (f a)
  | tscp0 P => P
  end.

Ltac uncurry_hyp OBG :=
  let t := fresh "t" in
  unshelve refine (let t : telescope := _ in _);
    [ repeat lazymatch type of OBG with
             | forall x : ?A, _ =>
               apply (@tscp A);
               let x := fresh x in
               intros x;
               specialize (OBG x)
             | ?T => apply (tscp0 T)
             end
    | cut (forall x, teleprop t x); subst t; cbv [telesig teleprop];
      [ clear OBG; intros OBG
      | intros x;
        let rec go t := assumption + specialize (OBG (paco_projT1 t)); go (paco_projT2 t) in
        go x
      ]
    ].

Ltac curry_hyp OBG :=
  let t := fresh "t" in
  unshelve refine (let t : telescope := _ in _);
    [ repeat lazymatch type of OBG with
             | forall _ : paco_sigT (fun x : ?A => _), _ =>
               apply (@tscp A);
               let x := fresh x in
               intros x;
               let OBG' := fresh OBG in
               rename OBG into OBG';
               pose proof (paco_sigT_curry_ OBG' x) as OBG; clear OBG';
               cbn [paco_projT1 paco_projT2] in OBG
             | True -> ?T => apply (tscp0 T)
             end
    | cbv zeta beta in t;
      cut (teleforall t); subst t; cbv [ teleforall ];
      [ clear OBG; intros OBG
      | repeat lazymatch goal with
             | [ |- forall x : _, _ ] =>
               let x := fresh x in
               intros x;
               let OBG' := fresh OBG in
               rename OBG into OBG';
               pose proof (paco_sigT_curry_ OBG' x) as OBG; clear OBG';
               cbn [paco_projT1 paco_projT2] in OBG
             end;
        exact (OBG I)
      ]
    ].

Section TEST.

Context (hyp : forall (x y z : nat), Prop).
Context (goal : forall (u v w : bool), Prop).

Lemma TEST
      (H : forall x y z : nat, x < z -> hyp x y z) :
  forall u v w, u = true -> goal u v w.
Proof.
  uncurry_hyp H.
  curry_hyp H.
  uncurry_goal.
  curry_goal.
Abort.

End TEST.
*)
