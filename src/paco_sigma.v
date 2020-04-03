Require Setoid.

Set Implicit Arguments.
Set Universe Polymorphism.

Delimit Scope paco_scope with paco.
Local Open Scope paco_scope.

(* General fact(s) I don't know where to put *)

Lemma iff_forall {A} (P Q : A -> Prop) :
  (forall x, P x <-> Q x) -> (forall x, P x) <-> (forall x, Q x).
Proof.
  intros H; split; intros I x; apply H; trivial.
Qed.

(* Universe-polymorphic [eq] *)
Inductive paco_eq@{u} {A : Type@{u}} (a : A) : A -> Prop :=
| paco_eq_refl : paco_eq a a.

Local Infix "=" := paco_eq : paco_scope.
Local Open Scope paco_scope.

Lemma f_equal@{u} {A B : Type@{u}} (f : A -> B) (x y : A) :
  (x = y)%paco -> (f x = f y)%paco.
Proof.
  intros []; constructor.
Qed.

(** * Sigma *)

(** Universe-polymorphic [sigT] *)
Inductive paco_sigT@{u v} {A : Type@{u}} (T : A -> Type@{v}) : Type :=
  paco_existT { paco_projT1 : A; paco_projT2 : T paco_projT1 }.

Local Notation "{ x : A & P }" := (paco_sigT (fun x : A => P)) : paco_scope.

Lemma paco_sigT_curry@{u v} {A : Type@{u}} {T : A -> Type@{v}}
      {U : forall x : A, T x -> Prop} :
  (forall xy : paco_sigT T, U (paco_projT1 xy) (paco_projT2 xy)) -> 
  forall (x : A) (y : T x), U x y.
Proof.
  exact (fun H x y => H (paco_existT _ x y)).
Qed.

Lemma paco_sigT_curry_2@{u v} {A : Type@{u}} {T : A -> Type@{v}}
      {U : paco_sigT T -> Prop} :
  (forall xy : paco_sigT T, U xy) ->
  (forall (x : A) (y : T x), U (paco_existT _ x y)).
Proof.
  exact (fun H _ _ => H _).
Qed.

Lemma paco_sigT_uncurry@{u v} {A : Type@{u}} {T : A -> Type@{v}}
      {U : paco_sigT T -> Prop} :
  (forall (x : A) (y : T x), U (paco_existT _ x y)) ->
  forall xy : paco_sigT T, U xy.
Proof.
  intros H []; apply H.
Qed.

Lemma paco_sigT_uncurry_@{u v} {A : Type@{u}} {T : A -> Type@{v}}
      {U : forall x : A, T x -> Prop} :
  (forall (x : A) (y : T x), U x y) ->
  (forall xy : paco_sigT T, U (paco_projT1 xy) (paco_projT2 xy)).
Proof.
  exact (fun H _ => H _ _).
Qed.

(** * Arity-generic constructions *)

Set Printing Universes.

(* Tuple of types *)
Fixpoint arity@{u v w} (n : nat) : Type@{v} :=
  match n with
  | O => unit
  | S n => paco_sigT@{u v} (fun A : Type@{w} => A -> arity n)
  end.

Notation arity_hd := (@paco_projT1 Type (fun A => A -> arity _)).
Notation arity_tl := (@paco_projT2 Type (fun A => A -> arity _)).

Definition arity0 : arity 0 := tt.
Notation arityS := (@paco_existT Type (fun A => A -> arity _)).

Lemma arity_inv {n} : forall (t : arity n),
  (match n return arity n -> arity n with
  | O => fun _ => tt
  | S n => fun t : arity (S n) => arityS (arity_hd t) (arity_tl t)
  end t = t)%paco.
Proof.
  destruct n; destruct t; reflexivity.
Defined.

Fixpoint tuple@{u v w} {n} : arity@{u v w} n -> Type@{u} :=
  match n with
  | O => fun _ => unit
  | S n => fun t => paco_sigT (fun x : paco_projT1 t => tuple (paco_projT2 t x))
  end.

(* From: [A0, A1, ...]
   To:   [forall (x0 : A0) (x1 : A1 x0) ..., P x0 x1 ...] *)
Fixpoint Forall {n} : forall (t : arity n), (tuple t -> Prop) -> Prop :=
  match n with
  | O => fun _ f => f tt
  | S n => fun t f =>
    forall x, Forall (arity_tl t x) (fun u => f (paco_existT _ x u))
  end.

(* From: [A0, A1, ...]
   To:   [forall (x0 : A0) (x1 : A1 x0) ..., T] *)
Fixpoint Pi {n} : forall (t : arity n), (tuple t -> Type) -> Type :=
  match n with
  | O => fun _ f => f tt
  | S n => fun t f => forall x, Pi (arity_tl t x) (fun u => f (paco_existT _ x u))
  end.

Notation funtype t r := (@Pi _ t (fun _ => r)).

Fixpoint uncurry@{u v w} {n} {r : Type@{u}} : forall t : arity@{u v w} n,
  funtype t r -> tuple t -> r :=
  match n with
  | O => fun _ y _ => y
  | S n => fun t f u => uncurry (paco_projT2 t _) (f _) (paco_projT2 u)
  end.

Arguments uncurry {n r} [t].

Fixpoint curry@{u v w} {n} {r : Type@{u}} : forall (t : arity@{u v w} n),
  (tuple t -> r) -> funtype t r :=
  match n with
  | O => fun _ f => f tt
  | S n => fun t f x =>
      curry (paco_projT2 t x) (fun u => f (paco_existT _ x u))
  end.

Arguments curry {n r} [t].

Notation rel t := (funtype t Prop).
Notation crel t := (funtype t Type).

Fixpoint snoctype {n} : forall (t : arity n), crel t -> arity (S n) :=
  match n with
  | O => fun _ A => arityS A (fun _ => arity0)
  | S n => fun t T => arityS _ (fun x => snoctype (arity_tl t x) (T x))
  end.

Fixpoint const {n} {r : Type} (y : r) : forall (t : arity n), funtype t r :=
  match n with
  | O => fun _ => y
  | S n => fun t x => const y (arity_tl t x)
  end.

Fixpoint tyfun_adj {n m} : forall (t : arity n) (T : crel t),
    funtype (snoctype t T) (arity m) ->
    funtype t (arity (S m)) :=
  match n with
  | O => fun _ A t' => arityS A t'
  | S n => fun t T f x => tyfun_adj (arity_tl t x) (T x) (f x)
  end.

Fixpoint _tyforall {m} (t : arity m) {n} :
  (funtype t (arity n) -> Type) -> Type :=
  match n with
  | O => fun f => f (const arity0 t)
  | S n => fun f => forall T : crel t, _tyforall (snoctype t T) (fun g => f (tyfun_adj t T g))
  end.

Definition tyforall : forall n, (arity n -> Type) -> Type :=
  @_tyforall _ arity0.

Fixpoint _propforall {m} (t : arity m) {n} :
  (funtype t (arity n) -> Prop) -> Prop :=
  match n with
  | O => fun f => f (const arity0 t)
  | S n => fun f => forall T : crel t, _propforall (snoctype t T) (fun g => f (tyfun_adj t T g))
  end.

Definition propforall : forall n, (arity n -> Prop) -> Prop :=
  @_propforall _ arity0.

Lemma Forall_forall {n} (t : arity n) (P : tuple t -> Prop) :
  Forall t P <-> forall u, P u.
Proof.
  induction n; cbn.
  - split; [ destruct u | ]; trivial.
  - split.
    + intros I [x y]; specialize (I x). eapply IHn with (u := y); trivial.
    + intros I x; apply IHn; trivial.
Qed.

Definition _rel@{u v w} {n} (t : arity@{u v w} n) : Type@{u} := tuple@{u v w} t -> Prop.

Lemma curry_uncurry_ext : forall {n} {A : Type}
                             (t : A -> arity n) {R : Type}
                             (f : forall a, funtype (t a) R),
    ((fun x => curry (uncurry (f x))) = f)%paco.
Proof.
  induction n; cbn; intros.
  - constructor.
  - change (fun u => ?f u) with f.
    specialize (IHn { a : A & arity_hd (t a) }%paco).
    specialize (IHn _ _ (fun u => f _ (paco_projT2 u))).
    apply (f_equal (fun g x y => g (paco_existT _ x y))) in IHn.
    apply IHn.
Qed.

Lemma curry_uncurry : forall {n} (t : arity n) (R : Type) (f : funtype t R),
    (curry (uncurry f) = f)%paco.
Proof.
  intros.
  assert (H := curry_uncurry_ext (fun _ : unit => t) (fun _ : unit => f)).
  apply (f_equal (fun f => f tt)) in H.
  exact H.
Qed.

Lemma uncurry_curry_eq : forall {n} {R : Type}
                             {t : arity n} (f : tuple t -> R) (x : tuple t),
  (uncurry (curry f) x = f x)%paco.
Proof.
  induction n; cbn; intros R t f []; cbn.
  - reflexivity.
  - rewrite IHn. reflexivity.
Qed.

Lemma uncurry_curry@{u v w} : forall {n} {t : arity@{u v w} n} (r : _rel t) (u : tuple t),
  uncurry (curry r) u <-> r u.
Proof.
  intros; destruct (uncurry_curry_eq r u); reflexivity.
Qed.

(** * Tactics *)

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
