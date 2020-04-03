Require Setoid.

Set Implicit Arguments.
Set Universe Polymorphism.

(* General fact(s) I don't know where to put *)

Lemma iff_forall {A} (P Q : A -> Prop) :
  (forall x, P x <-> Q x) -> (forall x, P x) <-> (forall x, Q x).
Proof.
  intros H; split; intros I x; apply H; trivial.
Qed.

(** * Sigma *)

(** Universe-polymorphic [sigT] *)
Inductive paco_sigT@{u v} {A : Type@{u}} (T : A -> Type@{v}) : Type :=
  paco_existT { paco_projT1 : A; paco_projT2 : T paco_projT1 }.

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
Fixpoint Forall@{u} (t : arity@{u}) : (tuple t -> Prop) -> Prop :=
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

Fixpoint curry@{u v w} {r : Type@{v}} (t : arity) :
  (tuple t -> r) -> funtype@{u v w} t r :=
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

Fixpoint const@{u v w} {r : Type@{v}} (y : r) (t : arity) : funtype@{u v w} t r :=
  match t with
  | arity0 => y
  | arityS A t => fun x => const y (t x)
  end.

Fixpoint tyfun_adj@{u v w} (t : arity) :
  forall (T : crel@{u v} t),
    funtype@{u v w} (snoctype t T) arity ->
    funtype@{u v w} t arity :=
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

Definition _rel@{u} (t : arity@{u}) : Type@{u} := tuple t -> Prop.

Lemma uncurry_curry : forall {t : arity} (r : _rel t) (u : tuple t),
  uncurry (curry r) u <-> r u.
Proof.
  induction t; cbn; intros.
  - destruct u; reflexivity.
  - destruct u as [x y]; cbn; apply H.
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
