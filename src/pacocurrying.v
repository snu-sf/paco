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

Set Printing Universes.

(* Tuple of types *)
Fixpoint tytuple@{u v} (n : nat) : Type@{v} :=
  match n with
  | O => unit
  | S n => paco_sigT@{v _} (fun A : Type@{u} => A -> tytuple n)
  end.

(* From: [A0, A1, ...]
   To:   [forall (x0 : A0) (x1 : A1 x0) ..., T] *)
Fixpoint funtype@{u v w} {n : nat} (r : Type@{w}) : tytuple@{u v} n -> Type@{w} :=
  match n with
  | O => fun _ => r
  | S n => fun t => forall x : paco_projT1 t, funtype r (paco_projT2 t x)
  end.

Fixpoint tuple@{u v w} {n : nat} : tytuple@{u v} n -> Type@{w} :=
  match n with
  | O => fun _ => unit
  | S n => fun t => paco_sigT (fun x => tuple (paco_projT2 t x))
  end.

Fixpoint uncurry@{u v w} {n : nat} (r : Type@{w}) : forall t : tytuple n,
    funtype@{u v w} r t -> tuple t -> r :=
  match n with
  | O => fun _ y _ => y
  | S n => fun _ f u => uncurry r _ (f (paco_projT1 u)) (paco_projT2 u)
  end.

Definition rel@{u v w} {n : nat} : tytuple@{u v} n -> Type@{w} :=
  funtype@{u v w} Prop.

(* From: [A0, A1, ...]
   To:   [forall (x0 : A0) (x1 : A1) ..., Type] *)
Definition crel@{u v v' w} {n : nat} : tytuple@{u v} n -> Type@{w} :=
  funtype@{u v w} Type@{v'}.

Fixpoint snoctype@{u v v' w} {n : nat} : forall t : tytuple@{u v} n, crel@{u v v' w} t -> tytuple@{u v} (S n).
 refine
  match n with
  | O => fun t A => paco_existT _ A (fun _ : A => tt)
  | S n => fun t F =>
    paco_existT@{v v} _ (paco_projT1@{v v} t) (fun x => _)
  end.
 apply (@snoctype _ _ (F x)).
Defined.
(* WTF can't write the term directly *)

Fixpoint const {n : nat} {r : Type} (y : r) : forall t : tytuple n, funtype r t :=
  match n with
  | O => fun _ => y
  | S n => fun t x => const y (paco_projT2 t x)
  end.

Fixpoint map_funtype {n : nat} {r s : Type} (f : r -> s)
  : forall t : tytuple n, funtype r t -> funtype s t :=
  match n with
  | O => fun _ x => f x
  | S n => fun t g y => map_funtype f _ (g y)
  end.

Fixpoint deptype {n : nat} (r : Type) (d : r -> Type) {struct n} : forall t : tytuple n,
    funtype r t -> Type :=
  match n with
  | O => fun _ x => d x
  | S n => fun t f => forall x : _, deptype d _ (f x)
  end.

Fixpoint tyfun_adj {n : nat} (r : Type) {struct n} :
  forall (t : tytuple n) (T : crel t),
    funtype r (snoctype t T) ->
    funtype (paco_sigT (fun A => A -> r)) t :=
  match n with
  | O => fun _ A f => paco_existT _ A f
  | S n => fun t T f x => @tyfun_adj n r _ (T x) (f x)
  end.

Fixpoint _tyforall {n m : nat} (t : tytuple n) {struct m} : (funtype (tytuple m) t -> Type) -> Type :=
  match m with
  | O => fun f => f (const tt t)
  | S m => fun f => forall T : crel t, @_tyforall (S n) m (snoctype t T) (fun g => f (tyfun_adj _ T g))
  end.

Definition tyforall {n : nat} : (tytuple n -> Type) -> Type :=
  @_tyforall 0 n tt.

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
