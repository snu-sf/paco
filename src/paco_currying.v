From Paco Require Export paco_rel.
From Paco Require Import paco_internal.

Set Implicit Arguments.
Set Universe Polymorphism.

Section PACO.

Universe u.
Context {t : arity@{u}}.

Local Infix "<=" := le.

Definition _paco (gf : rel t -> rel t) (r : rel t) : rel t :=
  curry (paco (uncurry_relT gf) (uncurry r)).

(* An alternative definition is
   [curry (upaco (uncurry_relT gf) (uncurry r))]
   They are propositionally equal if [t] is an [arityn n],
   but the one below unifies more easily with [_paco gf r \n/ r].
 *)
Definition _upaco paco_ (gf : rel t -> rel t) (r : rel t) : rel t :=
  union (paco_ gf r) r.

End PACO.

Section PACOLEMMAS.

Inductive paco_spec : forall
  (rel_ : Type)
  (le_ : rel_ -> rel_ -> Prop)
  (bot_ : rel_)
  (paco_ upaco_ : (rel_ -> rel_) -> rel_ -> rel_), Prop :=
| upaco_refl (t : arity) paco_
  (PACO_WRAP : forall gf r, le (_paco (t := t) gf r) (paco_ gf r))
  (PACO_UNWRAP : forall gf r, le (paco_ gf r) (_paco (t := t) gf r))

  (* TODO: No longer needed after paco_fold'? maybe in gpaco *)
  (UPACO_SPEC : paco_eq
     (_upaco _paco)
     (fun gf (r : rel t) => curry (upaco (uncurry_relT gf) (uncurry r)))) :
  @paco_spec (rel t) le _bot paco_ (_upaco paco_)
.

Lemma paco_left t paco_ gf r r'
  (PACO_UNWRAP : forall gf r, le (paco_ gf r) (_paco (t := t) gf r)) :
  le (_paco (t := t) gf r) r' -> le (paco_ gf r) r'.
Proof.
  intros H; eapply Transitive_le; [ apply PACO_UNWRAP | eassumption ].
Qed.

Lemma paco_right t paco_ gf r r'
  (PACO_WRAP : forall gf r, le (_paco (t := t) gf r) (paco_ gf r)) :
  le r (_paco (t := t) gf r') -> le r (paco_ gf r').
Proof.
  intros H; eapply Transitive_le; [ eassumption | apply PACO_WRAP ].
Qed.

Ltac paco_wrap :=
  repeat
    ((apply paco_right + apply paco_left); [ assumption | ]).

Lemma paco_spec_proof {n} (t : arityn n) paco_ :
  (forall gf r, le (_paco (t := t) gf r) (paco_ gf r)) ->
  (forall gf r, le (paco_ gf r) (_paco (t := t) gf r)) ->
  paco_spec (rel_ := rel t) le _bot paco_ (_upaco paco_).
Proof.
  constructor; try assumption. clear.
  assert (I := @curry_uncurry_ctx n).
  specialize (I ((rel (aton t) -> rel (aton t)) * funtype (aton t) Prop)%type).
  specialize (I (fun _ => t) Prop Prop).
  specialize (I (fun gfr => paco (uncurry_relT (fst gfr)) (uncurry (snd gfr)))).
  specialize (I (fun gfr u p => p \/ uncurry (snd gfr) u)).
  apply (f_equal (fun h gf r => h (gf, r))) in I.
  cbn in I. unfold _upaco, union, upaco, _paco.
  apply I.
Qed.

Context
  (rel_ : Type)
  (le_ : rel_ -> rel_ -> Prop)
  (bot_ : rel_)
  (paco_ upaco_ : (rel_ -> rel_) -> rel_ -> rel_)
  (SPEC : @paco_spec rel_ le_ bot_ paco_ upaco_).

Local Infix "<=" := le_.
Notation le1_ gf gf' := (forall r, le_ (gf r) (gf' r)).

Definition monotone_ (gf : rel_ -> rel_) : Prop :=
  forall r r', le_ r r' -> le_ (gf r) (gf r').

Lemma _paco_mon_gen :
  forall (gf gf' : rel_ -> rel_), le1_ gf gf' ->
  forall (r r' : rel_), r <= r' ->
  paco_ gf r <= paco_ gf' r'.
Proof.
  destruct SPEC.
  intros. paco_wrap; apply curry_le.
  red. apply paco_mon_gen.
  - intro; apply uncurry_relT_le; trivial.
  - apply uncurry_le; assumption.
Qed.

Lemma _bot_min (r : rel_) : bot_ <= r.
Proof.
  destruct SPEC. apply _bot_min.
Qed.

Lemma _paco_mon_bot (gf gf' : rel_ -> rel_) (r : rel_) :
  le1_ gf gf' -> paco_ gf bot_ <= paco_ gf' r.
Proof.
  intros H. apply _paco_mon_gen with (2 := _bot_min r). auto.
Qed.

Lemma _upaco_mon_gen (gf gf': rel_ -> rel_)
    (LEgf: le1_ gf gf')
    r r' (LEr: r <= r'):
  upaco_ gf r <= upaco_ gf' r'.
Proof.
  destruct SPEC.
  symmetry in UPACO_SPEC; destruct UPACO_SPEC.
  apply curry_le, _union_monotone.
  - apply uncurry_le. paco_wrap. apply curry_le.
    red; apply paco_mon_gen.
    + intros ?; apply uncurry_le, LEgf.
    + apply uncurry_le, LEr.
  - apply uncurry_le, LEr.
Qed.

Lemma _upaco_mon_bot (gf gf' : rel_ -> rel_) (r : rel_) :
  le1_ gf gf' -> upaco_ gf bot_ <= upaco_ gf' r.
Proof.
  intros H. apply _upaco_mon_gen with (2 := _bot_min r). auto.
Qed.

Theorem _paco_mon gf : monotone_ (paco_ gf).
Proof.
  red. apply _paco_mon_gen. destruct SPEC; apply Reflexive_le_relT.
Qed.

Theorem _upaco_mon gf : monotone_ (upaco_ gf).
Proof.
  red. apply _upaco_mon_gen. destruct SPEC; apply Reflexive_le_relT.
Qed.

Theorem _paco_acc: forall (gf : rel_ -> rel_)
  l r (OBG: forall rr (INC: r <= rr) (CIH: l <= rr), l <= paco_ gf rr),
  l <= paco_ gf r.
Proof.
  destruct SPEC.
  intros. paco_wrap. apply curry_le_r.
  eapply _paco_acc. intros.
  apply curry_le_r. apply curry_le_r in INC. apply curry_le_r in CIH.
  specialize (OBG _ INC CIH). unfold _paco in OBG.
  eapply Transitive_le; [ apply OBG | ].
  paco_wrap.
  apply curry_le.
  red; apply paco_mon_gen; trivial. apply uncurry_curry.
Qed.

Theorem _paco_mult_strong: forall gf r,
  paco_ gf (upaco_ gf r) <= paco_ gf r.
Proof.
  destruct SPEC.
  intros; paco_wrap; apply curry_le.
  eapply Transitive_le_; [ | eapply _paco_mult_strong ].
  red; eapply paco_mon_gen.
  - intros x; apply uncurry_relT_le, Reflexive_le.
  - intros x; unfold _upaco, union. rewrite uncurry_curry.
    intros []; [ left | right ]; auto.
    revert x H. apply curry_le_r, PACO_UNWRAP.
Qed.

Corollary _paco_mult: forall gf r,
  paco_ gf (paco_ gf r) <= paco_ gf r.
Proof.
  pose proof _paco_mult_strong as PMS.
  pose proof _paco_mon_gen as PMG.
  destruct SPEC.
  intros;
  eapply Transitive_le; [ | eapply PMS ].
  apply PMG. apply Reflexive_le_relT.
  apply curry_le_r. left. assumption.
Qed.

Theorem _paco_fold: forall gf r,
  gf (upaco_ gf r) <= paco_ gf r.
Proof.
  destruct SPEC.
  intros. paco_wrap.
  apply curry_le_r.
  red; apply (paco_fold' (gf := uncurry_relT gf)).
  intros x [H|H]; [ left | right; auto ].
  revert x H; apply curry_le_r, PACO_UNWRAP.
Qed.

Theorem _paco_unfold: forall gf (MON: monotone_ gf) r,
  paco_ gf r <= gf (upaco_ gf r).
Proof.
  unfold monotone_.
  destruct SPEC. intros.
  eapply Transitive_le; [ apply PACO_UNWRAP | ].
  eapply Transitive_le; [ apply curry_le, _paco_unfold, uncurry_monotone; auto | ].
  apply curry_le_l. apply uncurry_monotone; auto.
  intros x [H|H]; [ left | right ]; auto.
  revert x H. apply curry_le_l, PACO_WRAP.
Qed.

End PACOLEMMAS.

Arguments _paco_unfold : clear implicits.
Arguments _paco_unfold [_ _ _ _ _] SPEC gf.
