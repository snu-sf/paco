From Paco Require Export paco_rel.
From Paco Require Import paco_internal.

Set Implicit Arguments.
Set Universe Polymorphism.

Section INTERNAL.

Universe u.
Context {t : arity@{u}}.

Local Infix "<=" := le.

Definition _paco (gf : rel t -> rel t) (r : rel t) : rel t :=
  curry (paco (uncurry_relT gf) (uncurry r)).

Definition _upaco (gf : rel t -> rel t) (r : rel t) : rel t :=
  union (_paco gf r) r.

Lemma _paco_mon_gen :
  forall (gf gf' : rel t -> rel t), le_relT gf gf' ->
  forall (r r' : rel t), r <= r' ->
  _paco gf r <= _paco gf' r'.
Proof.
  intros. apply curry_le. red. apply paco_mon_gen.
  - intro; apply uncurry_relT_le; trivial.
  - apply uncurry_le; assumption.
Qed.

Lemma _paco_mon_bot (gf gf' : rel t -> rel t) (r : rel t) :
  le_relT gf gf' -> _paco gf _bot <= _paco gf' r.
Proof.
  intros H. apply _paco_mon_gen with (2 := _bot_min r). auto.
Qed.

Lemma _upaco_mon_gen (gf gf': rel t -> rel t)
    (LEgf: le_relT gf gf')
    r r' (LEr: r <= r'):
  _upaco gf r <= _upaco gf' r'.
Proof.
  apply union_monotone; [ | assumption ].
  apply _paco_mon_gen; assumption.
Qed.

Lemma _upaco_mon_bot (gf gf' : rel t -> rel t) (r : rel t) :
  le_relT gf gf' -> _upaco gf _bot <= _upaco gf' r.
Proof.
  intros H. apply _upaco_mon_gen with (2 := _bot_min r). auto.
Qed.

Theorem _paco_mon gf : _monotone (_paco gf).
Proof.
  red. apply _paco_mon_gen. apply Reflexive_le_relT.
Qed.

Theorem _upaco_mon gf : _monotone (_upaco gf).
Proof.
  red. apply _upaco_mon_gen. apply Reflexive_le_relT.
Qed.

Theorem _paco_acc: forall (gf : rel t -> rel t)
  l r (OBG: forall rr (INC: r <= rr) (CIH: l <= rr), l <= _paco gf rr),
  l <= _paco gf r.
Proof.
  intros. apply curry_le_r.
  eapply _paco_acc. intros.
  apply curry_le_r. apply curry_le_r in INC. apply curry_le_r in CIH.
  specialize (OBG _ INC CIH). unfold _paco in OBG.
  eapply Transitive_le; [ apply OBG | ].
  apply curry_le.
  red; apply paco_mon_gen; trivial. apply uncurry_curry.
Qed.

Theorem _paco_mult_strong: forall gf r,
  _paco gf (_upaco gf r) <= _paco gf r.
Proof.
  intros; apply curry_le.
  eapply Transitive_le_; [ | eapply _paco_mult_strong ].
  red; eapply paco_mon_gen.
  - intros x; apply uncurry_relT_le, Reflexive_le.
  - intros x; unfold _upaco, union. rewrite uncurry_curry.
    intros []; [ left | right ]; auto.
    apply uncurry_curry; auto.
Qed.

Corollary _paco_mult: forall gf r,
  _paco gf (_paco gf r) <= _paco gf r.
Proof.
  intros;
  eapply Transitive_le; [ | eapply _paco_mult_strong ].
  apply _paco_mon_gen. apply Reflexive_le_relT.
  apply curry_le; left.
  apply uncurry_curry. auto.
Qed.

Theorem _paco_fold: forall gf (MON: _monotone gf) r,
  gf (_upaco gf r) <= _paco gf r.
Proof.
  intros. eapply Transitive_le; [ | eapply curry_le, _paco_fold ].
  apply curry_le_r. apply uncurry_monotone; auto.
  intros ? []; [ left | right ]; auto.
  apply uncurry_curry; auto.
Qed.

Theorem _paco_unfold: forall gf (MON: _monotone gf) r,
  _paco gf r <= gf (_upaco gf r).
Proof.
  intros. eapply Transitive_le; [ eapply curry_le, _paco_unfold, uncurry_monotone; auto | ].
  apply curry_le_l. apply uncurry_monotone; auto.
  intros ? []; [ left | right ]; auto.
  apply uncurry_curry; auto.
Qed.

End INTERNAL.

Arguments _paco_fold : clear implicits.
Arguments _paco_unfold : clear implicits.

Arguments _paco_fold {t}.
Arguments _paco_unfold {t}.
