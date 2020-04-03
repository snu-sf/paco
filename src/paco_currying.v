From Paco Require Export paco_sigma.
From Paco Require Import paco_internal.

Set Implicit Arguments.
Set Universe Polymorphism.

Section INTERNAL.

Universe u.
Context {t : arity@{u}}.

Definition le (r r' : rel t) : Prop :=
  Forall t (fun u : tuple t => uncurry r u -> uncurry r' u).

Local Infix "<=" := le.

Definition _monotone (gf : rel t -> rel t) : Prop :=
  forall r r' : rel t, r <= r' -> gf r <= gf r'.

Definition _le (r r' : _rel t) : Prop :=
  forall u, r u -> r' u.

Definition __monotone (gf : _rel t -> _rel t) : Prop :=
  forall r r' : _rel t, _le r r' -> _le (gf r) (gf r').

Lemma uncurry_le (r r' : rel t)
  : _le (uncurry r) (uncurry r') <-> r <= r'.
Proof.
  symmetry.
  apply Forall_forall.
Qed.

Lemma curry_le (r r' : _rel t)
  : curry r <= curry r' <-> _le r r'.
Proof.
  etransitivity; [ apply Forall_forall | ].
  apply iff_forall; intros u.
  rewrite 2 uncurry_curry.
  reflexivity.
Qed.

Lemma curry_le_l (r : _rel t) (r' : rel t) :
  _le r (uncurry r') <-> curry r <= r'.
Proof.
  unfold le; rewrite Forall_forall.
  apply iff_forall. intros u. rewrite uncurry_curry.
  reflexivity.
Qed.

Lemma curry_le_r (r : rel t) (r' : _rel t) :
  _le (uncurry r) r' <-> r <= curry r'.
Proof.
  unfold le. rewrite Forall_forall.
  apply iff_forall. intros u. rewrite uncurry_curry.
  reflexivity.
Qed.

Lemma Reflexive_le_ (r : _rel t) : _le r r.
Proof.
  firstorder.
Qed.

Lemma Reflexive_le (r : rel t) : r <= r.
Proof.
  apply uncurry_le, Reflexive_le_.
Qed.

Lemma Transitive_le_ (r r' r'' : _rel t) :
  _le r r' -> _le r' r'' -> _le r r''.
Proof.
  firstorder.
Qed.

Lemma Transitive_le (x y z : rel t) :
  x <= y -> y <= z -> x <= z.
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
  gf (curry r) <= gf' (curry r').
Proof.
  apply uncurry_le.
Qed.

Lemma curry_relT_le (gf gf' : _rel t -> _rel t) (r r' : rel t) :
  curry_relT gf r <= curry_relT gf' r' <->
  _le (gf (uncurry r)) (gf' (uncurry r')).
Proof.
  apply curry_le.
Qed.

Lemma uncurry_monotone (gf : rel t -> rel t)
  : _monotone gf -> __monotone (uncurry_relT gf).
Proof.
  unfold _monotone, __monotone. intros.
  rewrite uncurry_relT_le. apply H. apply curry_le. assumption.
Qed.

Lemma curry_monotone (gf : _rel t -> _rel t)
  : __monotone gf -> _monotone (curry_relT gf).
Proof.
  unfold _monotone, __monotone. intros.
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
  r1 <= r1' -> r2 <= r2' -> le (union r1 r2) (union r1' r2').
Proof.
  unfold union.
  intros HL HR.
  apply curry_le, _union_monotone; apply uncurry_le; assumption.
Qed.

Lemma _monotone_union (gf gf' : rel t -> rel t) :
  _monotone gf ->
  _monotone gf' ->
  _monotone (fun r => union (gf r) (gf' r)).
Proof.
  intros H H' r r' Hrr. apply union_monotone; auto.
Qed.

Lemma _monotone_compose (gf gf' : rel t -> rel t) :
  _monotone gf ->
  _monotone gf' ->
  _monotone (fun r => gf (gf' r)).
Proof.
  intros H H' r r' Hrr; apply H, H', Hrr.
Qed.

Definition le_relT (gf gf' : rel t -> rel t) : Prop :=
  forall r, gf r <= gf' r.

Lemma Reflexive_le_relT gf : le_relT gf gf.
Proof.
  intros r; apply Reflexive_le.
Qed.

Definition _paco (gf : rel t -> rel t) (r : rel t) : rel t :=
  curry (paco (uncurry_relT gf) (uncurry r)).

Definition _upaco (gf : rel t -> rel t) (r : rel t) : rel t :=
  union (_paco gf r) r.

Definition _bot : rel t :=
  curry (fun _ => False).

Lemma _paco_mon_gen :
  forall (gf gf' : rel t -> rel t), le_relT gf gf' ->
  forall (r r' : rel t), r <= r' ->
  _paco gf r <= _paco gf' r'.
Proof.
  intros. apply curry_le. red. apply paco_mon_gen.
  - intro; apply uncurry_relT_le; trivial.
  - apply uncurry_le; assumption.
Qed.

Lemma _bot_min r : _bot <= r.
Proof. apply curry_le_l. red. contradiction. Qed.

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
