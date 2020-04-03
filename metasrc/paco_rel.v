From Paco Require Export paco_sigma.

Set Implicit Arguments.
Set Universe Polymorphism.

Section REL.

Universe u v w.
Context {n : nat} {t : arity@{u v w} n}.

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

Definition _le_relT (gf gf' : _rel t -> _rel t) : Prop :=
  forall r, _le (gf r) (gf' r).

Definition le_relT (gf gf' : rel t -> rel t) : Prop :=
  forall r, gf r <= gf' r.

Lemma Reflexive_le_relT gf : le_relT gf gf.
Proof.
  intros r; apply Reflexive_le.
Qed.

Lemma Reflexive_le_relT_ gf : _le_relT gf gf.
Proof.
  intros r; apply Reflexive_le_.
Qed.

Lemma uncurry_relT_le_relT (gf gf' : rel t -> rel t) :
  le_relT gf gf' ->
  _le_relT (uncurry_relT gf) (uncurry_relT gf').
Proof.
  intros Hle r. apply uncurry_relT_le, Hle.
Qed.

Definition _bot : rel t :=
  curry (fun _ => False).

Lemma _bot_min r : _bot <= r.
Proof. apply curry_le_l. red. contradiction. Qed.

End REL.
