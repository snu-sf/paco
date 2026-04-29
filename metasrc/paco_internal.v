From Paco Require Export paconotation.
From Paco Require Import pacotac_internal paconotation_internal.
Set Implicit Arguments.
Set Primitive Projections.

(** ** Predicates of Arity 1
*)

Section Arg1_def.

Variable T0 : Type.
Variable gf : rel1 T0 -> rel1 T0.
Arguments gf : clear implicits.

Variant _gf (r: rel1 T0) x0 : Prop :=
| paco_pfold pco
    (LE : pco <1= r)
    (SIM: gf pco x0)
.

Definition paco (r: rel1 T0) (x0: T0)  : Prop :=
  exists pf, pf <1= _gf (pf \1/ r) /\ pf x0.

Definition upaco(r: rel1 T0) := paco r \1/ r.

End Arg1_def.

Arguments paco [ T0 ] gf r x0.
Arguments upaco [ T0 ] gf r x0.
#[export] Hint Unfold upaco : core.

Lemma gf_mon T0 gf gf' r r' x
  (IN: @_gf T0 gf r  x)
  (LEgf: gf <2= gf')
  (LEr: r <1= r')
  :
  _gf gf' r' x.
Proof.
  destruct IN. econstructor; intros.
   - apply LE in PR. eauto.
   - eapply LEgf. eauto.
Qed.

Lemma paco_observe T0 gf
  : forall (r : rel1 T0) (x0 : T0), paco gf r x0 -> _gf gf (paco gf r \1/ r) x0.
Proof.
  intros. destruct H as [? [? ?]].
  eapply gf_mon; eauto.
  intros. destruct PR; eauto.
  left. econstructor. eauto.
Qed.

Lemma paco_go T0 gf
  : forall (r : rel1 T0) (x0 : T0), _gf gf (paco gf r \1/ r) x0 -> paco gf r x0.
Proof.
  intros. econstructor. split; eauto.
  intros. eapply gf_mon; eauto.
  intros. destruct PR0; eauto.
  left. eapply paco_observe. eauto.
Qed.

#[export] Hint Resolve gf_mon : core.
#[export] Hint Resolve paco_observe : core.
#[export] Hint Resolve paco_go : core.

Definition monotone T0 (gf: rel1 T0 -> rel1 T0) :=
  forall x0 r r' (IN: gf r x0) (LE: r <1= r'), gf r' x0.

Definition _monotone T0 (gf: rel1 T0 -> rel1 T0) :=
  forall r r'(LE: r <1= r'), gf r <1== gf r'.

Lemma monotone_eq T0 (gf: rel1 T0 -> rel1 T0) :
  monotone gf <-> _monotone gf.
Proof. unfold monotone, _monotone, le1. split; eauto. Qed.

Lemma paco_mon_gen T0 gf gf' r r' x
    (PR: @paco T0 gf r x)
    (LEgf: gf <2= gf')
    (LEr: r <1= r'):
  paco gf' r' x.
Proof.
  destruct PR as [pf [PFH PFx]].
  exists pf. split; eauto.
  intros. eapply gf_mon; eauto.
  intros. destruct PR0; eauto.
Qed.

Lemma paco_cofix T0 gf r l
  (LE: l <1= @_gf T0 gf (l \1/ r))
  :
  l <1= paco gf r.
Proof.
  intros. exists l. eauto.
Qed.

Section Arg1.

Variable T0 : Type.
Variable gf : rel1 T0 -> rel1 T0.
Arguments gf : clear implicits.

Theorem paco_mon: monotone (paco gf).
Proof. red; intros. eapply paco_mon_gen; eauto. Qed.

Theorem paco_mult_strong: forall r,
  paco gf (upaco gf r) <1= paco gf r.
Proof.
  intros. eapply paco_cofix with (l := paco gf r \1/ paco gf (paco gf r \1/ r)); eauto.
  intros. destruct PR0 as [PR0|PR0].
  - eapply paco_observe in PR0. eapply gf_mon; eauto.
    intros. destruct PR1; eauto.
  - eapply paco_observe in PR0. eapply gf_mon; eauto.
    intros. destruct PR1 as [PR1|[]]; eauto.
Qed.

Corollary paco_mult: forall r,
  paco gf (paco gf r) <1= paco gf r.
Proof. intros; eapply paco_mult_strong, paco_mon; eauto. Qed.

Theorem paco_acc: forall
  l r (OBG: forall rr (INC: r <1= rr) (CIH: l <1= rr), l <1= paco gf rr),
  l <1= paco gf r.
Proof.
  intros l r LE.
  assert (SIM: l <1= paco gf (l \1/ r)) by eauto. clear LE.
  intros. eapply paco_mult_strong.
  eapply paco_cofix with (l := paco gf (l \1/ r)); eauto.
  intros. eapply paco_observe in PR0.
  eapply gf_mon; eauto.
  intros. destruct PR1 as [PR1|[PR1|PR1]]; eauto.
Qed.

Theorem paco_fold: forall r,
  gf (upaco gf r) <1= paco gf r.
Proof. intros. eapply paco_go. econstructor; [|apply PR]. eauto. Qed.

Theorem paco_unfold: forall (MON: monotone gf) r,
  paco gf r <1= gf (upaco gf r).
Proof. unfold monotone; intros; apply paco_observe in PR; destruct PR as []; eauto. Qed.

Theorem _paco_acc: forall
  l r (OBG: forall rr (INC: r <1== rr) (CIH: l <1== rr), l <1== paco gf rr),
  l <1== paco gf r.
Proof. unfold le1. eapply paco_acc. Qed.

Theorem _paco_mon: _monotone (paco gf).
Proof. apply monotone_eq. eapply paco_mon. Qed.

Theorem _paco_mult_strong: forall r,
  paco gf (upaco gf r) <1== paco gf r.
Proof. unfold le1. eapply paco_mult_strong. Qed.

Theorem _paco_fold: forall r,
  gf (upaco gf r) <1== paco gf r.
Proof. unfold le1. eapply paco_fold. Qed.

Theorem _paco_unfold: forall (MON: _monotone gf) r,
  paco gf r <1== gf (upaco gf r).
Proof.
  unfold le1. intro.
  eapply paco_unfold; apply monotone_eq; eauto.
Qed.

End Arg1.

#[export] Hint Unfold monotone : core.
#[export] Hint Resolve paco_fold : core.

Arguments paco_mon_gen        [ T0 ] gf gf' r r' x PR LEgf LEr.
Arguments paco_acc            [ T0 ] gf l r OBG x0 PR.
Arguments paco_mon            [ T0 ] gf x0 r r' IN LE.
Arguments paco_mult_strong    [ T0 ] gf r x0 PR.
Arguments paco_mult           [ T0 ] gf r x0 PR.
Arguments paco_fold           [ T0 ] gf r x0 PR.
Arguments paco_unfold         [ T0 ] gf MON r x0 PR.
