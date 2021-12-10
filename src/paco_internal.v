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

Variant _paco (paco: rel1 T0 -> rel1 T0) ( r: rel1 T0) x0 : Prop :=
| paco_pfold pco
    (LE : pco <1= (paco r \1/ r))
    (SIM: gf pco x0)
.

CoInductive paco r x0 : Prop := paco_go { paco_observe: _paco paco r x0 }.

Definition upaco( r: rel1 T0) := paco r \1/ r.

End Arg1_def.

Arguments paco [ T0 ] gf r x0.
Arguments upaco [ T0 ] gf r x0.
#[export] Hint Unfold upaco : core.

(* Less than or equal - internal use only *)
Notation "p <_paco_1= q" :=
  (forall _paco_x0 (PR: p _paco_x0 : Prop), q _paco_x0 : Prop)
  (at level 50, no associativity).

(* coinduction automation - internal use only *)
Ltac paco_cofix_auto :=
  let CIH := fresh "CIH" in cofix CIH; repeat intro;
  match goal with [H: _ |- _] => apply paco_observe in H; destruct H as [] end; do 2 econstructor;
  try (match goal with [H: _|-_] => apply H end); intros;
  lazymatch goal with [PR: _ |- _] => match goal with [H: _ |- _] => apply H in PR end end;
  repeat match goal with [ H : _ \/ _ |- _] => destruct H end; first [eauto; fail|eauto 10].

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
  revert x PR. cofix CIH.
  intros. apply paco_observe in PR. destruct PR as [].
  do 2 econstructor.
  - intros. specialize (LE x0 PR). destruct LE.
    + left. apply CIH, H.
    + right. apply LEr, H.
  - apply LEgf, SIM.
Qed.

Section Arg1.

Variable T0 : Type.
Variable gf : rel1 T0 -> rel1 T0.
Arguments gf : clear implicits.

Theorem paco_acc: forall
  l r (OBG: forall rr (INC: r <1= rr) (CIH: l <1= rr), l <1= paco gf rr),
  l <1= paco gf r.
Proof.
  intros; assert (SIM: paco gf (r \1/ l) x0) by eauto.
  clear PR; repeat (try left; do 2 paco_revert; paco_cofix_auto).
Qed.

Theorem paco_mon: monotone (paco gf).
Proof. paco_cofix_auto; repeat (left; do 2 paco_revert; paco_cofix_auto). Qed.

Theorem paco_mult_strong: forall r,
  paco gf (upaco gf r) <1= paco gf r.
Proof. paco_cofix_auto; repeat (left; do 2 paco_revert; paco_cofix_auto). Qed.

Corollary paco_mult: forall r,
  paco gf (paco gf r) <1= paco gf r.
Proof. intros; eapply paco_mult_strong, paco_mon; eauto. Qed.

Theorem paco_fold: forall r,
  gf (upaco gf r) <1= paco gf r.
Proof. intros; do 2 econstructor; [ |eauto]; eauto. Qed.

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
