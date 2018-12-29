Require Export paconotation pacotacuser.
Require Import pacotac paconotation_internal.
Set Implicit Arguments.
Set Primitive Projections.

(** ** Predicates of Arity 1
*)

Section Arg1_def.
Variable T0 : Type.
Variable gf : rel1 T0 -> rel1 T0.
Arguments gf : clear implicits.

CoInductive paco( r: rel1 T0) x0 : Prop :=
| paco_pfold pco
    (LE : pco <1= (paco r \1/ r))
    (SIM: gf pco x0)
.
Definition upaco( r: rel1 T0) := paco r \1/ r.
End Arg1_def.
Arguments paco [ T0 ].
Arguments upaco [ T0 ].
Hint Unfold upaco.

Section Arg1_2_def.
Variable T0 : Type.
Variable gf_0 gf_1 : rel1 T0 -> rel1 T0 -> rel1 T0.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.

CoInductive paco_2_0( r_0 r_1: rel1 T0) x0 : Prop :=
| paco_2_0_pfold pco_0 pco_1
    (LE : pco_0 <1= (paco_2_0 r_0 r_1 \1/ r_0))
    (LE : pco_1 <1= (paco_2_1 r_0 r_1 \1/ r_1))
    (SIM: gf_0 pco_0 pco_1 x0)
with paco_2_1( r_0 r_1: rel1 T0) x0 : Prop :=
| paco_2_1_pfold pco_0 pco_1
    (LE : pco_0 <1= (paco_2_0 r_0 r_1 \1/ r_0))
    (LE : pco_1 <1= (paco_2_1 r_0 r_1 \1/ r_1))
    (SIM: gf_1 pco_0 pco_1 x0)
.
Definition upaco_2_0( r_0 r_1: rel1 T0) := paco_2_0 r_0 r_1 \1/ r_0.
Definition upaco_2_1( r_0 r_1: rel1 T0) := paco_2_1 r_0 r_1 \1/ r_1.
End Arg1_2_def.
Arguments paco_2_0 [ T0 ].
Arguments upaco_2_0 [ T0 ].
Hint Unfold upaco_2_0.
Arguments paco_2_1 [ T0 ].
Arguments upaco_2_1 [ T0 ].
Hint Unfold upaco_2_1.

Section Arg1_3_def.
Variable T0 : Type.
Variable gf_0 gf_1 gf_2 : rel1 T0 -> rel1 T0 -> rel1 T0 -> rel1 T0.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.
Arguments gf_2 : clear implicits.

CoInductive paco_3_0( r_0 r_1 r_2: rel1 T0) x0 : Prop :=
| paco_3_0_pfold pco_0 pco_1 pco_2
    (LE : pco_0 <1= (paco_3_0 r_0 r_1 r_2 \1/ r_0))
    (LE : pco_1 <1= (paco_3_1 r_0 r_1 r_2 \1/ r_1))
    (LE : pco_2 <1= (paco_3_2 r_0 r_1 r_2 \1/ r_2))
    (SIM: gf_0 pco_0 pco_1 pco_2 x0)
with paco_3_1( r_0 r_1 r_2: rel1 T0) x0 : Prop :=
| paco_3_1_pfold pco_0 pco_1 pco_2
    (LE : pco_0 <1= (paco_3_0 r_0 r_1 r_2 \1/ r_0))
    (LE : pco_1 <1= (paco_3_1 r_0 r_1 r_2 \1/ r_1))
    (LE : pco_2 <1= (paco_3_2 r_0 r_1 r_2 \1/ r_2))
    (SIM: gf_1 pco_0 pco_1 pco_2 x0)
with paco_3_2( r_0 r_1 r_2: rel1 T0) x0 : Prop :=
| paco_3_2_pfold pco_0 pco_1 pco_2
    (LE : pco_0 <1= (paco_3_0 r_0 r_1 r_2 \1/ r_0))
    (LE : pco_1 <1= (paco_3_1 r_0 r_1 r_2 \1/ r_1))
    (LE : pco_2 <1= (paco_3_2 r_0 r_1 r_2 \1/ r_2))
    (SIM: gf_2 pco_0 pco_1 pco_2 x0)
.
Definition upaco_3_0( r_0 r_1 r_2: rel1 T0) := paco_3_0 r_0 r_1 r_2 \1/ r_0.
Definition upaco_3_1( r_0 r_1 r_2: rel1 T0) := paco_3_1 r_0 r_1 r_2 \1/ r_1.
Definition upaco_3_2( r_0 r_1 r_2: rel1 T0) := paco_3_2 r_0 r_1 r_2 \1/ r_2.
End Arg1_3_def.
Arguments paco_3_0 [ T0 ].
Arguments upaco_3_0 [ T0 ].
Hint Unfold upaco_3_0.
Arguments paco_3_1 [ T0 ].
Arguments upaco_3_1 [ T0 ].
Hint Unfold upaco_3_1.
Arguments paco_3_2 [ T0 ].
Arguments upaco_3_2 [ T0 ].
Hint Unfold upaco_3_2.

(* Less than or equal - internal use only *)
Notation "p <_paco_1= q" :=
  (forall _paco_x0 (PR: p _paco_x0 : Prop), q _paco_x0 : Prop)
  (at level 50, no associativity).

(** 1 Mutual Coinduction *)

Section Arg1_1.

Definition monotone T0 (gf: rel1 T0 -> rel1 T0) :=
  forall x0 r r' (IN: gf r x0) (LE: r <1= r'), gf r' x0.

Definition _monotone T0 (gf: rel1 T0 -> rel1 T0) :=
  forall r r'(LE: r <1= r'), gf r <1== gf r'.

Lemma monotone_eq T0 (gf: rel1 T0 -> rel1 T0) :
  monotone gf <-> _monotone gf.
Proof. unfold monotone, _monotone, le1. split; eauto. Qed.

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
Proof. intros; econstructor; [ |eauto]; eauto. Qed.

Theorem paco_unfold: forall (MON: monotone gf) r,
  paco gf r <1= gf (upaco gf r).
Proof. unfold monotone; intros; destruct PR; eauto. Qed.

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
  unfold le1. repeat_intros 1.
  eapply paco_unfold; apply monotone_eq; eauto.
Qed.

End Arg1_1.

Hint Unfold monotone.
Hint Resolve paco_fold.

Arguments paco_acc            [ T0 ].
Arguments paco_mon            [ T0 ].
Arguments paco_mult_strong    [ T0 ].
Arguments paco_mult           [ T0 ].
Arguments paco_fold           [ T0 ].
Arguments paco_unfold         [ T0 ].

(** 2 Mutual Coinduction *)

Section Arg1_2.

Definition monotone_2 T0 (gf: rel1 T0 -> rel1 T0 -> rel1 T0) :=
  forall x0 r_0 r_1 r'_0 r'_1 (IN: gf r_0 r_1 x0) (LE_0: r_0 <1= r'_0)(LE_1: r_1 <1= r'_1), gf r'_0 r'_1 x0.

Definition _monotone_2 T0 (gf: rel1 T0 -> rel1 T0 -> rel1 T0) :=
  forall r_0 r_1 r'_0 r'_1(LE_0: r_0 <1= r'_0)(LE_1: r_1 <1= r'_1), gf r_0 r_1 <1== gf r'_0 r'_1.

Lemma monotone_2_eq T0 (gf: rel1 T0 -> rel1 T0 -> rel1 T0) :
  monotone_2 gf <-> _monotone_2 gf.
Proof. unfold monotone_2, _monotone_2, le1. split; eauto. Qed.

Variable T0 : Type.
Variable gf_0 gf_1 : rel1 T0 -> rel1 T0 -> rel1 T0.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.

Theorem paco_2_0_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_0 <1= rr) (CIH: l <1= rr), l <1= paco_2_0 gf_0 gf_1 rr r_1),
  l <1= paco_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  intros; assert (SIM: paco_2_0 gf_0 gf_1 (r_0 \1/ l) r_1 x0) by eauto.
  clear PR; repeat (try left; do 2 paco_revert; paco_cofix_auto).
Qed.

Theorem paco_2_1_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_1 <1= rr) (CIH: l <1= rr), l <1= paco_2_1 gf_0 gf_1 r_0 rr),
  l <1= paco_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  intros; assert (SIM: paco_2_1 gf_0 gf_1 r_0 (r_1 \1/ l) x0) by eauto.
  clear PR; repeat (try left; do 2 paco_revert; paco_cofix_auto).
Qed.

Theorem paco_2_0_mon: monotone_2 (paco_2_0 gf_0 gf_1).
Proof. paco_cofix_auto; repeat (left; do 2 paco_revert; paco_cofix_auto). Qed.

Theorem paco_2_1_mon: monotone_2 (paco_2_1 gf_0 gf_1).
Proof. paco_cofix_auto; repeat (left; do 2 paco_revert; paco_cofix_auto). Qed.

Theorem paco_2_0_mult_strong: forall r_0 r_1,
  paco_2_0 gf_0 gf_1 (upaco_2_0 gf_0 gf_1 r_0 r_1) (upaco_2_1 gf_0 gf_1 r_0 r_1) <1= paco_2_0 gf_0 gf_1 r_0 r_1.
Proof. paco_cofix_auto; repeat (left; do 2 paco_revert; paco_cofix_auto). Qed.

Theorem paco_2_1_mult_strong: forall r_0 r_1,
  paco_2_1 gf_0 gf_1 (upaco_2_0 gf_0 gf_1 r_0 r_1) (upaco_2_1 gf_0 gf_1 r_0 r_1) <1= paco_2_1 gf_0 gf_1 r_0 r_1.
Proof. paco_cofix_auto; repeat (left; do 2 paco_revert; paco_cofix_auto). Qed.

Corollary paco_2_0_mult: forall r_0 r_1,
  paco_2_0 gf_0 gf_1 (paco_2_0 gf_0 gf_1 r_0 r_1) (paco_2_1 gf_0 gf_1 r_0 r_1) <1= paco_2_0 gf_0 gf_1 r_0 r_1.
Proof. intros; eapply paco_2_0_mult_strong, paco_2_0_mon; eauto. Qed.

Corollary paco_2_1_mult: forall r_0 r_1,
  paco_2_1 gf_0 gf_1 (paco_2_0 gf_0 gf_1 r_0 r_1) (paco_2_1 gf_0 gf_1 r_0 r_1) <1= paco_2_1 gf_0 gf_1 r_0 r_1.
Proof. intros; eapply paco_2_1_mult_strong, paco_2_1_mon; eauto. Qed.

Theorem paco_2_0_fold: forall r_0 r_1,
  gf_0 (upaco_2_0 gf_0 gf_1 r_0 r_1) (upaco_2_1 gf_0 gf_1 r_0 r_1) <1= paco_2_0 gf_0 gf_1 r_0 r_1.
Proof. intros; econstructor; [ | |eauto]; eauto. Qed.

Theorem paco_2_1_fold: forall r_0 r_1,
  gf_1 (upaco_2_0 gf_0 gf_1 r_0 r_1) (upaco_2_1 gf_0 gf_1 r_0 r_1) <1= paco_2_1 gf_0 gf_1 r_0 r_1.
Proof. intros; econstructor; [ | |eauto]; eauto. Qed.

Theorem paco_2_0_unfold: forall (MON: monotone_2 gf_0) (MON: monotone_2 gf_1) r_0 r_1,
  paco_2_0 gf_0 gf_1 r_0 r_1 <1= gf_0 (upaco_2_0 gf_0 gf_1 r_0 r_1) (upaco_2_1 gf_0 gf_1 r_0 r_1).
Proof. unfold monotone_2; intros; destruct PR; eauto. Qed.

Theorem paco_2_1_unfold: forall (MON: monotone_2 gf_0) (MON: monotone_2 gf_1) r_0 r_1,
  paco_2_1 gf_0 gf_1 r_0 r_1 <1= gf_1 (upaco_2_0 gf_0 gf_1 r_0 r_1) (upaco_2_1 gf_0 gf_1 r_0 r_1).
Proof. unfold monotone_2; intros; destruct PR; eauto. Qed.

Theorem _paco_2_0_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_0 <1== rr) (CIH: l <1== rr), l <1== paco_2_0 gf_0 gf_1 rr r_1),
  l <1== paco_2_0 gf_0 gf_1 r_0 r_1.
Proof. unfold le1. eapply paco_2_0_acc. Qed.

Theorem _paco_2_1_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_1 <1== rr) (CIH: l <1== rr), l <1== paco_2_1 gf_0 gf_1 r_0 rr),
  l <1== paco_2_1 gf_0 gf_1 r_0 r_1.
Proof. unfold le1. eapply paco_2_1_acc. Qed.

Theorem _paco_2_0_mon: _monotone_2 (paco_2_0 gf_0 gf_1).
Proof. apply monotone_2_eq. eapply paco_2_0_mon. Qed.

Theorem _paco_2_1_mon: _monotone_2 (paco_2_1 gf_0 gf_1).
Proof. apply monotone_2_eq. eapply paco_2_1_mon. Qed.

Theorem _paco_2_0_mult_strong: forall r_0 r_1,
  paco_2_0 gf_0 gf_1 (upaco_2_0 gf_0 gf_1 r_0 r_1) (upaco_2_1 gf_0 gf_1 r_0 r_1) <1== paco_2_0 gf_0 gf_1 r_0 r_1.
Proof. unfold le1. eapply paco_2_0_mult_strong. Qed.

Theorem _paco_2_1_mult_strong: forall r_0 r_1,
  paco_2_1 gf_0 gf_1 (upaco_2_0 gf_0 gf_1 r_0 r_1) (upaco_2_1 gf_0 gf_1 r_0 r_1) <1== paco_2_1 gf_0 gf_1 r_0 r_1.
Proof. unfold le1. eapply paco_2_1_mult_strong. Qed.

Theorem _paco_2_0_fold: forall r_0 r_1,
  gf_0 (upaco_2_0 gf_0 gf_1 r_0 r_1) (upaco_2_1 gf_0 gf_1 r_0 r_1) <1== paco_2_0 gf_0 gf_1 r_0 r_1.
Proof. unfold le1. eapply paco_2_0_fold. Qed.

Theorem _paco_2_1_fold: forall r_0 r_1,
  gf_1 (upaco_2_0 gf_0 gf_1 r_0 r_1) (upaco_2_1 gf_0 gf_1 r_0 r_1) <1== paco_2_1 gf_0 gf_1 r_0 r_1.
Proof. unfold le1. eapply paco_2_1_fold. Qed.

Theorem _paco_2_0_unfold: forall (MON: _monotone_2 gf_0) (MON: _monotone_2 gf_1) r_0 r_1,
  paco_2_0 gf_0 gf_1 r_0 r_1 <1== gf_0 (upaco_2_0 gf_0 gf_1 r_0 r_1) (upaco_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  unfold le1. repeat_intros 2.
  eapply paco_2_0_unfold; apply monotone_2_eq; eauto.
Qed.

Theorem _paco_2_1_unfold: forall (MON: _monotone_2 gf_0) (MON: _monotone_2 gf_1) r_0 r_1,
  paco_2_1 gf_0 gf_1 r_0 r_1 <1== gf_1 (upaco_2_0 gf_0 gf_1 r_0 r_1) (upaco_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  unfold le1. repeat_intros 2.
  eapply paco_2_1_unfold; apply monotone_2_eq; eauto.
Qed.

End Arg1_2.

Hint Unfold monotone_2.
Hint Resolve paco_2_0_fold.
Hint Resolve paco_2_1_fold.

Arguments paco_2_0_acc            [ T0 ].
Arguments paco_2_1_acc            [ T0 ].
Arguments paco_2_0_mon            [ T0 ].
Arguments paco_2_1_mon            [ T0 ].
Arguments paco_2_0_mult_strong    [ T0 ].
Arguments paco_2_1_mult_strong    [ T0 ].
Arguments paco_2_0_mult           [ T0 ].
Arguments paco_2_1_mult           [ T0 ].
Arguments paco_2_0_fold           [ T0 ].
Arguments paco_2_1_fold           [ T0 ].
Arguments paco_2_0_unfold         [ T0 ].
Arguments paco_2_1_unfold         [ T0 ].

(** 3 Mutual Coinduction *)

Section Arg1_3.

Definition monotone_3 T0 (gf: rel1 T0 -> rel1 T0 -> rel1 T0 -> rel1 T0) :=
  forall x0 r_0 r_1 r_2 r'_0 r'_1 r'_2 (IN: gf r_0 r_1 r_2 x0) (LE_0: r_0 <1= r'_0)(LE_1: r_1 <1= r'_1)(LE_2: r_2 <1= r'_2), gf r'_0 r'_1 r'_2 x0.

Definition _monotone_3 T0 (gf: rel1 T0 -> rel1 T0 -> rel1 T0 -> rel1 T0) :=
  forall r_0 r_1 r_2 r'_0 r'_1 r'_2(LE_0: r_0 <1= r'_0)(LE_1: r_1 <1= r'_1)(LE_2: r_2 <1= r'_2), gf r_0 r_1 r_2 <1== gf r'_0 r'_1 r'_2.

Lemma monotone_3_eq T0 (gf: rel1 T0 -> rel1 T0 -> rel1 T0 -> rel1 T0) :
  monotone_3 gf <-> _monotone_3 gf.
Proof. unfold monotone_3, _monotone_3, le1. split; eauto. Qed.

Variable T0 : Type.
Variable gf_0 gf_1 gf_2 : rel1 T0 -> rel1 T0 -> rel1 T0 -> rel1 T0.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.
Arguments gf_2 : clear implicits.

Theorem paco_3_0_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_0 <1= rr) (CIH: l <1= rr), l <1= paco_3_0 gf_0 gf_1 gf_2 rr r_1 r_2),
  l <1= paco_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros; assert (SIM: paco_3_0 gf_0 gf_1 gf_2 (r_0 \1/ l) r_1 r_2 x0) by eauto.
  clear PR; repeat (try left; do 2 paco_revert; paco_cofix_auto).
Qed.

Theorem paco_3_1_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_1 <1= rr) (CIH: l <1= rr), l <1= paco_3_1 gf_0 gf_1 gf_2 r_0 rr r_2),
  l <1= paco_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros; assert (SIM: paco_3_1 gf_0 gf_1 gf_2 r_0 (r_1 \1/ l) r_2 x0) by eauto.
  clear PR; repeat (try left; do 2 paco_revert; paco_cofix_auto).
Qed.

Theorem paco_3_2_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_2 <1= rr) (CIH: l <1= rr), l <1= paco_3_2 gf_0 gf_1 gf_2 r_0 r_1 rr),
  l <1= paco_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros; assert (SIM: paco_3_2 gf_0 gf_1 gf_2 r_0 r_1 (r_2 \1/ l) x0) by eauto.
  clear PR; repeat (try left; do 2 paco_revert; paco_cofix_auto).
Qed.

Theorem paco_3_0_mon: monotone_3 (paco_3_0 gf_0 gf_1 gf_2).
Proof. paco_cofix_auto; repeat (left; do 2 paco_revert; paco_cofix_auto). Qed.

Theorem paco_3_1_mon: monotone_3 (paco_3_1 gf_0 gf_1 gf_2).
Proof. paco_cofix_auto; repeat (left; do 2 paco_revert; paco_cofix_auto). Qed.

Theorem paco_3_2_mon: monotone_3 (paco_3_2 gf_0 gf_1 gf_2).
Proof. paco_cofix_auto; repeat (left; do 2 paco_revert; paco_cofix_auto). Qed.

Theorem paco_3_0_mult_strong: forall r_0 r_1 r_2,
  paco_3_0 gf_0 gf_1 gf_2 (upaco_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <1= paco_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. paco_cofix_auto; repeat (left; do 2 paco_revert; paco_cofix_auto). Qed.

Theorem paco_3_1_mult_strong: forall r_0 r_1 r_2,
  paco_3_1 gf_0 gf_1 gf_2 (upaco_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <1= paco_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. paco_cofix_auto; repeat (left; do 2 paco_revert; paco_cofix_auto). Qed.

Theorem paco_3_2_mult_strong: forall r_0 r_1 r_2,
  paco_3_2 gf_0 gf_1 gf_2 (upaco_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <1= paco_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. paco_cofix_auto; repeat (left; do 2 paco_revert; paco_cofix_auto). Qed.

Corollary paco_3_0_mult: forall r_0 r_1 r_2,
  paco_3_0 gf_0 gf_1 gf_2 (paco_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <1= paco_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco_3_0_mult_strong, paco_3_0_mon; eauto. Qed.

Corollary paco_3_1_mult: forall r_0 r_1 r_2,
  paco_3_1 gf_0 gf_1 gf_2 (paco_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <1= paco_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco_3_1_mult_strong, paco_3_1_mon; eauto. Qed.

Corollary paco_3_2_mult: forall r_0 r_1 r_2,
  paco_3_2 gf_0 gf_1 gf_2 (paco_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <1= paco_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco_3_2_mult_strong, paco_3_2_mon; eauto. Qed.

Theorem paco_3_0_fold: forall r_0 r_1 r_2,
  gf_0 (upaco_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <1= paco_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; econstructor; [ | | |eauto]; eauto. Qed.

Theorem paco_3_1_fold: forall r_0 r_1 r_2,
  gf_1 (upaco_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <1= paco_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; econstructor; [ | | |eauto]; eauto. Qed.

Theorem paco_3_2_fold: forall r_0 r_1 r_2,
  gf_2 (upaco_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <1= paco_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; econstructor; [ | | |eauto]; eauto. Qed.

Theorem paco_3_0_unfold: forall (MON: monotone_3 gf_0) (MON: monotone_3 gf_1) (MON: monotone_3 gf_2) r_0 r_1 r_2,
  paco_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 <1= gf_0 (upaco_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof. unfold monotone_3; intros; destruct PR; eauto. Qed.

Theorem paco_3_1_unfold: forall (MON: monotone_3 gf_0) (MON: monotone_3 gf_1) (MON: monotone_3 gf_2) r_0 r_1 r_2,
  paco_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 <1= gf_1 (upaco_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof. unfold monotone_3; intros; destruct PR; eauto. Qed.

Theorem paco_3_2_unfold: forall (MON: monotone_3 gf_0) (MON: monotone_3 gf_1) (MON: monotone_3 gf_2) r_0 r_1 r_2,
  paco_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 <1= gf_2 (upaco_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof. unfold monotone_3; intros; destruct PR; eauto. Qed.

Theorem _paco_3_0_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_0 <1== rr) (CIH: l <1== rr), l <1== paco_3_0 gf_0 gf_1 gf_2 rr r_1 r_2),
  l <1== paco_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. unfold le1. eapply paco_3_0_acc. Qed.

Theorem _paco_3_1_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_1 <1== rr) (CIH: l <1== rr), l <1== paco_3_1 gf_0 gf_1 gf_2 r_0 rr r_2),
  l <1== paco_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. unfold le1. eapply paco_3_1_acc. Qed.

Theorem _paco_3_2_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_2 <1== rr) (CIH: l <1== rr), l <1== paco_3_2 gf_0 gf_1 gf_2 r_0 r_1 rr),
  l <1== paco_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. unfold le1. eapply paco_3_2_acc. Qed.

Theorem _paco_3_0_mon: _monotone_3 (paco_3_0 gf_0 gf_1 gf_2).
Proof. apply monotone_3_eq. eapply paco_3_0_mon. Qed.

Theorem _paco_3_1_mon: _monotone_3 (paco_3_1 gf_0 gf_1 gf_2).
Proof. apply monotone_3_eq. eapply paco_3_1_mon. Qed.

Theorem _paco_3_2_mon: _monotone_3 (paco_3_2 gf_0 gf_1 gf_2).
Proof. apply monotone_3_eq. eapply paco_3_2_mon. Qed.

Theorem _paco_3_0_mult_strong: forall r_0 r_1 r_2,
  paco_3_0 gf_0 gf_1 gf_2 (upaco_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <1== paco_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. unfold le1. eapply paco_3_0_mult_strong. Qed.

Theorem _paco_3_1_mult_strong: forall r_0 r_1 r_2,
  paco_3_1 gf_0 gf_1 gf_2 (upaco_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <1== paco_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. unfold le1. eapply paco_3_1_mult_strong. Qed.

Theorem _paco_3_2_mult_strong: forall r_0 r_1 r_2,
  paco_3_2 gf_0 gf_1 gf_2 (upaco_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <1== paco_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. unfold le1. eapply paco_3_2_mult_strong. Qed.

Theorem _paco_3_0_fold: forall r_0 r_1 r_2,
  gf_0 (upaco_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <1== paco_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. unfold le1. eapply paco_3_0_fold. Qed.

Theorem _paco_3_1_fold: forall r_0 r_1 r_2,
  gf_1 (upaco_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <1== paco_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. unfold le1. eapply paco_3_1_fold. Qed.

Theorem _paco_3_2_fold: forall r_0 r_1 r_2,
  gf_2 (upaco_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <1== paco_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. unfold le1. eapply paco_3_2_fold. Qed.

Theorem _paco_3_0_unfold: forall (MON: _monotone_3 gf_0) (MON: _monotone_3 gf_1) (MON: _monotone_3 gf_2) r_0 r_1 r_2,
  paco_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 <1== gf_0 (upaco_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  unfold le1. repeat_intros 3.
  eapply paco_3_0_unfold; apply monotone_3_eq; eauto.
Qed.

Theorem _paco_3_1_unfold: forall (MON: _monotone_3 gf_0) (MON: _monotone_3 gf_1) (MON: _monotone_3 gf_2) r_0 r_1 r_2,
  paco_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 <1== gf_1 (upaco_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  unfold le1. repeat_intros 3.
  eapply paco_3_1_unfold; apply monotone_3_eq; eauto.
Qed.

Theorem _paco_3_2_unfold: forall (MON: _monotone_3 gf_0) (MON: _monotone_3 gf_1) (MON: _monotone_3 gf_2) r_0 r_1 r_2,
  paco_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 <1== gf_2 (upaco_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  unfold le1. repeat_intros 3.
  eapply paco_3_2_unfold; apply monotone_3_eq; eauto.
Qed.

End Arg1_3.

Hint Unfold monotone_3.
Hint Resolve paco_3_0_fold.
Hint Resolve paco_3_1_fold.
Hint Resolve paco_3_2_fold.

Arguments paco_3_0_acc            [ T0 ].
Arguments paco_3_1_acc            [ T0 ].
Arguments paco_3_2_acc            [ T0 ].
Arguments paco_3_0_mon            [ T0 ].
Arguments paco_3_1_mon            [ T0 ].
Arguments paco_3_2_mon            [ T0 ].
Arguments paco_3_0_mult_strong    [ T0 ].
Arguments paco_3_1_mult_strong    [ T0 ].
Arguments paco_3_2_mult_strong    [ T0 ].
Arguments paco_3_0_mult           [ T0 ].
Arguments paco_3_1_mult           [ T0 ].
Arguments paco_3_2_mult           [ T0 ].
Arguments paco_3_0_fold           [ T0 ].
Arguments paco_3_1_fold           [ T0 ].
Arguments paco_3_2_fold           [ T0 ].
Arguments paco_3_0_unfold         [ T0 ].
Arguments paco_3_1_unfold         [ T0 ].
Arguments paco_3_2_unfold         [ T0 ].

