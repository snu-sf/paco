Require Export paconotation pacotacuser.
Require Import paconotation_internal pacotac pacon.
Set Implicit Arguments.

Section PACO2.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.

Record sig2T :=
  exist2T { 
      proj2T0: @T0;
      proj2T1: @T1 proj2T0;
    }.

Definition uncurry2 (R: rel2 T0 T1): rel1 sig2T := fun x => R (proj2T0 x) (proj2T1 x).

Definition curry2 (R: rel1 sig2T): rel2 T0 T1 :=
  fun x0 x1 => R (exist2T x1).

Lemma uncurry_map2 r0 r1 (LE : r0 <2== r1) : uncurry2 r0 <1== uncurry2 r1.
Proof. intros [] H. apply LE. auto. Qed.

Lemma uncurry_map_rev2 r0 r1 (LE: uncurry2 r0 <1== uncurry2 r1) : r0 <2== r1.
Proof.
  repeat_intros 2. intros H. apply (LE (exist2T x1) H).
Qed.

Lemma curry_map2 r0 r1 (LE: r0 <1== r1) : curry2 r0 <2== curry2 r1.
Proof. 
  repeat_intros 2. intros H. apply (LE (exist2T x1) H).
Qed.

Lemma curry_map_rev2 r0 r1 (LE: curry2 r0 <2== curry2 r1) : r0 <1== r1.
Proof. 
  intros [] H. apply LE. apply H.
Qed.

Lemma uncurry_bij1_2 r : curry2 (uncurry2 r) <2== r.
Proof. unfold le2. repeat_intros 2; auto. Qed.

Lemma uncurry_bij2_2 r : r <2== curry2 (uncurry2 r).
Proof. unfold le2. repeat_intros 2; auto. Qed.

Lemma curry_bij1_2 r : uncurry2 (curry2 r) <1== r.
Proof. intros []; auto. Qed.

Lemma curry_bij2_2 r : r <1== uncurry2 (curry2 r).
Proof. intros []; auto. Qed.

Lemma uncurry_adjoint1_2 r0 r1 (LE: uncurry2 r0 <1== r1) : r0 <2== curry2 r1.
Proof.
  apply uncurry_map_rev2. eapply le1_trans; [eauto|]. apply curry_bij2_2.
Qed.

Lemma uncurry_adjoint2_2 r0 r1 (LE: r0 <2== curry2 r1) : uncurry2 r0 <1== r1.
Proof.
  apply curry_map_rev2. eapply le2_trans; [|eauto]. apply uncurry_bij2_2.
Qed.

Lemma curry_adjoint1_2 r0 r1 (LE: curry2 r0 <2== r1) : r0 <1== uncurry2 r1.
Proof.
  apply curry_map_rev2. eapply le2_trans; [eauto|]. apply uncurry_bij2_2.
Qed.

Lemma curry_adjoint2_2 r0 r1 (LE: r0 <1== uncurry2 r1) : curry2 r0 <2== r1.
Proof.
  apply uncurry_map_rev2. eapply le1_trans; [|eauto]. apply curry_bij1_2.
Qed.

(** ** Predicates of Arity 2
*)

Section Arg2_def.
Variable gf : rel2 T0 T1 -> rel2 T0 T1.
Arguments gf : clear implicits.

Definition paco2( r: rel2 T0 T1) : rel2 T0 T1 :=
  curry2 (paco (fun R0 => uncurry2 (gf (curry2 R0))) (uncurry2 r)).

Definition upaco2( r: rel2 T0 T1) := paco2 r \2/ r.
End Arg2_def.
Arguments paco2 : clear implicits.
Arguments upaco2 : clear implicits.
Hint Unfold upaco2.

Section Arg2_2_def.
Variable gf_0 gf_1 : rel2 T0 T1 -> rel2 T0 T1 -> rel2 T0 T1.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.

Definition paco2_2_0( r_0 r_1: rel2 T0 T1) : rel2 T0 T1 :=
  curry2 (paco_2_0 (fun R0 R1 => uncurry2 (gf_0 (curry2 R0) (curry2 R1))) (fun R0 R1 => uncurry2 (gf_1 (curry2 R0) (curry2 R1))) (uncurry2 r_0) (uncurry2 r_1)).

Definition paco2_2_1( r_0 r_1: rel2 T0 T1) : rel2 T0 T1 :=
  curry2 (paco_2_1 (fun R0 R1 => uncurry2 (gf_0 (curry2 R0) (curry2 R1))) (fun R0 R1 => uncurry2 (gf_1 (curry2 R0) (curry2 R1))) (uncurry2 r_0) (uncurry2 r_1)).

Definition upaco2_2_0( r_0 r_1: rel2 T0 T1) := paco2_2_0 r_0 r_1 \2/ r_0.
Definition upaco2_2_1( r_0 r_1: rel2 T0 T1) := paco2_2_1 r_0 r_1 \2/ r_1.
End Arg2_2_def.
Arguments paco2_2_0 : clear implicits.
Arguments upaco2_2_0 : clear implicits.
Hint Unfold upaco2_2_0.
Arguments paco2_2_1 : clear implicits.
Arguments upaco2_2_1 : clear implicits.
Hint Unfold upaco2_2_1.

Section Arg2_3_def.
Variable gf_0 gf_1 gf_2 : rel2 T0 T1 -> rel2 T0 T1 -> rel2 T0 T1 -> rel2 T0 T1.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.
Arguments gf_2 : clear implicits.

Definition paco2_3_0( r_0 r_1 r_2: rel2 T0 T1) : rel2 T0 T1 :=
  curry2 (paco_3_0 (fun R0 R1 R2 => uncurry2 (gf_0 (curry2 R0) (curry2 R1) (curry2 R2))) (fun R0 R1 R2 => uncurry2 (gf_1 (curry2 R0) (curry2 R1) (curry2 R2))) (fun R0 R1 R2 => uncurry2 (gf_2 (curry2 R0) (curry2 R1) (curry2 R2))) (uncurry2 r_0) (uncurry2 r_1) (uncurry2 r_2)).

Definition paco2_3_1( r_0 r_1 r_2: rel2 T0 T1) : rel2 T0 T1 :=
  curry2 (paco_3_1 (fun R0 R1 R2 => uncurry2 (gf_0 (curry2 R0) (curry2 R1) (curry2 R2))) (fun R0 R1 R2 => uncurry2 (gf_1 (curry2 R0) (curry2 R1) (curry2 R2))) (fun R0 R1 R2 => uncurry2 (gf_2 (curry2 R0) (curry2 R1) (curry2 R2))) (uncurry2 r_0) (uncurry2 r_1) (uncurry2 r_2)).

Definition paco2_3_2( r_0 r_1 r_2: rel2 T0 T1) : rel2 T0 T1 :=
  curry2 (paco_3_2 (fun R0 R1 R2 => uncurry2 (gf_0 (curry2 R0) (curry2 R1) (curry2 R2))) (fun R0 R1 R2 => uncurry2 (gf_1 (curry2 R0) (curry2 R1) (curry2 R2))) (fun R0 R1 R2 => uncurry2 (gf_2 (curry2 R0) (curry2 R1) (curry2 R2))) (uncurry2 r_0) (uncurry2 r_1) (uncurry2 r_2)).

Definition upaco2_3_0( r_0 r_1 r_2: rel2 T0 T1) := paco2_3_0 r_0 r_1 r_2 \2/ r_0.
Definition upaco2_3_1( r_0 r_1 r_2: rel2 T0 T1) := paco2_3_1 r_0 r_1 r_2 \2/ r_1.
Definition upaco2_3_2( r_0 r_1 r_2: rel2 T0 T1) := paco2_3_2 r_0 r_1 r_2 \2/ r_2.
End Arg2_3_def.
Arguments paco2_3_0 : clear implicits.
Arguments upaco2_3_0 : clear implicits.
Hint Unfold upaco2_3_0.
Arguments paco2_3_1 : clear implicits.
Arguments upaco2_3_1 : clear implicits.
Hint Unfold upaco2_3_1.
Arguments paco2_3_2 : clear implicits.
Arguments upaco2_3_2 : clear implicits.
Hint Unfold upaco2_3_2.

(** 1 Mutual Coinduction *)

Section Arg2_1.

Definition monotone2 (gf: rel2 T0 T1 -> rel2 T0 T1) :=
  forall x0 x1 r r' (IN: gf r x0 x1) (LE: r <2= r'), gf r' x0 x1.

Definition _monotone2 (gf: rel2 T0 T1 -> rel2 T0 T1) :=
  forall r r'(LE: r <2= r'), gf r <2== gf r'.

Lemma monotone2_eq (gf: rel2 T0 T1 -> rel2 T0 T1) :
  monotone2 gf <-> _monotone2 gf.
Proof. unfold monotone2, _monotone2, le2. split; eauto. Qed.

Lemma monotone2_map (gf: rel2 T0 T1 -> rel2 T0 T1)
      (MON: _monotone2 gf) :
  _monotone (fun R0 => uncurry2 (gf (curry2 R0))).
Proof.
  repeat_intros 3. apply uncurry_map2. apply MON; apply curry_map2; auto.
Qed.

Variable gf : rel2 T0 T1 -> rel2 T0 T1.
Arguments gf : clear implicits.

Theorem _paco2_mon: _monotone2 (paco2 gf).
Proof.
  repeat_intros 3. eapply curry_map2, _paco_mon; apply uncurry_map2; auto.
Qed.

Theorem _paco2_acc: forall
  l r (OBG: forall rr (INC: r <2== rr) (CIH: l <2== rr), l <2== paco2 gf rr),
  l <2== paco2 gf r.
Proof.
  intros. apply uncurry_adjoint1_2.
  eapply _paco_acc. intros.
  apply uncurry_adjoint1_2 in INC. apply uncurry_adjoint1_2 in CIH.
  apply uncurry_adjoint2_2.
  eapply le2_trans. eapply (OBG _ INC CIH).
  apply curry_map2.
  apply _paco_mon; try apply le1_refl; apply curry_bij1_2.
Qed.

Theorem _paco2_mult_strong: forall r,
  paco2 gf (upaco2 gf r) <2== paco2 gf r.
Proof.
  intros. apply curry_map2.
  eapply le1_trans; [| eapply _paco_mult_strong].
  apply _paco_mon; intros []; eauto.
Qed.

Theorem _paco2_fold: forall r,
  gf (upaco2 gf r) <2== paco2 gf r.
Proof.
  intros. apply uncurry_adjoint1_2.
  eapply le1_trans; [| apply _paco_fold]. apply le1_refl.
Qed.

Theorem _paco2_unfold: forall (MON: _monotone2 gf) r,
  paco2 gf r <2== gf (upaco2 gf r).
Proof.
  intros. apply curry_adjoint2_2.
  eapply _paco_unfold; apply monotone2_map; auto.
Qed.

Theorem paco2_acc: forall
  l r (OBG: forall rr (INC: r <2= rr) (CIH: l <2= rr), l <2= paco2 gf rr),
  l <2= paco2 gf r.
Proof.
  apply _paco2_acc.
Qed.

Theorem paco2_mon: monotone2 (paco2 gf).
Proof.
  apply monotone2_eq.
  apply _paco2_mon.
Qed.

Theorem paco2_mult_strong: forall r,
  paco2 gf (upaco2 gf r) <2= paco2 gf r.
Proof.
  apply _paco2_mult_strong.
Qed.

Corollary paco2_mult: forall r,
  paco2 gf (paco2 gf r) <2= paco2 gf r.
Proof. intros; eapply paco2_mult_strong, paco2_mon; eauto. Qed.

Theorem paco2_fold: forall r,
  gf (upaco2 gf r) <2= paco2 gf r.
Proof.
  apply _paco2_fold.
Qed.

Theorem paco2_unfold: forall (MON: monotone2 gf) r,
  paco2 gf r <2= gf (upaco2 gf r).
Proof.
  repeat_intros 1. eapply _paco2_unfold; apply monotone2_eq; auto.
Qed.

End Arg2_1.

Arguments paco2_acc : clear implicits.
Arguments paco2_mon : clear implicits.
Arguments paco2_mult_strong : clear implicits.
Arguments paco2_mult : clear implicits.
Arguments paco2_fold : clear implicits.
Arguments paco2_unfold : clear implicits.

Global Instance paco2_inst  (gf : rel2 T0 T1->_) r x0 x1 : paco_class (paco2 gf r x0 x1) :=
{ pacoacc    := paco2_acc gf;
  pacomult   := paco2_mult gf;
  pacofold   := paco2_fold gf;
  pacounfold := paco2_unfold gf }.

(** 2 Mutual Coinduction *)

Section Arg2_2.

Definition monotone2_2 (gf: rel2 T0 T1 -> rel2 T0 T1 -> rel2 T0 T1) :=
  forall x0 x1 r_0 r_1 r'_0 r'_1 (IN: gf r_0 r_1 x0 x1) (LE_0: r_0 <2= r'_0)(LE_1: r_1 <2= r'_1), gf r'_0 r'_1 x0 x1.

Definition _monotone2_2 (gf: rel2 T0 T1 -> rel2 T0 T1 -> rel2 T0 T1) :=
  forall r_0 r_1 r'_0 r'_1(LE_0: r_0 <2= r'_0)(LE_1: r_1 <2= r'_1), gf r_0 r_1 <2== gf r'_0 r'_1.

Lemma monotone2_2_eq (gf: rel2 T0 T1 -> rel2 T0 T1 -> rel2 T0 T1) :
  monotone2_2 gf <-> _monotone2_2 gf.
Proof. unfold monotone2_2, _monotone2_2, le2. split; eauto. Qed.

Lemma monotone2_2_map (gf: rel2 T0 T1 -> rel2 T0 T1 -> rel2 T0 T1)
      (MON: _monotone2_2 gf) :
  _monotone_2 (fun R0 R1 => uncurry2 (gf (curry2 R0) (curry2 R1))).
Proof.
  repeat_intros 6. apply uncurry_map2. apply MON; apply curry_map2; auto.
Qed.

Variable gf_0 gf_1 : rel2 T0 T1 -> rel2 T0 T1 -> rel2 T0 T1.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.

Theorem _paco2_2_0_mon: _monotone2_2 (paco2_2_0 gf_0 gf_1).
Proof.
  repeat_intros 6. eapply curry_map2, _paco_2_0_mon; apply uncurry_map2; auto.
Qed.

Theorem _paco2_2_1_mon: _monotone2_2 (paco2_2_1 gf_0 gf_1).
Proof.
  repeat_intros 6. eapply curry_map2, _paco_2_1_mon; apply uncurry_map2; auto.
Qed.

Theorem _paco2_2_0_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_0 <2== rr) (CIH: l <2== rr), l <2== paco2_2_0 gf_0 gf_1 rr r_1),
  l <2== paco2_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_2.
  eapply _paco_2_0_acc. intros.
  apply uncurry_adjoint1_2 in INC. apply uncurry_adjoint1_2 in CIH.
  apply uncurry_adjoint2_2.
  eapply le2_trans. eapply (OBG _ INC CIH).
  apply curry_map2.
  apply _paco_2_0_mon; try apply le1_refl; apply curry_bij1_2.
Qed.

Theorem _paco2_2_1_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_1 <2== rr) (CIH: l <2== rr), l <2== paco2_2_1 gf_0 gf_1 r_0 rr),
  l <2== paco2_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_2.
  eapply _paco_2_1_acc. intros.
  apply uncurry_adjoint1_2 in INC. apply uncurry_adjoint1_2 in CIH.
  apply uncurry_adjoint2_2.
  eapply le2_trans. eapply (OBG _ INC CIH).
  apply curry_map2.
  apply _paco_2_1_mon; try apply le1_refl; apply curry_bij1_2.
Qed.

Theorem _paco2_2_0_mult_strong: forall r_0 r_1,
  paco2_2_0 gf_0 gf_1 (upaco2_2_0 gf_0 gf_1 r_0 r_1) (upaco2_2_1 gf_0 gf_1 r_0 r_1) <2== paco2_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply curry_map2.
  eapply le1_trans; [| eapply _paco_2_0_mult_strong].
  apply _paco_2_0_mon; intros []; eauto.
Qed.

Theorem _paco2_2_1_mult_strong: forall r_0 r_1,
  paco2_2_1 gf_0 gf_1 (upaco2_2_0 gf_0 gf_1 r_0 r_1) (upaco2_2_1 gf_0 gf_1 r_0 r_1) <2== paco2_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply curry_map2.
  eapply le1_trans; [| eapply _paco_2_1_mult_strong].
  apply _paco_2_1_mon; intros []; eauto.
Qed.

Theorem _paco2_2_0_fold: forall r_0 r_1,
  gf_0 (upaco2_2_0 gf_0 gf_1 r_0 r_1) (upaco2_2_1 gf_0 gf_1 r_0 r_1) <2== paco2_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_2.
  eapply le1_trans; [| apply _paco_2_0_fold]. apply le1_refl.
Qed.

Theorem _paco2_2_1_fold: forall r_0 r_1,
  gf_1 (upaco2_2_0 gf_0 gf_1 r_0 r_1) (upaco2_2_1 gf_0 gf_1 r_0 r_1) <2== paco2_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_2.
  eapply le1_trans; [| apply _paco_2_1_fold]. apply le1_refl.
Qed.

Theorem _paco2_2_0_unfold: forall (MON: _monotone2_2 gf_0) (MON: _monotone2_2 gf_1) r_0 r_1,
  paco2_2_0 gf_0 gf_1 r_0 r_1 <2== gf_0 (upaco2_2_0 gf_0 gf_1 r_0 r_1) (upaco2_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  intros. apply curry_adjoint2_2.
  eapply _paco_2_0_unfold; apply monotone2_2_map; auto.
Qed.

Theorem _paco2_2_1_unfold: forall (MON: _monotone2_2 gf_0) (MON: _monotone2_2 gf_1) r_0 r_1,
  paco2_2_1 gf_0 gf_1 r_0 r_1 <2== gf_1 (upaco2_2_0 gf_0 gf_1 r_0 r_1) (upaco2_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  intros. apply curry_adjoint2_2.
  eapply _paco_2_1_unfold; apply monotone2_2_map; auto.
Qed.

Theorem paco2_2_0_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_0 <2= rr) (CIH: l <2= rr), l <2= paco2_2_0 gf_0 gf_1 rr r_1),
  l <2= paco2_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco2_2_0_acc.
Qed.

Theorem paco2_2_1_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_1 <2= rr) (CIH: l <2= rr), l <2= paco2_2_1 gf_0 gf_1 r_0 rr),
  l <2= paco2_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco2_2_1_acc.
Qed.

Theorem paco2_2_0_mon: monotone2_2 (paco2_2_0 gf_0 gf_1).
Proof.
  apply monotone2_2_eq.
  apply _paco2_2_0_mon.
Qed.

Theorem paco2_2_1_mon: monotone2_2 (paco2_2_1 gf_0 gf_1).
Proof.
  apply monotone2_2_eq.
  apply _paco2_2_1_mon.
Qed.

Theorem paco2_2_0_mult_strong: forall r_0 r_1,
  paco2_2_0 gf_0 gf_1 (upaco2_2_0 gf_0 gf_1 r_0 r_1) (upaco2_2_1 gf_0 gf_1 r_0 r_1) <2= paco2_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco2_2_0_mult_strong.
Qed.

Theorem paco2_2_1_mult_strong: forall r_0 r_1,
  paco2_2_1 gf_0 gf_1 (upaco2_2_0 gf_0 gf_1 r_0 r_1) (upaco2_2_1 gf_0 gf_1 r_0 r_1) <2= paco2_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco2_2_1_mult_strong.
Qed.

Corollary paco2_2_0_mult: forall r_0 r_1,
  paco2_2_0 gf_0 gf_1 (paco2_2_0 gf_0 gf_1 r_0 r_1) (paco2_2_1 gf_0 gf_1 r_0 r_1) <2= paco2_2_0 gf_0 gf_1 r_0 r_1.
Proof. intros; eapply paco2_2_0_mult_strong, paco2_2_0_mon; eauto. Qed.

Corollary paco2_2_1_mult: forall r_0 r_1,
  paco2_2_1 gf_0 gf_1 (paco2_2_0 gf_0 gf_1 r_0 r_1) (paco2_2_1 gf_0 gf_1 r_0 r_1) <2= paco2_2_1 gf_0 gf_1 r_0 r_1.
Proof. intros; eapply paco2_2_1_mult_strong, paco2_2_1_mon; eauto. Qed.

Theorem paco2_2_0_fold: forall r_0 r_1,
  gf_0 (upaco2_2_0 gf_0 gf_1 r_0 r_1) (upaco2_2_1 gf_0 gf_1 r_0 r_1) <2= paco2_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco2_2_0_fold.
Qed.

Theorem paco2_2_1_fold: forall r_0 r_1,
  gf_1 (upaco2_2_0 gf_0 gf_1 r_0 r_1) (upaco2_2_1 gf_0 gf_1 r_0 r_1) <2= paco2_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco2_2_1_fold.
Qed.

Theorem paco2_2_0_unfold: forall (MON: monotone2_2 gf_0) (MON: monotone2_2 gf_1) r_0 r_1,
  paco2_2_0 gf_0 gf_1 r_0 r_1 <2= gf_0 (upaco2_2_0 gf_0 gf_1 r_0 r_1) (upaco2_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  repeat_intros 2. eapply _paco2_2_0_unfold; apply monotone2_2_eq; auto.
Qed.

Theorem paco2_2_1_unfold: forall (MON: monotone2_2 gf_0) (MON: monotone2_2 gf_1) r_0 r_1,
  paco2_2_1 gf_0 gf_1 r_0 r_1 <2= gf_1 (upaco2_2_0 gf_0 gf_1 r_0 r_1) (upaco2_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  repeat_intros 2. eapply _paco2_2_1_unfold; apply monotone2_2_eq; auto.
Qed.

End Arg2_2.

Arguments paco2_2_0_acc : clear implicits.
Arguments paco2_2_1_acc : clear implicits.
Arguments paco2_2_0_mon : clear implicits.
Arguments paco2_2_1_mon : clear implicits.
Arguments paco2_2_0_mult_strong : clear implicits.
Arguments paco2_2_1_mult_strong : clear implicits.
Arguments paco2_2_0_mult : clear implicits.
Arguments paco2_2_1_mult : clear implicits.
Arguments paco2_2_0_fold : clear implicits.
Arguments paco2_2_1_fold : clear implicits.
Arguments paco2_2_0_unfold : clear implicits.
Arguments paco2_2_1_unfold : clear implicits.

Global Instance paco2_2_0_inst  (gf_0 gf_1 : rel2 T0 T1->_) r_0 r_1 x0 x1 : paco_class (paco2_2_0 gf_0 gf_1 r_0 r_1 x0 x1) :=
{ pacoacc    := paco2_2_0_acc gf_0 gf_1;
  pacomult   := paco2_2_0_mult gf_0 gf_1;
  pacofold   := paco2_2_0_fold gf_0 gf_1;
  pacounfold := paco2_2_0_unfold gf_0 gf_1 }.

Global Instance paco2_2_1_inst  (gf_0 gf_1 : rel2 T0 T1->_) r_0 r_1 x0 x1 : paco_class (paco2_2_1 gf_0 gf_1 r_0 r_1 x0 x1) :=
{ pacoacc    := paco2_2_1_acc gf_0 gf_1;
  pacomult   := paco2_2_1_mult gf_0 gf_1;
  pacofold   := paco2_2_1_fold gf_0 gf_1;
  pacounfold := paco2_2_1_unfold gf_0 gf_1 }.

(** 3 Mutual Coinduction *)

Section Arg2_3.

Definition monotone2_3 (gf: rel2 T0 T1 -> rel2 T0 T1 -> rel2 T0 T1 -> rel2 T0 T1) :=
  forall x0 x1 r_0 r_1 r_2 r'_0 r'_1 r'_2 (IN: gf r_0 r_1 r_2 x0 x1) (LE_0: r_0 <2= r'_0)(LE_1: r_1 <2= r'_1)(LE_2: r_2 <2= r'_2), gf r'_0 r'_1 r'_2 x0 x1.

Definition _monotone2_3 (gf: rel2 T0 T1 -> rel2 T0 T1 -> rel2 T0 T1 -> rel2 T0 T1) :=
  forall r_0 r_1 r_2 r'_0 r'_1 r'_2(LE_0: r_0 <2= r'_0)(LE_1: r_1 <2= r'_1)(LE_2: r_2 <2= r'_2), gf r_0 r_1 r_2 <2== gf r'_0 r'_1 r'_2.

Lemma monotone2_3_eq (gf: rel2 T0 T1 -> rel2 T0 T1 -> rel2 T0 T1 -> rel2 T0 T1) :
  monotone2_3 gf <-> _monotone2_3 gf.
Proof. unfold monotone2_3, _monotone2_3, le2. split; eauto. Qed.

Lemma monotone2_3_map (gf: rel2 T0 T1 -> rel2 T0 T1 -> rel2 T0 T1 -> rel2 T0 T1)
      (MON: _monotone2_3 gf) :
  _monotone_3 (fun R0 R1 R2 => uncurry2 (gf (curry2 R0) (curry2 R1) (curry2 R2))).
Proof.
  repeat_intros 9. apply uncurry_map2. apply MON; apply curry_map2; auto.
Qed.

Variable gf_0 gf_1 gf_2 : rel2 T0 T1 -> rel2 T0 T1 -> rel2 T0 T1 -> rel2 T0 T1.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.
Arguments gf_2 : clear implicits.

Theorem _paco2_3_0_mon: _monotone2_3 (paco2_3_0 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 9. eapply curry_map2, _paco_3_0_mon; apply uncurry_map2; auto.
Qed.

Theorem _paco2_3_1_mon: _monotone2_3 (paco2_3_1 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 9. eapply curry_map2, _paco_3_1_mon; apply uncurry_map2; auto.
Qed.

Theorem _paco2_3_2_mon: _monotone2_3 (paco2_3_2 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 9. eapply curry_map2, _paco_3_2_mon; apply uncurry_map2; auto.
Qed.

Theorem _paco2_3_0_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_0 <2== rr) (CIH: l <2== rr), l <2== paco2_3_0 gf_0 gf_1 gf_2 rr r_1 r_2),
  l <2== paco2_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_2.
  eapply _paco_3_0_acc. intros.
  apply uncurry_adjoint1_2 in INC. apply uncurry_adjoint1_2 in CIH.
  apply uncurry_adjoint2_2.
  eapply le2_trans. eapply (OBG _ INC CIH).
  apply curry_map2.
  apply _paco_3_0_mon; try apply le1_refl; apply curry_bij1_2.
Qed.

Theorem _paco2_3_1_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_1 <2== rr) (CIH: l <2== rr), l <2== paco2_3_1 gf_0 gf_1 gf_2 r_0 rr r_2),
  l <2== paco2_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_2.
  eapply _paco_3_1_acc. intros.
  apply uncurry_adjoint1_2 in INC. apply uncurry_adjoint1_2 in CIH.
  apply uncurry_adjoint2_2.
  eapply le2_trans. eapply (OBG _ INC CIH).
  apply curry_map2.
  apply _paco_3_1_mon; try apply le1_refl; apply curry_bij1_2.
Qed.

Theorem _paco2_3_2_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_2 <2== rr) (CIH: l <2== rr), l <2== paco2_3_2 gf_0 gf_1 gf_2 r_0 r_1 rr),
  l <2== paco2_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_2.
  eapply _paco_3_2_acc. intros.
  apply uncurry_adjoint1_2 in INC. apply uncurry_adjoint1_2 in CIH.
  apply uncurry_adjoint2_2.
  eapply le2_trans. eapply (OBG _ INC CIH).
  apply curry_map2.
  apply _paco_3_2_mon; try apply le1_refl; apply curry_bij1_2.
Qed.

Theorem _paco2_3_0_mult_strong: forall r_0 r_1 r_2,
  paco2_3_0 gf_0 gf_1 gf_2 (upaco2_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco2_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco2_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <2== paco2_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply curry_map2.
  eapply le1_trans; [| eapply _paco_3_0_mult_strong].
  apply _paco_3_0_mon; intros []; eauto.
Qed.

Theorem _paco2_3_1_mult_strong: forall r_0 r_1 r_2,
  paco2_3_1 gf_0 gf_1 gf_2 (upaco2_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco2_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco2_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <2== paco2_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply curry_map2.
  eapply le1_trans; [| eapply _paco_3_1_mult_strong].
  apply _paco_3_1_mon; intros []; eauto.
Qed.

Theorem _paco2_3_2_mult_strong: forall r_0 r_1 r_2,
  paco2_3_2 gf_0 gf_1 gf_2 (upaco2_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco2_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco2_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <2== paco2_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply curry_map2.
  eapply le1_trans; [| eapply _paco_3_2_mult_strong].
  apply _paco_3_2_mon; intros []; eauto.
Qed.

Theorem _paco2_3_0_fold: forall r_0 r_1 r_2,
  gf_0 (upaco2_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco2_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco2_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <2== paco2_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_2.
  eapply le1_trans; [| apply _paco_3_0_fold]. apply le1_refl.
Qed.

Theorem _paco2_3_1_fold: forall r_0 r_1 r_2,
  gf_1 (upaco2_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco2_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco2_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <2== paco2_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_2.
  eapply le1_trans; [| apply _paco_3_1_fold]. apply le1_refl.
Qed.

Theorem _paco2_3_2_fold: forall r_0 r_1 r_2,
  gf_2 (upaco2_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco2_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco2_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <2== paco2_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_2.
  eapply le1_trans; [| apply _paco_3_2_fold]. apply le1_refl.
Qed.

Theorem _paco2_3_0_unfold: forall (MON: _monotone2_3 gf_0) (MON: _monotone2_3 gf_1) (MON: _monotone2_3 gf_2) r_0 r_1 r_2,
  paco2_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 <2== gf_0 (upaco2_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco2_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco2_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  intros. apply curry_adjoint2_2.
  eapply _paco_3_0_unfold; apply monotone2_3_map; auto.
Qed.

Theorem _paco2_3_1_unfold: forall (MON: _monotone2_3 gf_0) (MON: _monotone2_3 gf_1) (MON: _monotone2_3 gf_2) r_0 r_1 r_2,
  paco2_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 <2== gf_1 (upaco2_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco2_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco2_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  intros. apply curry_adjoint2_2.
  eapply _paco_3_1_unfold; apply monotone2_3_map; auto.
Qed.

Theorem _paco2_3_2_unfold: forall (MON: _monotone2_3 gf_0) (MON: _monotone2_3 gf_1) (MON: _monotone2_3 gf_2) r_0 r_1 r_2,
  paco2_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 <2== gf_2 (upaco2_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco2_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco2_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  intros. apply curry_adjoint2_2.
  eapply _paco_3_2_unfold; apply monotone2_3_map; auto.
Qed.

Theorem paco2_3_0_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_0 <2= rr) (CIH: l <2= rr), l <2= paco2_3_0 gf_0 gf_1 gf_2 rr r_1 r_2),
  l <2= paco2_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco2_3_0_acc.
Qed.

Theorem paco2_3_1_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_1 <2= rr) (CIH: l <2= rr), l <2= paco2_3_1 gf_0 gf_1 gf_2 r_0 rr r_2),
  l <2= paco2_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco2_3_1_acc.
Qed.

Theorem paco2_3_2_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_2 <2= rr) (CIH: l <2= rr), l <2= paco2_3_2 gf_0 gf_1 gf_2 r_0 r_1 rr),
  l <2= paco2_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco2_3_2_acc.
Qed.

Theorem paco2_3_0_mon: monotone2_3 (paco2_3_0 gf_0 gf_1 gf_2).
Proof.
  apply monotone2_3_eq.
  apply _paco2_3_0_mon.
Qed.

Theorem paco2_3_1_mon: monotone2_3 (paco2_3_1 gf_0 gf_1 gf_2).
Proof.
  apply monotone2_3_eq.
  apply _paco2_3_1_mon.
Qed.

Theorem paco2_3_2_mon: monotone2_3 (paco2_3_2 gf_0 gf_1 gf_2).
Proof.
  apply monotone2_3_eq.
  apply _paco2_3_2_mon.
Qed.

Theorem paco2_3_0_mult_strong: forall r_0 r_1 r_2,
  paco2_3_0 gf_0 gf_1 gf_2 (upaco2_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco2_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco2_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <2= paco2_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco2_3_0_mult_strong.
Qed.

Theorem paco2_3_1_mult_strong: forall r_0 r_1 r_2,
  paco2_3_1 gf_0 gf_1 gf_2 (upaco2_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco2_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco2_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <2= paco2_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco2_3_1_mult_strong.
Qed.

Theorem paco2_3_2_mult_strong: forall r_0 r_1 r_2,
  paco2_3_2 gf_0 gf_1 gf_2 (upaco2_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco2_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco2_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <2= paco2_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco2_3_2_mult_strong.
Qed.

Corollary paco2_3_0_mult: forall r_0 r_1 r_2,
  paco2_3_0 gf_0 gf_1 gf_2 (paco2_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco2_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco2_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <2= paco2_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco2_3_0_mult_strong, paco2_3_0_mon; eauto. Qed.

Corollary paco2_3_1_mult: forall r_0 r_1 r_2,
  paco2_3_1 gf_0 gf_1 gf_2 (paco2_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco2_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco2_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <2= paco2_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco2_3_1_mult_strong, paco2_3_1_mon; eauto. Qed.

Corollary paco2_3_2_mult: forall r_0 r_1 r_2,
  paco2_3_2 gf_0 gf_1 gf_2 (paco2_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco2_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco2_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <2= paco2_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco2_3_2_mult_strong, paco2_3_2_mon; eauto. Qed.

Theorem paco2_3_0_fold: forall r_0 r_1 r_2,
  gf_0 (upaco2_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco2_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco2_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <2= paco2_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco2_3_0_fold.
Qed.

Theorem paco2_3_1_fold: forall r_0 r_1 r_2,
  gf_1 (upaco2_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco2_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco2_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <2= paco2_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco2_3_1_fold.
Qed.

Theorem paco2_3_2_fold: forall r_0 r_1 r_2,
  gf_2 (upaco2_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco2_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco2_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <2= paco2_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco2_3_2_fold.
Qed.

Theorem paco2_3_0_unfold: forall (MON: monotone2_3 gf_0) (MON: monotone2_3 gf_1) (MON: monotone2_3 gf_2) r_0 r_1 r_2,
  paco2_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 <2= gf_0 (upaco2_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco2_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco2_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  repeat_intros 3. eapply _paco2_3_0_unfold; apply monotone2_3_eq; auto.
Qed.

Theorem paco2_3_1_unfold: forall (MON: monotone2_3 gf_0) (MON: monotone2_3 gf_1) (MON: monotone2_3 gf_2) r_0 r_1 r_2,
  paco2_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 <2= gf_1 (upaco2_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco2_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco2_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  repeat_intros 3. eapply _paco2_3_1_unfold; apply monotone2_3_eq; auto.
Qed.

Theorem paco2_3_2_unfold: forall (MON: monotone2_3 gf_0) (MON: monotone2_3 gf_1) (MON: monotone2_3 gf_2) r_0 r_1 r_2,
  paco2_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 <2= gf_2 (upaco2_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco2_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco2_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  repeat_intros 3. eapply _paco2_3_2_unfold; apply monotone2_3_eq; auto.
Qed.

End Arg2_3.

Arguments paco2_3_0_acc : clear implicits.
Arguments paco2_3_1_acc : clear implicits.
Arguments paco2_3_2_acc : clear implicits.
Arguments paco2_3_0_mon : clear implicits.
Arguments paco2_3_1_mon : clear implicits.
Arguments paco2_3_2_mon : clear implicits.
Arguments paco2_3_0_mult_strong : clear implicits.
Arguments paco2_3_1_mult_strong : clear implicits.
Arguments paco2_3_2_mult_strong : clear implicits.
Arguments paco2_3_0_mult : clear implicits.
Arguments paco2_3_1_mult : clear implicits.
Arguments paco2_3_2_mult : clear implicits.
Arguments paco2_3_0_fold : clear implicits.
Arguments paco2_3_1_fold : clear implicits.
Arguments paco2_3_2_fold : clear implicits.
Arguments paco2_3_0_unfold : clear implicits.
Arguments paco2_3_1_unfold : clear implicits.
Arguments paco2_3_2_unfold : clear implicits.

Global Instance paco2_3_0_inst  (gf_0 gf_1 gf_2 : rel2 T0 T1->_) r_0 r_1 r_2 x0 x1 : paco_class (paco2_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1) :=
{ pacoacc    := paco2_3_0_acc gf_0 gf_1 gf_2;
  pacomult   := paco2_3_0_mult gf_0 gf_1 gf_2;
  pacofold   := paco2_3_0_fold gf_0 gf_1 gf_2;
  pacounfold := paco2_3_0_unfold gf_0 gf_1 gf_2 }.

Global Instance paco2_3_1_inst  (gf_0 gf_1 gf_2 : rel2 T0 T1->_) r_0 r_1 r_2 x0 x1 : paco_class (paco2_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1) :=
{ pacoacc    := paco2_3_1_acc gf_0 gf_1 gf_2;
  pacomult   := paco2_3_1_mult gf_0 gf_1 gf_2;
  pacofold   := paco2_3_1_fold gf_0 gf_1 gf_2;
  pacounfold := paco2_3_1_unfold gf_0 gf_1 gf_2 }.

Global Instance paco2_3_2_inst  (gf_0 gf_1 gf_2 : rel2 T0 T1->_) r_0 r_1 r_2 x0 x1 : paco_class (paco2_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1) :=
{ pacoacc    := paco2_3_2_acc gf_0 gf_1 gf_2;
  pacomult   := paco2_3_2_mult gf_0 gf_1 gf_2;
  pacofold   := paco2_3_2_fold gf_0 gf_1 gf_2;
  pacounfold := paco2_3_2_unfold gf_0 gf_1 gf_2 }.

End PACO2.

Global Opaque paco2.

Hint Unfold upaco2.
Hint Resolve paco2_fold.
Hint Unfold monotone2.

Global Opaque paco2_2_0.
Global Opaque paco2_2_1.

Hint Unfold upaco2_2_0.
Hint Unfold upaco2_2_1.
Hint Resolve paco2_2_0_fold.
Hint Resolve paco2_2_1_fold.
Hint Unfold monotone2_2.

Global Opaque paco2_3_0.
Global Opaque paco2_3_1.
Global Opaque paco2_3_2.

Hint Unfold upaco2_3_0.
Hint Unfold upaco2_3_1.
Hint Unfold upaco2_3_2.
Hint Resolve paco2_3_0_fold.
Hint Resolve paco2_3_1_fold.
Hint Resolve paco2_3_2_fold.
Hint Unfold monotone2_3.

