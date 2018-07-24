Require Export paconotation pacotacuser.
Require Import paconotation_internal pacotac pacon.
Set Implicit Arguments.

Section PACO1.

Variable T0 : Type.

Record sig1T :=
  exist1T { 
      proj1T0: @T0;
    }.

Definition uncurry1 (R: rel1 T0): rel1 sig1T := fun x => R (proj1T0 x).

Definition curry1 (R: rel1 sig1T): rel1 T0 :=
  fun x0 => R (exist1T x0).

Lemma uncurry_map1 r0 r1 (LE : r0 <1== r1) : uncurry1 r0 <1== uncurry1 r1.
Proof. intros [] H. apply LE. auto. Qed.

Lemma uncurry_map_rev1 r0 r1 (LE: uncurry1 r0 <1== uncurry1 r1) : r0 <1== r1.
Proof.
  repeat_intros 1. intros H. apply (LE (exist1T x0) H).
Qed.

Lemma curry_map1 r0 r1 (LE: r0 <1== r1) : curry1 r0 <1== curry1 r1.
Proof. 
  repeat_intros 1. intros H. apply (LE (exist1T x0) H).
Qed.

Lemma curry_map_rev1 r0 r1 (LE: curry1 r0 <1== curry1 r1) : r0 <1== r1.
Proof. 
  intros [] H. apply LE. apply H.
Qed.

Lemma uncurry_bij1_1 r : curry1 (uncurry1 r) <1== r.
Proof. unfold le1. repeat_intros 1; auto. Qed.

Lemma uncurry_bij2_1 r : r <1== curry1 (uncurry1 r).
Proof. unfold le1. repeat_intros 1; auto. Qed.

Lemma curry_bij1_1 r : uncurry1 (curry1 r) <1== r.
Proof. intros []; auto. Qed.

Lemma curry_bij2_1 r : r <1== uncurry1 (curry1 r).
Proof. intros []; auto. Qed.

Lemma uncurry_adjoint1_1 r0 r1 (LE: uncurry1 r0 <1== r1) : r0 <1== curry1 r1.
Proof.
  apply uncurry_map_rev1. eapply le1_trans; [eauto|]. apply curry_bij2_1.
Qed.

Lemma uncurry_adjoint2_1 r0 r1 (LE: r0 <1== curry1 r1) : uncurry1 r0 <1== r1.
Proof.
  apply curry_map_rev1. eapply le1_trans; [|eauto]. apply uncurry_bij2_1.
Qed.

Lemma curry_adjoint1_1 r0 r1 (LE: curry1 r0 <1== r1) : r0 <1== uncurry1 r1.
Proof.
  apply curry_map_rev1. eapply le1_trans; [eauto|]. apply uncurry_bij2_1.
Qed.

Lemma curry_adjoint2_1 r0 r1 (LE: r0 <1== uncurry1 r1) : curry1 r0 <1== r1.
Proof.
  apply uncurry_map_rev1. eapply le1_trans; [|eauto]. apply curry_bij1_1.
Qed.

(** ** Predicates of Arity 1
*)

Section Arg1_def.
Variable gf : rel1 T0 -> rel1 T0.
Arguments gf : clear implicits.

Definition paco1( r: rel1 T0) : rel1 T0 :=
  curry1 (paco (fun R0 => uncurry1 (gf (curry1 R0))) (uncurry1 r)).

Definition upaco1( r: rel1 T0) := paco1 r \1/ r.
End Arg1_def.
Arguments paco1 : clear implicits.
Arguments upaco1 : clear implicits.
Hint Unfold upaco1.

Section Arg1_2_def.
Variable gf_0 gf_1 : rel1 T0 -> rel1 T0 -> rel1 T0.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.

Definition paco1_2_0( r_0 r_1: rel1 T0) : rel1 T0 :=
  curry1 (paco_2_0 (fun R0 R1 => uncurry1 (gf_0 (curry1 R0) (curry1 R1))) (fun R0 R1 => uncurry1 (gf_1 (curry1 R0) (curry1 R1))) (uncurry1 r_0) (uncurry1 r_1)).

Definition paco1_2_1( r_0 r_1: rel1 T0) : rel1 T0 :=
  curry1 (paco_2_1 (fun R0 R1 => uncurry1 (gf_0 (curry1 R0) (curry1 R1))) (fun R0 R1 => uncurry1 (gf_1 (curry1 R0) (curry1 R1))) (uncurry1 r_0) (uncurry1 r_1)).

Definition upaco1_2_0( r_0 r_1: rel1 T0) := paco1_2_0 r_0 r_1 \1/ r_0.
Definition upaco1_2_1( r_0 r_1: rel1 T0) := paco1_2_1 r_0 r_1 \1/ r_1.
End Arg1_2_def.
Arguments paco1_2_0 : clear implicits.
Arguments upaco1_2_0 : clear implicits.
Hint Unfold upaco1_2_0.
Arguments paco1_2_1 : clear implicits.
Arguments upaco1_2_1 : clear implicits.
Hint Unfold upaco1_2_1.

Section Arg1_3_def.
Variable gf_0 gf_1 gf_2 : rel1 T0 -> rel1 T0 -> rel1 T0 -> rel1 T0.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.
Arguments gf_2 : clear implicits.

Definition paco1_3_0( r_0 r_1 r_2: rel1 T0) : rel1 T0 :=
  curry1 (paco_3_0 (fun R0 R1 R2 => uncurry1 (gf_0 (curry1 R0) (curry1 R1) (curry1 R2))) (fun R0 R1 R2 => uncurry1 (gf_1 (curry1 R0) (curry1 R1) (curry1 R2))) (fun R0 R1 R2 => uncurry1 (gf_2 (curry1 R0) (curry1 R1) (curry1 R2))) (uncurry1 r_0) (uncurry1 r_1) (uncurry1 r_2)).

Definition paco1_3_1( r_0 r_1 r_2: rel1 T0) : rel1 T0 :=
  curry1 (paco_3_1 (fun R0 R1 R2 => uncurry1 (gf_0 (curry1 R0) (curry1 R1) (curry1 R2))) (fun R0 R1 R2 => uncurry1 (gf_1 (curry1 R0) (curry1 R1) (curry1 R2))) (fun R0 R1 R2 => uncurry1 (gf_2 (curry1 R0) (curry1 R1) (curry1 R2))) (uncurry1 r_0) (uncurry1 r_1) (uncurry1 r_2)).

Definition paco1_3_2( r_0 r_1 r_2: rel1 T0) : rel1 T0 :=
  curry1 (paco_3_2 (fun R0 R1 R2 => uncurry1 (gf_0 (curry1 R0) (curry1 R1) (curry1 R2))) (fun R0 R1 R2 => uncurry1 (gf_1 (curry1 R0) (curry1 R1) (curry1 R2))) (fun R0 R1 R2 => uncurry1 (gf_2 (curry1 R0) (curry1 R1) (curry1 R2))) (uncurry1 r_0) (uncurry1 r_1) (uncurry1 r_2)).

Definition upaco1_3_0( r_0 r_1 r_2: rel1 T0) := paco1_3_0 r_0 r_1 r_2 \1/ r_0.
Definition upaco1_3_1( r_0 r_1 r_2: rel1 T0) := paco1_3_1 r_0 r_1 r_2 \1/ r_1.
Definition upaco1_3_2( r_0 r_1 r_2: rel1 T0) := paco1_3_2 r_0 r_1 r_2 \1/ r_2.
End Arg1_3_def.
Arguments paco1_3_0 : clear implicits.
Arguments upaco1_3_0 : clear implicits.
Hint Unfold upaco1_3_0.
Arguments paco1_3_1 : clear implicits.
Arguments upaco1_3_1 : clear implicits.
Hint Unfold upaco1_3_1.
Arguments paco1_3_2 : clear implicits.
Arguments upaco1_3_2 : clear implicits.
Hint Unfold upaco1_3_2.

(** 1 Mutual Coinduction *)

Section Arg1_1.

Definition monotone1 (gf: rel1 T0 -> rel1 T0) :=
  forall x0 r r' (IN: gf r x0) (LE: r <1= r'), gf r' x0.

Definition _monotone1 (gf: rel1 T0 -> rel1 T0) :=
  forall r r'(LE: r <1= r'), gf r <1== gf r'.

Lemma monotone1_eq (gf: rel1 T0 -> rel1 T0) :
  monotone1 gf <-> _monotone1 gf.
Proof. unfold monotone1, _monotone1, le1. split; eauto. Qed.

Lemma monotone1_map (gf: rel1 T0 -> rel1 T0)
      (MON: _monotone1 gf) :
  _monotone (fun R0 => uncurry1 (gf (curry1 R0))).
Proof.
  repeat_intros 3. apply uncurry_map1. apply MON; apply curry_map1; auto.
Qed.

Variable gf : rel1 T0 -> rel1 T0.
Arguments gf : clear implicits.

Theorem _paco1_mon: _monotone1 (paco1 gf).
Proof.
  repeat_intros 3. eapply curry_map1, _paco_mon; apply uncurry_map1; auto.
Qed.

Theorem _paco1_acc: forall
  l r (OBG: forall rr (INC: r <1== rr) (CIH: l <1== rr), l <1== paco1 gf rr),
  l <1== paco1 gf r.
Proof.
  intros. apply uncurry_adjoint1_1.
  eapply _paco_acc. intros.
  apply uncurry_adjoint1_1 in INC. apply uncurry_adjoint1_1 in CIH.
  apply uncurry_adjoint2_1.
  eapply le1_trans. eapply (OBG _ INC CIH).
  apply curry_map1.
  apply _paco_mon; try apply le1_refl; apply curry_bij1_1.
Qed.

Theorem _paco1_mult_strong: forall r,
  paco1 gf (upaco1 gf r) <1== paco1 gf r.
Proof.
  intros. apply curry_map1.
  eapply le1_trans; [| eapply _paco_mult_strong].
  apply _paco_mon; intros []; eauto.
Qed.

Theorem _paco1_fold: forall r,
  gf (upaco1 gf r) <1== paco1 gf r.
Proof.
  intros. apply uncurry_adjoint1_1.
  eapply le1_trans; [| apply _paco_fold]. apply le1_refl.
Qed.

Theorem _paco1_unfold: forall (MON: _monotone1 gf) r,
  paco1 gf r <1== gf (upaco1 gf r).
Proof.
  intros. apply curry_adjoint2_1.
  eapply _paco_unfold; apply monotone1_map; auto.
Qed.

Theorem paco1_acc: forall
  l r (OBG: forall rr (INC: r <1= rr) (CIH: l <1= rr), l <1= paco1 gf rr),
  l <1= paco1 gf r.
Proof.
  apply _paco1_acc.
Qed.

Theorem paco1_mon: monotone1 (paco1 gf).
Proof.
  apply monotone1_eq.
  apply _paco1_mon.
Qed.

Theorem paco1_mult_strong: forall r,
  paco1 gf (upaco1 gf r) <1= paco1 gf r.
Proof.
  apply _paco1_mult_strong.
Qed.

Corollary paco1_mult: forall r,
  paco1 gf (paco1 gf r) <1= paco1 gf r.
Proof. intros; eapply paco1_mult_strong, paco1_mon; eauto. Qed.

Theorem paco1_fold: forall r,
  gf (upaco1 gf r) <1= paco1 gf r.
Proof.
  apply _paco1_fold.
Qed.

Theorem paco1_unfold: forall (MON: monotone1 gf) r,
  paco1 gf r <1= gf (upaco1 gf r).
Proof.
  repeat_intros 1. eapply _paco1_unfold; apply monotone1_eq; auto.
Qed.

End Arg1_1.

Arguments paco1_acc : clear implicits.
Arguments paco1_mon : clear implicits.
Arguments paco1_mult_strong : clear implicits.
Arguments paco1_mult : clear implicits.
Arguments paco1_fold : clear implicits.
Arguments paco1_unfold : clear implicits.

Global Instance paco1_inst  (gf : rel1 T0->_) r x0 : paco_class (paco1 gf r x0) :=
{ pacoacc    := paco1_acc gf;
  pacomult   := paco1_mult gf;
  pacofold   := paco1_fold gf;
  pacounfold := paco1_unfold gf }.

(** 2 Mutual Coinduction *)

Section Arg1_2.

Definition monotone1_2 (gf: rel1 T0 -> rel1 T0 -> rel1 T0) :=
  forall x0 r_0 r_1 r'_0 r'_1 (IN: gf r_0 r_1 x0) (LE_0: r_0 <1= r'_0)(LE_1: r_1 <1= r'_1), gf r'_0 r'_1 x0.

Definition _monotone1_2 (gf: rel1 T0 -> rel1 T0 -> rel1 T0) :=
  forall r_0 r_1 r'_0 r'_1(LE_0: r_0 <1= r'_0)(LE_1: r_1 <1= r'_1), gf r_0 r_1 <1== gf r'_0 r'_1.

Lemma monotone1_2_eq (gf: rel1 T0 -> rel1 T0 -> rel1 T0) :
  monotone1_2 gf <-> _monotone1_2 gf.
Proof. unfold monotone1_2, _monotone1_2, le1. split; eauto. Qed.

Lemma monotone1_2_map (gf: rel1 T0 -> rel1 T0 -> rel1 T0)
      (MON: _monotone1_2 gf) :
  _monotone_2 (fun R0 R1 => uncurry1 (gf (curry1 R0) (curry1 R1))).
Proof.
  repeat_intros 6. apply uncurry_map1. apply MON; apply curry_map1; auto.
Qed.

Variable gf_0 gf_1 : rel1 T0 -> rel1 T0 -> rel1 T0.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.

Theorem _paco1_2_0_mon: _monotone1_2 (paco1_2_0 gf_0 gf_1).
Proof.
  repeat_intros 6. eapply curry_map1, _paco_2_0_mon; apply uncurry_map1; auto.
Qed.

Theorem _paco1_2_1_mon: _monotone1_2 (paco1_2_1 gf_0 gf_1).
Proof.
  repeat_intros 6. eapply curry_map1, _paco_2_1_mon; apply uncurry_map1; auto.
Qed.

Theorem _paco1_2_0_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_0 <1== rr) (CIH: l <1== rr), l <1== paco1_2_0 gf_0 gf_1 rr r_1),
  l <1== paco1_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_1.
  eapply _paco_2_0_acc. intros.
  apply uncurry_adjoint1_1 in INC. apply uncurry_adjoint1_1 in CIH.
  apply uncurry_adjoint2_1.
  eapply le1_trans. eapply (OBG _ INC CIH).
  apply curry_map1.
  apply _paco_2_0_mon; try apply le1_refl; apply curry_bij1_1.
Qed.

Theorem _paco1_2_1_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_1 <1== rr) (CIH: l <1== rr), l <1== paco1_2_1 gf_0 gf_1 r_0 rr),
  l <1== paco1_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_1.
  eapply _paco_2_1_acc. intros.
  apply uncurry_adjoint1_1 in INC. apply uncurry_adjoint1_1 in CIH.
  apply uncurry_adjoint2_1.
  eapply le1_trans. eapply (OBG _ INC CIH).
  apply curry_map1.
  apply _paco_2_1_mon; try apply le1_refl; apply curry_bij1_1.
Qed.

Theorem _paco1_2_0_mult_strong: forall r_0 r_1,
  paco1_2_0 gf_0 gf_1 (upaco1_2_0 gf_0 gf_1 r_0 r_1) (upaco1_2_1 gf_0 gf_1 r_0 r_1) <1== paco1_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply curry_map1.
  eapply le1_trans; [| eapply _paco_2_0_mult_strong].
  apply _paco_2_0_mon; intros []; eauto.
Qed.

Theorem _paco1_2_1_mult_strong: forall r_0 r_1,
  paco1_2_1 gf_0 gf_1 (upaco1_2_0 gf_0 gf_1 r_0 r_1) (upaco1_2_1 gf_0 gf_1 r_0 r_1) <1== paco1_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply curry_map1.
  eapply le1_trans; [| eapply _paco_2_1_mult_strong].
  apply _paco_2_1_mon; intros []; eauto.
Qed.

Theorem _paco1_2_0_fold: forall r_0 r_1,
  gf_0 (upaco1_2_0 gf_0 gf_1 r_0 r_1) (upaco1_2_1 gf_0 gf_1 r_0 r_1) <1== paco1_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_1.
  eapply le1_trans; [| apply _paco_2_0_fold]. apply le1_refl.
Qed.

Theorem _paco1_2_1_fold: forall r_0 r_1,
  gf_1 (upaco1_2_0 gf_0 gf_1 r_0 r_1) (upaco1_2_1 gf_0 gf_1 r_0 r_1) <1== paco1_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_1.
  eapply le1_trans; [| apply _paco_2_1_fold]. apply le1_refl.
Qed.

Theorem _paco1_2_0_unfold: forall (MON: _monotone1_2 gf_0) (MON: _monotone1_2 gf_1) r_0 r_1,
  paco1_2_0 gf_0 gf_1 r_0 r_1 <1== gf_0 (upaco1_2_0 gf_0 gf_1 r_0 r_1) (upaco1_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  intros. apply curry_adjoint2_1.
  eapply _paco_2_0_unfold; apply monotone1_2_map; auto.
Qed.

Theorem _paco1_2_1_unfold: forall (MON: _monotone1_2 gf_0) (MON: _monotone1_2 gf_1) r_0 r_1,
  paco1_2_1 gf_0 gf_1 r_0 r_1 <1== gf_1 (upaco1_2_0 gf_0 gf_1 r_0 r_1) (upaco1_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  intros. apply curry_adjoint2_1.
  eapply _paco_2_1_unfold; apply monotone1_2_map; auto.
Qed.

Theorem paco1_2_0_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_0 <1= rr) (CIH: l <1= rr), l <1= paco1_2_0 gf_0 gf_1 rr r_1),
  l <1= paco1_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco1_2_0_acc.
Qed.

Theorem paco1_2_1_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_1 <1= rr) (CIH: l <1= rr), l <1= paco1_2_1 gf_0 gf_1 r_0 rr),
  l <1= paco1_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco1_2_1_acc.
Qed.

Theorem paco1_2_0_mon: monotone1_2 (paco1_2_0 gf_0 gf_1).
Proof.
  apply monotone1_2_eq.
  apply _paco1_2_0_mon.
Qed.

Theorem paco1_2_1_mon: monotone1_2 (paco1_2_1 gf_0 gf_1).
Proof.
  apply monotone1_2_eq.
  apply _paco1_2_1_mon.
Qed.

Theorem paco1_2_0_mult_strong: forall r_0 r_1,
  paco1_2_0 gf_0 gf_1 (upaco1_2_0 gf_0 gf_1 r_0 r_1) (upaco1_2_1 gf_0 gf_1 r_0 r_1) <1= paco1_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco1_2_0_mult_strong.
Qed.

Theorem paco1_2_1_mult_strong: forall r_0 r_1,
  paco1_2_1 gf_0 gf_1 (upaco1_2_0 gf_0 gf_1 r_0 r_1) (upaco1_2_1 gf_0 gf_1 r_0 r_1) <1= paco1_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco1_2_1_mult_strong.
Qed.

Corollary paco1_2_0_mult: forall r_0 r_1,
  paco1_2_0 gf_0 gf_1 (paco1_2_0 gf_0 gf_1 r_0 r_1) (paco1_2_1 gf_0 gf_1 r_0 r_1) <1= paco1_2_0 gf_0 gf_1 r_0 r_1.
Proof. intros; eapply paco1_2_0_mult_strong, paco1_2_0_mon; eauto. Qed.

Corollary paco1_2_1_mult: forall r_0 r_1,
  paco1_2_1 gf_0 gf_1 (paco1_2_0 gf_0 gf_1 r_0 r_1) (paco1_2_1 gf_0 gf_1 r_0 r_1) <1= paco1_2_1 gf_0 gf_1 r_0 r_1.
Proof. intros; eapply paco1_2_1_mult_strong, paco1_2_1_mon; eauto. Qed.

Theorem paco1_2_0_fold: forall r_0 r_1,
  gf_0 (upaco1_2_0 gf_0 gf_1 r_0 r_1) (upaco1_2_1 gf_0 gf_1 r_0 r_1) <1= paco1_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco1_2_0_fold.
Qed.

Theorem paco1_2_1_fold: forall r_0 r_1,
  gf_1 (upaco1_2_0 gf_0 gf_1 r_0 r_1) (upaco1_2_1 gf_0 gf_1 r_0 r_1) <1= paco1_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco1_2_1_fold.
Qed.

Theorem paco1_2_0_unfold: forall (MON: monotone1_2 gf_0) (MON: monotone1_2 gf_1) r_0 r_1,
  paco1_2_0 gf_0 gf_1 r_0 r_1 <1= gf_0 (upaco1_2_0 gf_0 gf_1 r_0 r_1) (upaco1_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  repeat_intros 2. eapply _paco1_2_0_unfold; apply monotone1_2_eq; auto.
Qed.

Theorem paco1_2_1_unfold: forall (MON: monotone1_2 gf_0) (MON: monotone1_2 gf_1) r_0 r_1,
  paco1_2_1 gf_0 gf_1 r_0 r_1 <1= gf_1 (upaco1_2_0 gf_0 gf_1 r_0 r_1) (upaco1_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  repeat_intros 2. eapply _paco1_2_1_unfold; apply monotone1_2_eq; auto.
Qed.

End Arg1_2.

Arguments paco1_2_0_acc : clear implicits.
Arguments paco1_2_1_acc : clear implicits.
Arguments paco1_2_0_mon : clear implicits.
Arguments paco1_2_1_mon : clear implicits.
Arguments paco1_2_0_mult_strong : clear implicits.
Arguments paco1_2_1_mult_strong : clear implicits.
Arguments paco1_2_0_mult : clear implicits.
Arguments paco1_2_1_mult : clear implicits.
Arguments paco1_2_0_fold : clear implicits.
Arguments paco1_2_1_fold : clear implicits.
Arguments paco1_2_0_unfold : clear implicits.
Arguments paco1_2_1_unfold : clear implicits.

Global Instance paco1_2_0_inst  (gf_0 gf_1 : rel1 T0->_) r_0 r_1 x0 : paco_class (paco1_2_0 gf_0 gf_1 r_0 r_1 x0) :=
{ pacoacc    := paco1_2_0_acc gf_0 gf_1;
  pacomult   := paco1_2_0_mult gf_0 gf_1;
  pacofold   := paco1_2_0_fold gf_0 gf_1;
  pacounfold := paco1_2_0_unfold gf_0 gf_1 }.

Global Instance paco1_2_1_inst  (gf_0 gf_1 : rel1 T0->_) r_0 r_1 x0 : paco_class (paco1_2_1 gf_0 gf_1 r_0 r_1 x0) :=
{ pacoacc    := paco1_2_1_acc gf_0 gf_1;
  pacomult   := paco1_2_1_mult gf_0 gf_1;
  pacofold   := paco1_2_1_fold gf_0 gf_1;
  pacounfold := paco1_2_1_unfold gf_0 gf_1 }.

(** 3 Mutual Coinduction *)

Section Arg1_3.

Definition monotone1_3 (gf: rel1 T0 -> rel1 T0 -> rel1 T0 -> rel1 T0) :=
  forall x0 r_0 r_1 r_2 r'_0 r'_1 r'_2 (IN: gf r_0 r_1 r_2 x0) (LE_0: r_0 <1= r'_0)(LE_1: r_1 <1= r'_1)(LE_2: r_2 <1= r'_2), gf r'_0 r'_1 r'_2 x0.

Definition _monotone1_3 (gf: rel1 T0 -> rel1 T0 -> rel1 T0 -> rel1 T0) :=
  forall r_0 r_1 r_2 r'_0 r'_1 r'_2(LE_0: r_0 <1= r'_0)(LE_1: r_1 <1= r'_1)(LE_2: r_2 <1= r'_2), gf r_0 r_1 r_2 <1== gf r'_0 r'_1 r'_2.

Lemma monotone1_3_eq (gf: rel1 T0 -> rel1 T0 -> rel1 T0 -> rel1 T0) :
  monotone1_3 gf <-> _monotone1_3 gf.
Proof. unfold monotone1_3, _monotone1_3, le1. split; eauto. Qed.

Lemma monotone1_3_map (gf: rel1 T0 -> rel1 T0 -> rel1 T0 -> rel1 T0)
      (MON: _monotone1_3 gf) :
  _monotone_3 (fun R0 R1 R2 => uncurry1 (gf (curry1 R0) (curry1 R1) (curry1 R2))).
Proof.
  repeat_intros 9. apply uncurry_map1. apply MON; apply curry_map1; auto.
Qed.

Variable gf_0 gf_1 gf_2 : rel1 T0 -> rel1 T0 -> rel1 T0 -> rel1 T0.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.
Arguments gf_2 : clear implicits.

Theorem _paco1_3_0_mon: _monotone1_3 (paco1_3_0 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 9. eapply curry_map1, _paco_3_0_mon; apply uncurry_map1; auto.
Qed.

Theorem _paco1_3_1_mon: _monotone1_3 (paco1_3_1 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 9. eapply curry_map1, _paco_3_1_mon; apply uncurry_map1; auto.
Qed.

Theorem _paco1_3_2_mon: _monotone1_3 (paco1_3_2 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 9. eapply curry_map1, _paco_3_2_mon; apply uncurry_map1; auto.
Qed.

Theorem _paco1_3_0_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_0 <1== rr) (CIH: l <1== rr), l <1== paco1_3_0 gf_0 gf_1 gf_2 rr r_1 r_2),
  l <1== paco1_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_1.
  eapply _paco_3_0_acc. intros.
  apply uncurry_adjoint1_1 in INC. apply uncurry_adjoint1_1 in CIH.
  apply uncurry_adjoint2_1.
  eapply le1_trans. eapply (OBG _ INC CIH).
  apply curry_map1.
  apply _paco_3_0_mon; try apply le1_refl; apply curry_bij1_1.
Qed.

Theorem _paco1_3_1_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_1 <1== rr) (CIH: l <1== rr), l <1== paco1_3_1 gf_0 gf_1 gf_2 r_0 rr r_2),
  l <1== paco1_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_1.
  eapply _paco_3_1_acc. intros.
  apply uncurry_adjoint1_1 in INC. apply uncurry_adjoint1_1 in CIH.
  apply uncurry_adjoint2_1.
  eapply le1_trans. eapply (OBG _ INC CIH).
  apply curry_map1.
  apply _paco_3_1_mon; try apply le1_refl; apply curry_bij1_1.
Qed.

Theorem _paco1_3_2_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_2 <1== rr) (CIH: l <1== rr), l <1== paco1_3_2 gf_0 gf_1 gf_2 r_0 r_1 rr),
  l <1== paco1_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_1.
  eapply _paco_3_2_acc. intros.
  apply uncurry_adjoint1_1 in INC. apply uncurry_adjoint1_1 in CIH.
  apply uncurry_adjoint2_1.
  eapply le1_trans. eapply (OBG _ INC CIH).
  apply curry_map1.
  apply _paco_3_2_mon; try apply le1_refl; apply curry_bij1_1.
Qed.

Theorem _paco1_3_0_mult_strong: forall r_0 r_1 r_2,
  paco1_3_0 gf_0 gf_1 gf_2 (upaco1_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco1_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco1_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <1== paco1_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply curry_map1.
  eapply le1_trans; [| eapply _paco_3_0_mult_strong].
  apply _paco_3_0_mon; intros []; eauto.
Qed.

Theorem _paco1_3_1_mult_strong: forall r_0 r_1 r_2,
  paco1_3_1 gf_0 gf_1 gf_2 (upaco1_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco1_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco1_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <1== paco1_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply curry_map1.
  eapply le1_trans; [| eapply _paco_3_1_mult_strong].
  apply _paco_3_1_mon; intros []; eauto.
Qed.

Theorem _paco1_3_2_mult_strong: forall r_0 r_1 r_2,
  paco1_3_2 gf_0 gf_1 gf_2 (upaco1_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco1_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco1_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <1== paco1_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply curry_map1.
  eapply le1_trans; [| eapply _paco_3_2_mult_strong].
  apply _paco_3_2_mon; intros []; eauto.
Qed.

Theorem _paco1_3_0_fold: forall r_0 r_1 r_2,
  gf_0 (upaco1_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco1_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco1_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <1== paco1_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_1.
  eapply le1_trans; [| apply _paco_3_0_fold]. apply le1_refl.
Qed.

Theorem _paco1_3_1_fold: forall r_0 r_1 r_2,
  gf_1 (upaco1_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco1_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco1_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <1== paco1_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_1.
  eapply le1_trans; [| apply _paco_3_1_fold]. apply le1_refl.
Qed.

Theorem _paco1_3_2_fold: forall r_0 r_1 r_2,
  gf_2 (upaco1_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco1_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco1_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <1== paco1_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_1.
  eapply le1_trans; [| apply _paco_3_2_fold]. apply le1_refl.
Qed.

Theorem _paco1_3_0_unfold: forall (MON: _monotone1_3 gf_0) (MON: _monotone1_3 gf_1) (MON: _monotone1_3 gf_2) r_0 r_1 r_2,
  paco1_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 <1== gf_0 (upaco1_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco1_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco1_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  intros. apply curry_adjoint2_1.
  eapply _paco_3_0_unfold; apply monotone1_3_map; auto.
Qed.

Theorem _paco1_3_1_unfold: forall (MON: _monotone1_3 gf_0) (MON: _monotone1_3 gf_1) (MON: _monotone1_3 gf_2) r_0 r_1 r_2,
  paco1_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 <1== gf_1 (upaco1_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco1_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco1_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  intros. apply curry_adjoint2_1.
  eapply _paco_3_1_unfold; apply monotone1_3_map; auto.
Qed.

Theorem _paco1_3_2_unfold: forall (MON: _monotone1_3 gf_0) (MON: _monotone1_3 gf_1) (MON: _monotone1_3 gf_2) r_0 r_1 r_2,
  paco1_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 <1== gf_2 (upaco1_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco1_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco1_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  intros. apply curry_adjoint2_1.
  eapply _paco_3_2_unfold; apply monotone1_3_map; auto.
Qed.

Theorem paco1_3_0_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_0 <1= rr) (CIH: l <1= rr), l <1= paco1_3_0 gf_0 gf_1 gf_2 rr r_1 r_2),
  l <1= paco1_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco1_3_0_acc.
Qed.

Theorem paco1_3_1_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_1 <1= rr) (CIH: l <1= rr), l <1= paco1_3_1 gf_0 gf_1 gf_2 r_0 rr r_2),
  l <1= paco1_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco1_3_1_acc.
Qed.

Theorem paco1_3_2_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_2 <1= rr) (CIH: l <1= rr), l <1= paco1_3_2 gf_0 gf_1 gf_2 r_0 r_1 rr),
  l <1= paco1_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco1_3_2_acc.
Qed.

Theorem paco1_3_0_mon: monotone1_3 (paco1_3_0 gf_0 gf_1 gf_2).
Proof.
  apply monotone1_3_eq.
  apply _paco1_3_0_mon.
Qed.

Theorem paco1_3_1_mon: monotone1_3 (paco1_3_1 gf_0 gf_1 gf_2).
Proof.
  apply monotone1_3_eq.
  apply _paco1_3_1_mon.
Qed.

Theorem paco1_3_2_mon: monotone1_3 (paco1_3_2 gf_0 gf_1 gf_2).
Proof.
  apply monotone1_3_eq.
  apply _paco1_3_2_mon.
Qed.

Theorem paco1_3_0_mult_strong: forall r_0 r_1 r_2,
  paco1_3_0 gf_0 gf_1 gf_2 (upaco1_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco1_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco1_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <1= paco1_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco1_3_0_mult_strong.
Qed.

Theorem paco1_3_1_mult_strong: forall r_0 r_1 r_2,
  paco1_3_1 gf_0 gf_1 gf_2 (upaco1_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco1_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco1_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <1= paco1_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco1_3_1_mult_strong.
Qed.

Theorem paco1_3_2_mult_strong: forall r_0 r_1 r_2,
  paco1_3_2 gf_0 gf_1 gf_2 (upaco1_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco1_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco1_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <1= paco1_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco1_3_2_mult_strong.
Qed.

Corollary paco1_3_0_mult: forall r_0 r_1 r_2,
  paco1_3_0 gf_0 gf_1 gf_2 (paco1_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco1_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco1_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <1= paco1_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco1_3_0_mult_strong, paco1_3_0_mon; eauto. Qed.

Corollary paco1_3_1_mult: forall r_0 r_1 r_2,
  paco1_3_1 gf_0 gf_1 gf_2 (paco1_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco1_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco1_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <1= paco1_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco1_3_1_mult_strong, paco1_3_1_mon; eauto. Qed.

Corollary paco1_3_2_mult: forall r_0 r_1 r_2,
  paco1_3_2 gf_0 gf_1 gf_2 (paco1_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco1_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco1_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <1= paco1_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco1_3_2_mult_strong, paco1_3_2_mon; eauto. Qed.

Theorem paco1_3_0_fold: forall r_0 r_1 r_2,
  gf_0 (upaco1_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco1_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco1_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <1= paco1_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco1_3_0_fold.
Qed.

Theorem paco1_3_1_fold: forall r_0 r_1 r_2,
  gf_1 (upaco1_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco1_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco1_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <1= paco1_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco1_3_1_fold.
Qed.

Theorem paco1_3_2_fold: forall r_0 r_1 r_2,
  gf_2 (upaco1_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco1_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco1_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <1= paco1_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco1_3_2_fold.
Qed.

Theorem paco1_3_0_unfold: forall (MON: monotone1_3 gf_0) (MON: monotone1_3 gf_1) (MON: monotone1_3 gf_2) r_0 r_1 r_2,
  paco1_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 <1= gf_0 (upaco1_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco1_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco1_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  repeat_intros 3. eapply _paco1_3_0_unfold; apply monotone1_3_eq; auto.
Qed.

Theorem paco1_3_1_unfold: forall (MON: monotone1_3 gf_0) (MON: monotone1_3 gf_1) (MON: monotone1_3 gf_2) r_0 r_1 r_2,
  paco1_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 <1= gf_1 (upaco1_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco1_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco1_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  repeat_intros 3. eapply _paco1_3_1_unfold; apply monotone1_3_eq; auto.
Qed.

Theorem paco1_3_2_unfold: forall (MON: monotone1_3 gf_0) (MON: monotone1_3 gf_1) (MON: monotone1_3 gf_2) r_0 r_1 r_2,
  paco1_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 <1= gf_2 (upaco1_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco1_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco1_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  repeat_intros 3. eapply _paco1_3_2_unfold; apply monotone1_3_eq; auto.
Qed.

End Arg1_3.

Arguments paco1_3_0_acc : clear implicits.
Arguments paco1_3_1_acc : clear implicits.
Arguments paco1_3_2_acc : clear implicits.
Arguments paco1_3_0_mon : clear implicits.
Arguments paco1_3_1_mon : clear implicits.
Arguments paco1_3_2_mon : clear implicits.
Arguments paco1_3_0_mult_strong : clear implicits.
Arguments paco1_3_1_mult_strong : clear implicits.
Arguments paco1_3_2_mult_strong : clear implicits.
Arguments paco1_3_0_mult : clear implicits.
Arguments paco1_3_1_mult : clear implicits.
Arguments paco1_3_2_mult : clear implicits.
Arguments paco1_3_0_fold : clear implicits.
Arguments paco1_3_1_fold : clear implicits.
Arguments paco1_3_2_fold : clear implicits.
Arguments paco1_3_0_unfold : clear implicits.
Arguments paco1_3_1_unfold : clear implicits.
Arguments paco1_3_2_unfold : clear implicits.

Global Instance paco1_3_0_inst  (gf_0 gf_1 gf_2 : rel1 T0->_) r_0 r_1 r_2 x0 : paco_class (paco1_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0) :=
{ pacoacc    := paco1_3_0_acc gf_0 gf_1 gf_2;
  pacomult   := paco1_3_0_mult gf_0 gf_1 gf_2;
  pacofold   := paco1_3_0_fold gf_0 gf_1 gf_2;
  pacounfold := paco1_3_0_unfold gf_0 gf_1 gf_2 }.

Global Instance paco1_3_1_inst  (gf_0 gf_1 gf_2 : rel1 T0->_) r_0 r_1 r_2 x0 : paco_class (paco1_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0) :=
{ pacoacc    := paco1_3_1_acc gf_0 gf_1 gf_2;
  pacomult   := paco1_3_1_mult gf_0 gf_1 gf_2;
  pacofold   := paco1_3_1_fold gf_0 gf_1 gf_2;
  pacounfold := paco1_3_1_unfold gf_0 gf_1 gf_2 }.

Global Instance paco1_3_2_inst  (gf_0 gf_1 gf_2 : rel1 T0->_) r_0 r_1 r_2 x0 : paco_class (paco1_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0) :=
{ pacoacc    := paco1_3_2_acc gf_0 gf_1 gf_2;
  pacomult   := paco1_3_2_mult gf_0 gf_1 gf_2;
  pacofold   := paco1_3_2_fold gf_0 gf_1 gf_2;
  pacounfold := paco1_3_2_unfold gf_0 gf_1 gf_2 }.

End PACO1.

Global Opaque paco1.

Hint Unfold upaco1.
Hint Resolve paco1_fold.
Hint Unfold monotone1.

Global Opaque paco1_2_0.
Global Opaque paco1_2_1.

Hint Unfold upaco1_2_0.
Hint Unfold upaco1_2_1.
Hint Resolve paco1_2_0_fold.
Hint Resolve paco1_2_1_fold.
Hint Unfold monotone1_2.

Global Opaque paco1_3_0.
Global Opaque paco1_3_1.
Global Opaque paco1_3_2.

Hint Unfold upaco1_3_0.
Hint Unfold upaco1_3_1.
Hint Unfold upaco1_3_2.
Hint Resolve paco1_3_0_fold.
Hint Resolve paco1_3_1_fold.
Hint Resolve paco1_3_2_fold.
Hint Unfold monotone1_3.

