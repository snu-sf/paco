Require Export paconotation pacotacuser.
Require Import paconotation_internal pacotac pacon.
Set Implicit Arguments.

Section PACO13.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
Variable T7 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5), Type.
Variable T8 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6), Type.
Variable T9 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7), Type.
Variable T10 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8), Type.
Variable T11 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9), Type.
Variable T12 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10), Type.

Record sig13T :=
  exist13T { 
      proj13T0: @T0;
      proj13T1: @T1 proj13T0;
      proj13T2: @T2 proj13T0 proj13T1;
      proj13T3: @T3 proj13T0 proj13T1 proj13T2;
      proj13T4: @T4 proj13T0 proj13T1 proj13T2 proj13T3;
      proj13T5: @T5 proj13T0 proj13T1 proj13T2 proj13T3 proj13T4;
      proj13T6: @T6 proj13T0 proj13T1 proj13T2 proj13T3 proj13T4 proj13T5;
      proj13T7: @T7 proj13T0 proj13T1 proj13T2 proj13T3 proj13T4 proj13T5 proj13T6;
      proj13T8: @T8 proj13T0 proj13T1 proj13T2 proj13T3 proj13T4 proj13T5 proj13T6 proj13T7;
      proj13T9: @T9 proj13T0 proj13T1 proj13T2 proj13T3 proj13T4 proj13T5 proj13T6 proj13T7 proj13T8;
      proj13T10: @T10 proj13T0 proj13T1 proj13T2 proj13T3 proj13T4 proj13T5 proj13T6 proj13T7 proj13T8 proj13T9;
      proj13T11: @T11 proj13T0 proj13T1 proj13T2 proj13T3 proj13T4 proj13T5 proj13T6 proj13T7 proj13T8 proj13T9 proj13T10;
      proj13T12: @T12 proj13T0 proj13T1 proj13T2 proj13T3 proj13T4 proj13T5 proj13T6 proj13T7 proj13T8 proj13T9 proj13T10 proj13T11;
    }.

Definition uncurry13 (R: rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12): rel1 sig13T := fun x => R (proj13T0 x) (proj13T1 x) (proj13T2 x) (proj13T3 x) (proj13T4 x) (proj13T5 x) (proj13T6 x) (proj13T7 x) (proj13T8 x) (proj13T9 x) (proj13T10 x) (proj13T11 x) (proj13T12 x).

Definition curry13 (R: rel1 sig13T): rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 :=
  fun x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 => R (exist13T x12).

Lemma uncurry_map13 r0 r1 (LE : r0 <13== r1) : uncurry13 r0 <1== uncurry13 r1.
Proof. intros [] H. apply LE. auto. Qed.

Lemma uncurry_map_rev13 r0 r1 (LE: uncurry13 r0 <1== uncurry13 r1) : r0 <13== r1.
Proof.
  repeat_intros 13. intros H. apply (LE (exist13T x12) H).
Qed.

Lemma curry_map13 r0 r1 (LE: r0 <1== r1) : curry13 r0 <13== curry13 r1.
Proof. 
  repeat_intros 13. intros H. apply (LE (exist13T x12) H).
Qed.

Lemma curry_map_rev13 r0 r1 (LE: curry13 r0 <13== curry13 r1) : r0 <1== r1.
Proof. 
  intros [] H. apply LE. apply H.
Qed.

Lemma uncurry_bij1_13 r : curry13 (uncurry13 r) <13== r.
Proof. unfold le13. repeat_intros 13; auto. Qed.

Lemma uncurry_bij2_13 r : r <13== curry13 (uncurry13 r).
Proof. unfold le13. repeat_intros 13; auto. Qed.

Lemma curry_bij1_13 r : uncurry13 (curry13 r) <1== r.
Proof. intros []; auto. Qed.

Lemma curry_bij2_13 r : r <1== uncurry13 (curry13 r).
Proof. intros []; auto. Qed.

Lemma uncurry_adjoint1_13 r0 r1 (LE: uncurry13 r0 <1== r1) : r0 <13== curry13 r1.
Proof.
  apply uncurry_map_rev13. eapply le1_trans; [eauto|]. apply curry_bij2_13.
Qed.

Lemma uncurry_adjoint2_13 r0 r1 (LE: r0 <13== curry13 r1) : uncurry13 r0 <1== r1.
Proof.
  apply curry_map_rev13. eapply le13_trans; [|eauto]. apply uncurry_bij2_13.
Qed.

Lemma curry_adjoint1_13 r0 r1 (LE: curry13 r0 <13== r1) : r0 <1== uncurry13 r1.
Proof.
  apply curry_map_rev13. eapply le13_trans; [eauto|]. apply uncurry_bij2_13.
Qed.

Lemma curry_adjoint2_13 r0 r1 (LE: r0 <1== uncurry13 r1) : curry13 r0 <13== r1.
Proof.
  apply uncurry_map_rev13. eapply le1_trans; [|eauto]. apply curry_bij1_13.
Qed.

(** ** Predicates of Arity 13
*)

Section Arg13_def.
Variable gf : rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12.
Arguments gf : clear implicits.

Definition paco13( r: rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12) : rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 :=
  curry13 (paco (fun R0 => uncurry13 (gf (curry13 R0))) (uncurry13 r)).

Definition upaco13( r: rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12) := paco13 r \13/ r.
End Arg13_def.
Arguments paco13 : clear implicits.
Arguments upaco13 : clear implicits.
Hint Unfold upaco13.

Section Arg13_2_def.
Variable gf_0 gf_1 : rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.

Definition paco13_2_0( r_0 r_1: rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12) : rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 :=
  curry13 (paco_2_0 (fun R0 R1 => uncurry13 (gf_0 (curry13 R0) (curry13 R1))) (fun R0 R1 => uncurry13 (gf_1 (curry13 R0) (curry13 R1))) (uncurry13 r_0) (uncurry13 r_1)).

Definition paco13_2_1( r_0 r_1: rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12) : rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 :=
  curry13 (paco_2_1 (fun R0 R1 => uncurry13 (gf_0 (curry13 R0) (curry13 R1))) (fun R0 R1 => uncurry13 (gf_1 (curry13 R0) (curry13 R1))) (uncurry13 r_0) (uncurry13 r_1)).

Definition upaco13_2_0( r_0 r_1: rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12) := paco13_2_0 r_0 r_1 \13/ r_0.
Definition upaco13_2_1( r_0 r_1: rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12) := paco13_2_1 r_0 r_1 \13/ r_1.
End Arg13_2_def.
Arguments paco13_2_0 : clear implicits.
Arguments upaco13_2_0 : clear implicits.
Hint Unfold upaco13_2_0.
Arguments paco13_2_1 : clear implicits.
Arguments upaco13_2_1 : clear implicits.
Hint Unfold upaco13_2_1.

Section Arg13_3_def.
Variable gf_0 gf_1 gf_2 : rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.
Arguments gf_2 : clear implicits.

Definition paco13_3_0( r_0 r_1 r_2: rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12) : rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 :=
  curry13 (paco_3_0 (fun R0 R1 R2 => uncurry13 (gf_0 (curry13 R0) (curry13 R1) (curry13 R2))) (fun R0 R1 R2 => uncurry13 (gf_1 (curry13 R0) (curry13 R1) (curry13 R2))) (fun R0 R1 R2 => uncurry13 (gf_2 (curry13 R0) (curry13 R1) (curry13 R2))) (uncurry13 r_0) (uncurry13 r_1) (uncurry13 r_2)).

Definition paco13_3_1( r_0 r_1 r_2: rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12) : rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 :=
  curry13 (paco_3_1 (fun R0 R1 R2 => uncurry13 (gf_0 (curry13 R0) (curry13 R1) (curry13 R2))) (fun R0 R1 R2 => uncurry13 (gf_1 (curry13 R0) (curry13 R1) (curry13 R2))) (fun R0 R1 R2 => uncurry13 (gf_2 (curry13 R0) (curry13 R1) (curry13 R2))) (uncurry13 r_0) (uncurry13 r_1) (uncurry13 r_2)).

Definition paco13_3_2( r_0 r_1 r_2: rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12) : rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 :=
  curry13 (paco_3_2 (fun R0 R1 R2 => uncurry13 (gf_0 (curry13 R0) (curry13 R1) (curry13 R2))) (fun R0 R1 R2 => uncurry13 (gf_1 (curry13 R0) (curry13 R1) (curry13 R2))) (fun R0 R1 R2 => uncurry13 (gf_2 (curry13 R0) (curry13 R1) (curry13 R2))) (uncurry13 r_0) (uncurry13 r_1) (uncurry13 r_2)).

Definition upaco13_3_0( r_0 r_1 r_2: rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12) := paco13_3_0 r_0 r_1 r_2 \13/ r_0.
Definition upaco13_3_1( r_0 r_1 r_2: rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12) := paco13_3_1 r_0 r_1 r_2 \13/ r_1.
Definition upaco13_3_2( r_0 r_1 r_2: rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12) := paco13_3_2 r_0 r_1 r_2 \13/ r_2.
End Arg13_3_def.
Arguments paco13_3_0 : clear implicits.
Arguments upaco13_3_0 : clear implicits.
Hint Unfold upaco13_3_0.
Arguments paco13_3_1 : clear implicits.
Arguments upaco13_3_1 : clear implicits.
Hint Unfold upaco13_3_1.
Arguments paco13_3_2 : clear implicits.
Arguments upaco13_3_2 : clear implicits.
Hint Unfold upaco13_3_2.

(** 1 Mutual Coinduction *)

Section Arg13_1.

Definition monotone13 (gf: rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12) :=
  forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 r r' (IN: gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) (LE: r <13= r'), gf r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12.

Definition _monotone13 (gf: rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12) :=
  forall r r'(LE: r <13= r'), gf r <13== gf r'.

Lemma monotone13_eq (gf: rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12) :
  monotone13 gf <-> _monotone13 gf.
Proof. unfold monotone13, _monotone13, le13. split; eauto. Qed.

Lemma monotone13_map (gf: rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12)
      (MON: _monotone13 gf) :
  _monotone (fun R0 => uncurry13 (gf (curry13 R0))).
Proof.
  repeat_intros 3. apply uncurry_map13. apply MON; apply curry_map13; auto.
Qed.

Variable gf : rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12.
Arguments gf : clear implicits.

Theorem _paco13_mon: _monotone13 (paco13 gf).
Proof.
  repeat_intros 3. eapply curry_map13, _paco_mon; apply uncurry_map13; auto.
Qed.

Theorem _paco13_acc: forall
  l r (OBG: forall rr (INC: r <13== rr) (CIH: l <13== rr), l <13== paco13 gf rr),
  l <13== paco13 gf r.
Proof.
  intros. apply uncurry_adjoint1_13.
  eapply _paco_acc. intros.
  apply uncurry_adjoint1_13 in INC. apply uncurry_adjoint1_13 in CIH.
  apply uncurry_adjoint2_13.
  eapply le13_trans. eapply (OBG _ INC CIH).
  apply curry_map13.
  apply _paco_mon; try apply le1_refl; apply curry_bij1_13.
Qed.

Theorem _paco13_mult_strong: forall r,
  paco13 gf (upaco13 gf r) <13== paco13 gf r.
Proof.
  intros. apply curry_map13.
  eapply le1_trans; [| eapply _paco_mult_strong].
  apply _paco_mon; intros []; eauto.
Qed.

Theorem _paco13_fold: forall r,
  gf (upaco13 gf r) <13== paco13 gf r.
Proof.
  intros. apply uncurry_adjoint1_13.
  eapply le1_trans; [| apply _paco_fold]. apply le1_refl.
Qed.

Theorem _paco13_unfold: forall (MON: _monotone13 gf) r,
  paco13 gf r <13== gf (upaco13 gf r).
Proof.
  intros. apply curry_adjoint2_13.
  eapply _paco_unfold; apply monotone13_map; auto.
Qed.

Theorem paco13_acc: forall
  l r (OBG: forall rr (INC: r <13= rr) (CIH: l <13= rr), l <13= paco13 gf rr),
  l <13= paco13 gf r.
Proof.
  apply _paco13_acc.
Qed.

Theorem paco13_mon: monotone13 (paco13 gf).
Proof.
  apply monotone13_eq.
  apply _paco13_mon.
Qed.

Theorem paco13_mult_strong: forall r,
  paco13 gf (upaco13 gf r) <13= paco13 gf r.
Proof.
  apply _paco13_mult_strong.
Qed.

Corollary paco13_mult: forall r,
  paco13 gf (paco13 gf r) <13= paco13 gf r.
Proof. intros; eapply paco13_mult_strong, paco13_mon; eauto. Qed.

Theorem paco13_fold: forall r,
  gf (upaco13 gf r) <13= paco13 gf r.
Proof.
  apply _paco13_fold.
Qed.

Theorem paco13_unfold: forall (MON: monotone13 gf) r,
  paco13 gf r <13= gf (upaco13 gf r).
Proof.
  repeat_intros 1. eapply _paco13_unfold; apply monotone13_eq; auto.
Qed.

End Arg13_1.

Arguments paco13_acc : clear implicits.
Arguments paco13_mon : clear implicits.
Arguments paco13_mult_strong : clear implicits.
Arguments paco13_mult : clear implicits.
Arguments paco13_fold : clear implicits.
Arguments paco13_unfold : clear implicits.

Global Instance paco13_inst  (gf : rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12->_) r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : paco_class (paco13 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) :=
{ pacoacc    := paco13_acc gf;
  pacomult   := paco13_mult gf;
  pacofold   := paco13_fold gf;
  pacounfold := paco13_unfold gf }.

(** 2 Mutual Coinduction *)

Section Arg13_2.

Definition monotone13_2 (gf: rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12) :=
  forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 r_0 r_1 r'_0 r'_1 (IN: gf r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) (LE_0: r_0 <13= r'_0)(LE_1: r_1 <13= r'_1), gf r'_0 r'_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12.

Definition _monotone13_2 (gf: rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12) :=
  forall r_0 r_1 r'_0 r'_1(LE_0: r_0 <13= r'_0)(LE_1: r_1 <13= r'_1), gf r_0 r_1 <13== gf r'_0 r'_1.

Lemma monotone13_2_eq (gf: rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12) :
  monotone13_2 gf <-> _monotone13_2 gf.
Proof. unfold monotone13_2, _monotone13_2, le13. split; eauto. Qed.

Lemma monotone13_2_map (gf: rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12)
      (MON: _monotone13_2 gf) :
  _monotone_2 (fun R0 R1 => uncurry13 (gf (curry13 R0) (curry13 R1))).
Proof.
  repeat_intros 6. apply uncurry_map13. apply MON; apply curry_map13; auto.
Qed.

Variable gf_0 gf_1 : rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.

Theorem _paco13_2_0_mon: _monotone13_2 (paco13_2_0 gf_0 gf_1).
Proof.
  repeat_intros 6. eapply curry_map13, _paco_2_0_mon; apply uncurry_map13; auto.
Qed.

Theorem _paco13_2_1_mon: _monotone13_2 (paco13_2_1 gf_0 gf_1).
Proof.
  repeat_intros 6. eapply curry_map13, _paco_2_1_mon; apply uncurry_map13; auto.
Qed.

Theorem _paco13_2_0_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_0 <13== rr) (CIH: l <13== rr), l <13== paco13_2_0 gf_0 gf_1 rr r_1),
  l <13== paco13_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_13.
  eapply _paco_2_0_acc. intros.
  apply uncurry_adjoint1_13 in INC. apply uncurry_adjoint1_13 in CIH.
  apply uncurry_adjoint2_13.
  eapply le13_trans. eapply (OBG _ INC CIH).
  apply curry_map13.
  apply _paco_2_0_mon; try apply le1_refl; apply curry_bij1_13.
Qed.

Theorem _paco13_2_1_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_1 <13== rr) (CIH: l <13== rr), l <13== paco13_2_1 gf_0 gf_1 r_0 rr),
  l <13== paco13_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_13.
  eapply _paco_2_1_acc. intros.
  apply uncurry_adjoint1_13 in INC. apply uncurry_adjoint1_13 in CIH.
  apply uncurry_adjoint2_13.
  eapply le13_trans. eapply (OBG _ INC CIH).
  apply curry_map13.
  apply _paco_2_1_mon; try apply le1_refl; apply curry_bij1_13.
Qed.

Theorem _paco13_2_0_mult_strong: forall r_0 r_1,
  paco13_2_0 gf_0 gf_1 (upaco13_2_0 gf_0 gf_1 r_0 r_1) (upaco13_2_1 gf_0 gf_1 r_0 r_1) <13== paco13_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply curry_map13.
  eapply le1_trans; [| eapply _paco_2_0_mult_strong].
  apply _paco_2_0_mon; intros []; eauto.
Qed.

Theorem _paco13_2_1_mult_strong: forall r_0 r_1,
  paco13_2_1 gf_0 gf_1 (upaco13_2_0 gf_0 gf_1 r_0 r_1) (upaco13_2_1 gf_0 gf_1 r_0 r_1) <13== paco13_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply curry_map13.
  eapply le1_trans; [| eapply _paco_2_1_mult_strong].
  apply _paco_2_1_mon; intros []; eauto.
Qed.

Theorem _paco13_2_0_fold: forall r_0 r_1,
  gf_0 (upaco13_2_0 gf_0 gf_1 r_0 r_1) (upaco13_2_1 gf_0 gf_1 r_0 r_1) <13== paco13_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_13.
  eapply le1_trans; [| apply _paco_2_0_fold]. apply le1_refl.
Qed.

Theorem _paco13_2_1_fold: forall r_0 r_1,
  gf_1 (upaco13_2_0 gf_0 gf_1 r_0 r_1) (upaco13_2_1 gf_0 gf_1 r_0 r_1) <13== paco13_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_13.
  eapply le1_trans; [| apply _paco_2_1_fold]. apply le1_refl.
Qed.

Theorem _paco13_2_0_unfold: forall (MON: _monotone13_2 gf_0) (MON: _monotone13_2 gf_1) r_0 r_1,
  paco13_2_0 gf_0 gf_1 r_0 r_1 <13== gf_0 (upaco13_2_0 gf_0 gf_1 r_0 r_1) (upaco13_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  intros. apply curry_adjoint2_13.
  eapply _paco_2_0_unfold; apply monotone13_2_map; auto.
Qed.

Theorem _paco13_2_1_unfold: forall (MON: _monotone13_2 gf_0) (MON: _monotone13_2 gf_1) r_0 r_1,
  paco13_2_1 gf_0 gf_1 r_0 r_1 <13== gf_1 (upaco13_2_0 gf_0 gf_1 r_0 r_1) (upaco13_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  intros. apply curry_adjoint2_13.
  eapply _paco_2_1_unfold; apply monotone13_2_map; auto.
Qed.

Theorem paco13_2_0_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_0 <13= rr) (CIH: l <13= rr), l <13= paco13_2_0 gf_0 gf_1 rr r_1),
  l <13= paco13_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco13_2_0_acc.
Qed.

Theorem paco13_2_1_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_1 <13= rr) (CIH: l <13= rr), l <13= paco13_2_1 gf_0 gf_1 r_0 rr),
  l <13= paco13_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco13_2_1_acc.
Qed.

Theorem paco13_2_0_mon: monotone13_2 (paco13_2_0 gf_0 gf_1).
Proof.
  apply monotone13_2_eq.
  apply _paco13_2_0_mon.
Qed.

Theorem paco13_2_1_mon: monotone13_2 (paco13_2_1 gf_0 gf_1).
Proof.
  apply monotone13_2_eq.
  apply _paco13_2_1_mon.
Qed.

Theorem paco13_2_0_mult_strong: forall r_0 r_1,
  paco13_2_0 gf_0 gf_1 (upaco13_2_0 gf_0 gf_1 r_0 r_1) (upaco13_2_1 gf_0 gf_1 r_0 r_1) <13= paco13_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco13_2_0_mult_strong.
Qed.

Theorem paco13_2_1_mult_strong: forall r_0 r_1,
  paco13_2_1 gf_0 gf_1 (upaco13_2_0 gf_0 gf_1 r_0 r_1) (upaco13_2_1 gf_0 gf_1 r_0 r_1) <13= paco13_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco13_2_1_mult_strong.
Qed.

Corollary paco13_2_0_mult: forall r_0 r_1,
  paco13_2_0 gf_0 gf_1 (paco13_2_0 gf_0 gf_1 r_0 r_1) (paco13_2_1 gf_0 gf_1 r_0 r_1) <13= paco13_2_0 gf_0 gf_1 r_0 r_1.
Proof. intros; eapply paco13_2_0_mult_strong, paco13_2_0_mon; eauto. Qed.

Corollary paco13_2_1_mult: forall r_0 r_1,
  paco13_2_1 gf_0 gf_1 (paco13_2_0 gf_0 gf_1 r_0 r_1) (paco13_2_1 gf_0 gf_1 r_0 r_1) <13= paco13_2_1 gf_0 gf_1 r_0 r_1.
Proof. intros; eapply paco13_2_1_mult_strong, paco13_2_1_mon; eauto. Qed.

Theorem paco13_2_0_fold: forall r_0 r_1,
  gf_0 (upaco13_2_0 gf_0 gf_1 r_0 r_1) (upaco13_2_1 gf_0 gf_1 r_0 r_1) <13= paco13_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco13_2_0_fold.
Qed.

Theorem paco13_2_1_fold: forall r_0 r_1,
  gf_1 (upaco13_2_0 gf_0 gf_1 r_0 r_1) (upaco13_2_1 gf_0 gf_1 r_0 r_1) <13= paco13_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco13_2_1_fold.
Qed.

Theorem paco13_2_0_unfold: forall (MON: monotone13_2 gf_0) (MON: monotone13_2 gf_1) r_0 r_1,
  paco13_2_0 gf_0 gf_1 r_0 r_1 <13= gf_0 (upaco13_2_0 gf_0 gf_1 r_0 r_1) (upaco13_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  repeat_intros 2. eapply _paco13_2_0_unfold; apply monotone13_2_eq; auto.
Qed.

Theorem paco13_2_1_unfold: forall (MON: monotone13_2 gf_0) (MON: monotone13_2 gf_1) r_0 r_1,
  paco13_2_1 gf_0 gf_1 r_0 r_1 <13= gf_1 (upaco13_2_0 gf_0 gf_1 r_0 r_1) (upaco13_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  repeat_intros 2. eapply _paco13_2_1_unfold; apply monotone13_2_eq; auto.
Qed.

End Arg13_2.

Arguments paco13_2_0_acc : clear implicits.
Arguments paco13_2_1_acc : clear implicits.
Arguments paco13_2_0_mon : clear implicits.
Arguments paco13_2_1_mon : clear implicits.
Arguments paco13_2_0_mult_strong : clear implicits.
Arguments paco13_2_1_mult_strong : clear implicits.
Arguments paco13_2_0_mult : clear implicits.
Arguments paco13_2_1_mult : clear implicits.
Arguments paco13_2_0_fold : clear implicits.
Arguments paco13_2_1_fold : clear implicits.
Arguments paco13_2_0_unfold : clear implicits.
Arguments paco13_2_1_unfold : clear implicits.

Global Instance paco13_2_0_inst  (gf_0 gf_1 : rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12->_) r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : paco_class (paco13_2_0 gf_0 gf_1 r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) :=
{ pacoacc    := paco13_2_0_acc gf_0 gf_1;
  pacomult   := paco13_2_0_mult gf_0 gf_1;
  pacofold   := paco13_2_0_fold gf_0 gf_1;
  pacounfold := paco13_2_0_unfold gf_0 gf_1 }.

Global Instance paco13_2_1_inst  (gf_0 gf_1 : rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12->_) r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : paco_class (paco13_2_1 gf_0 gf_1 r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) :=
{ pacoacc    := paco13_2_1_acc gf_0 gf_1;
  pacomult   := paco13_2_1_mult gf_0 gf_1;
  pacofold   := paco13_2_1_fold gf_0 gf_1;
  pacounfold := paco13_2_1_unfold gf_0 gf_1 }.

(** 3 Mutual Coinduction *)

Section Arg13_3.

Definition monotone13_3 (gf: rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12) :=
  forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 r_0 r_1 r_2 r'_0 r'_1 r'_2 (IN: gf r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) (LE_0: r_0 <13= r'_0)(LE_1: r_1 <13= r'_1)(LE_2: r_2 <13= r'_2), gf r'_0 r'_1 r'_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12.

Definition _monotone13_3 (gf: rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12) :=
  forall r_0 r_1 r_2 r'_0 r'_1 r'_2(LE_0: r_0 <13= r'_0)(LE_1: r_1 <13= r'_1)(LE_2: r_2 <13= r'_2), gf r_0 r_1 r_2 <13== gf r'_0 r'_1 r'_2.

Lemma monotone13_3_eq (gf: rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12) :
  monotone13_3 gf <-> _monotone13_3 gf.
Proof. unfold monotone13_3, _monotone13_3, le13. split; eauto. Qed.

Lemma monotone13_3_map (gf: rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12)
      (MON: _monotone13_3 gf) :
  _monotone_3 (fun R0 R1 R2 => uncurry13 (gf (curry13 R0) (curry13 R1) (curry13 R2))).
Proof.
  repeat_intros 9. apply uncurry_map13. apply MON; apply curry_map13; auto.
Qed.

Variable gf_0 gf_1 gf_2 : rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.
Arguments gf_2 : clear implicits.

Theorem _paco13_3_0_mon: _monotone13_3 (paco13_3_0 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 9. eapply curry_map13, _paco_3_0_mon; apply uncurry_map13; auto.
Qed.

Theorem _paco13_3_1_mon: _monotone13_3 (paco13_3_1 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 9. eapply curry_map13, _paco_3_1_mon; apply uncurry_map13; auto.
Qed.

Theorem _paco13_3_2_mon: _monotone13_3 (paco13_3_2 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 9. eapply curry_map13, _paco_3_2_mon; apply uncurry_map13; auto.
Qed.

Theorem _paco13_3_0_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_0 <13== rr) (CIH: l <13== rr), l <13== paco13_3_0 gf_0 gf_1 gf_2 rr r_1 r_2),
  l <13== paco13_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_13.
  eapply _paco_3_0_acc. intros.
  apply uncurry_adjoint1_13 in INC. apply uncurry_adjoint1_13 in CIH.
  apply uncurry_adjoint2_13.
  eapply le13_trans. eapply (OBG _ INC CIH).
  apply curry_map13.
  apply _paco_3_0_mon; try apply le1_refl; apply curry_bij1_13.
Qed.

Theorem _paco13_3_1_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_1 <13== rr) (CIH: l <13== rr), l <13== paco13_3_1 gf_0 gf_1 gf_2 r_0 rr r_2),
  l <13== paco13_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_13.
  eapply _paco_3_1_acc. intros.
  apply uncurry_adjoint1_13 in INC. apply uncurry_adjoint1_13 in CIH.
  apply uncurry_adjoint2_13.
  eapply le13_trans. eapply (OBG _ INC CIH).
  apply curry_map13.
  apply _paco_3_1_mon; try apply le1_refl; apply curry_bij1_13.
Qed.

Theorem _paco13_3_2_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_2 <13== rr) (CIH: l <13== rr), l <13== paco13_3_2 gf_0 gf_1 gf_2 r_0 r_1 rr),
  l <13== paco13_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_13.
  eapply _paco_3_2_acc. intros.
  apply uncurry_adjoint1_13 in INC. apply uncurry_adjoint1_13 in CIH.
  apply uncurry_adjoint2_13.
  eapply le13_trans. eapply (OBG _ INC CIH).
  apply curry_map13.
  apply _paco_3_2_mon; try apply le1_refl; apply curry_bij1_13.
Qed.

Theorem _paco13_3_0_mult_strong: forall r_0 r_1 r_2,
  paco13_3_0 gf_0 gf_1 gf_2 (upaco13_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco13_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco13_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <13== paco13_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply curry_map13.
  eapply le1_trans; [| eapply _paco_3_0_mult_strong].
  apply _paco_3_0_mon; intros []; eauto.
Qed.

Theorem _paco13_3_1_mult_strong: forall r_0 r_1 r_2,
  paco13_3_1 gf_0 gf_1 gf_2 (upaco13_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco13_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco13_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <13== paco13_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply curry_map13.
  eapply le1_trans; [| eapply _paco_3_1_mult_strong].
  apply _paco_3_1_mon; intros []; eauto.
Qed.

Theorem _paco13_3_2_mult_strong: forall r_0 r_1 r_2,
  paco13_3_2 gf_0 gf_1 gf_2 (upaco13_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco13_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco13_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <13== paco13_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply curry_map13.
  eapply le1_trans; [| eapply _paco_3_2_mult_strong].
  apply _paco_3_2_mon; intros []; eauto.
Qed.

Theorem _paco13_3_0_fold: forall r_0 r_1 r_2,
  gf_0 (upaco13_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco13_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco13_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <13== paco13_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_13.
  eapply le1_trans; [| apply _paco_3_0_fold]. apply le1_refl.
Qed.

Theorem _paco13_3_1_fold: forall r_0 r_1 r_2,
  gf_1 (upaco13_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco13_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco13_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <13== paco13_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_13.
  eapply le1_trans; [| apply _paco_3_1_fold]. apply le1_refl.
Qed.

Theorem _paco13_3_2_fold: forall r_0 r_1 r_2,
  gf_2 (upaco13_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco13_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco13_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <13== paco13_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_13.
  eapply le1_trans; [| apply _paco_3_2_fold]. apply le1_refl.
Qed.

Theorem _paco13_3_0_unfold: forall (MON: _monotone13_3 gf_0) (MON: _monotone13_3 gf_1) (MON: _monotone13_3 gf_2) r_0 r_1 r_2,
  paco13_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 <13== gf_0 (upaco13_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco13_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco13_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  intros. apply curry_adjoint2_13.
  eapply _paco_3_0_unfold; apply monotone13_3_map; auto.
Qed.

Theorem _paco13_3_1_unfold: forall (MON: _monotone13_3 gf_0) (MON: _monotone13_3 gf_1) (MON: _monotone13_3 gf_2) r_0 r_1 r_2,
  paco13_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 <13== gf_1 (upaco13_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco13_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco13_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  intros. apply curry_adjoint2_13.
  eapply _paco_3_1_unfold; apply monotone13_3_map; auto.
Qed.

Theorem _paco13_3_2_unfold: forall (MON: _monotone13_3 gf_0) (MON: _monotone13_3 gf_1) (MON: _monotone13_3 gf_2) r_0 r_1 r_2,
  paco13_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 <13== gf_2 (upaco13_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco13_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco13_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  intros. apply curry_adjoint2_13.
  eapply _paco_3_2_unfold; apply monotone13_3_map; auto.
Qed.

Theorem paco13_3_0_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_0 <13= rr) (CIH: l <13= rr), l <13= paco13_3_0 gf_0 gf_1 gf_2 rr r_1 r_2),
  l <13= paco13_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco13_3_0_acc.
Qed.

Theorem paco13_3_1_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_1 <13= rr) (CIH: l <13= rr), l <13= paco13_3_1 gf_0 gf_1 gf_2 r_0 rr r_2),
  l <13= paco13_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco13_3_1_acc.
Qed.

Theorem paco13_3_2_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_2 <13= rr) (CIH: l <13= rr), l <13= paco13_3_2 gf_0 gf_1 gf_2 r_0 r_1 rr),
  l <13= paco13_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco13_3_2_acc.
Qed.

Theorem paco13_3_0_mon: monotone13_3 (paco13_3_0 gf_0 gf_1 gf_2).
Proof.
  apply monotone13_3_eq.
  apply _paco13_3_0_mon.
Qed.

Theorem paco13_3_1_mon: monotone13_3 (paco13_3_1 gf_0 gf_1 gf_2).
Proof.
  apply monotone13_3_eq.
  apply _paco13_3_1_mon.
Qed.

Theorem paco13_3_2_mon: monotone13_3 (paco13_3_2 gf_0 gf_1 gf_2).
Proof.
  apply monotone13_3_eq.
  apply _paco13_3_2_mon.
Qed.

Theorem paco13_3_0_mult_strong: forall r_0 r_1 r_2,
  paco13_3_0 gf_0 gf_1 gf_2 (upaco13_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco13_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco13_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <13= paco13_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco13_3_0_mult_strong.
Qed.

Theorem paco13_3_1_mult_strong: forall r_0 r_1 r_2,
  paco13_3_1 gf_0 gf_1 gf_2 (upaco13_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco13_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco13_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <13= paco13_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco13_3_1_mult_strong.
Qed.

Theorem paco13_3_2_mult_strong: forall r_0 r_1 r_2,
  paco13_3_2 gf_0 gf_1 gf_2 (upaco13_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco13_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco13_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <13= paco13_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco13_3_2_mult_strong.
Qed.

Corollary paco13_3_0_mult: forall r_0 r_1 r_2,
  paco13_3_0 gf_0 gf_1 gf_2 (paco13_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco13_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco13_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <13= paco13_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco13_3_0_mult_strong, paco13_3_0_mon; eauto. Qed.

Corollary paco13_3_1_mult: forall r_0 r_1 r_2,
  paco13_3_1 gf_0 gf_1 gf_2 (paco13_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco13_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco13_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <13= paco13_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco13_3_1_mult_strong, paco13_3_1_mon; eauto. Qed.

Corollary paco13_3_2_mult: forall r_0 r_1 r_2,
  paco13_3_2 gf_0 gf_1 gf_2 (paco13_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco13_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco13_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <13= paco13_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco13_3_2_mult_strong, paco13_3_2_mon; eauto. Qed.

Theorem paco13_3_0_fold: forall r_0 r_1 r_2,
  gf_0 (upaco13_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco13_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco13_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <13= paco13_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco13_3_0_fold.
Qed.

Theorem paco13_3_1_fold: forall r_0 r_1 r_2,
  gf_1 (upaco13_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco13_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco13_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <13= paco13_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco13_3_1_fold.
Qed.

Theorem paco13_3_2_fold: forall r_0 r_1 r_2,
  gf_2 (upaco13_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco13_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco13_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <13= paco13_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco13_3_2_fold.
Qed.

Theorem paco13_3_0_unfold: forall (MON: monotone13_3 gf_0) (MON: monotone13_3 gf_1) (MON: monotone13_3 gf_2) r_0 r_1 r_2,
  paco13_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 <13= gf_0 (upaco13_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco13_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco13_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  repeat_intros 3. eapply _paco13_3_0_unfold; apply monotone13_3_eq; auto.
Qed.

Theorem paco13_3_1_unfold: forall (MON: monotone13_3 gf_0) (MON: monotone13_3 gf_1) (MON: monotone13_3 gf_2) r_0 r_1 r_2,
  paco13_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 <13= gf_1 (upaco13_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco13_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco13_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  repeat_intros 3. eapply _paco13_3_1_unfold; apply monotone13_3_eq; auto.
Qed.

Theorem paco13_3_2_unfold: forall (MON: monotone13_3 gf_0) (MON: monotone13_3 gf_1) (MON: monotone13_3 gf_2) r_0 r_1 r_2,
  paco13_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 <13= gf_2 (upaco13_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco13_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco13_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  repeat_intros 3. eapply _paco13_3_2_unfold; apply monotone13_3_eq; auto.
Qed.

End Arg13_3.

Arguments paco13_3_0_acc : clear implicits.
Arguments paco13_3_1_acc : clear implicits.
Arguments paco13_3_2_acc : clear implicits.
Arguments paco13_3_0_mon : clear implicits.
Arguments paco13_3_1_mon : clear implicits.
Arguments paco13_3_2_mon : clear implicits.
Arguments paco13_3_0_mult_strong : clear implicits.
Arguments paco13_3_1_mult_strong : clear implicits.
Arguments paco13_3_2_mult_strong : clear implicits.
Arguments paco13_3_0_mult : clear implicits.
Arguments paco13_3_1_mult : clear implicits.
Arguments paco13_3_2_mult : clear implicits.
Arguments paco13_3_0_fold : clear implicits.
Arguments paco13_3_1_fold : clear implicits.
Arguments paco13_3_2_fold : clear implicits.
Arguments paco13_3_0_unfold : clear implicits.
Arguments paco13_3_1_unfold : clear implicits.
Arguments paco13_3_2_unfold : clear implicits.

Global Instance paco13_3_0_inst  (gf_0 gf_1 gf_2 : rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : paco_class (paco13_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) :=
{ pacoacc    := paco13_3_0_acc gf_0 gf_1 gf_2;
  pacomult   := paco13_3_0_mult gf_0 gf_1 gf_2;
  pacofold   := paco13_3_0_fold gf_0 gf_1 gf_2;
  pacounfold := paco13_3_0_unfold gf_0 gf_1 gf_2 }.

Global Instance paco13_3_1_inst  (gf_0 gf_1 gf_2 : rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : paco_class (paco13_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) :=
{ pacoacc    := paco13_3_1_acc gf_0 gf_1 gf_2;
  pacomult   := paco13_3_1_mult gf_0 gf_1 gf_2;
  pacofold   := paco13_3_1_fold gf_0 gf_1 gf_2;
  pacounfold := paco13_3_1_unfold gf_0 gf_1 gf_2 }.

Global Instance paco13_3_2_inst  (gf_0 gf_1 gf_2 : rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : paco_class (paco13_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) :=
{ pacoacc    := paco13_3_2_acc gf_0 gf_1 gf_2;
  pacomult   := paco13_3_2_mult gf_0 gf_1 gf_2;
  pacofold   := paco13_3_2_fold gf_0 gf_1 gf_2;
  pacounfold := paco13_3_2_unfold gf_0 gf_1 gf_2 }.

End PACO13.

Global Opaque paco13.

Hint Unfold upaco13.
Hint Resolve paco13_fold.
Hint Unfold monotone13.

Global Opaque paco13_2_0.
Global Opaque paco13_2_1.

Hint Unfold upaco13_2_0.
Hint Unfold upaco13_2_1.
Hint Resolve paco13_2_0_fold.
Hint Resolve paco13_2_1_fold.
Hint Unfold monotone13_2.

Global Opaque paco13_3_0.
Global Opaque paco13_3_1.
Global Opaque paco13_3_2.

Hint Unfold upaco13_3_0.
Hint Unfold upaco13_3_1.
Hint Unfold upaco13_3_2.
Hint Resolve paco13_3_0_fold.
Hint Resolve paco13_3_1_fold.
Hint Resolve paco13_3_2_fold.
Hint Unfold monotone13_3.

