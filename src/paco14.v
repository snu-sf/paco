Require Export paconotation pacotacuser.
Require Import paconotation_internal pacotac pacon.
Set Implicit Arguments.

Section PACO14.

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
Variable T13 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) (x12: @T12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11), Type.

Record sig14T :=
  exist14T { 
      proj14T0: @T0;
      proj14T1: @T1 proj14T0;
      proj14T2: @T2 proj14T0 proj14T1;
      proj14T3: @T3 proj14T0 proj14T1 proj14T2;
      proj14T4: @T4 proj14T0 proj14T1 proj14T2 proj14T3;
      proj14T5: @T5 proj14T0 proj14T1 proj14T2 proj14T3 proj14T4;
      proj14T6: @T6 proj14T0 proj14T1 proj14T2 proj14T3 proj14T4 proj14T5;
      proj14T7: @T7 proj14T0 proj14T1 proj14T2 proj14T3 proj14T4 proj14T5 proj14T6;
      proj14T8: @T8 proj14T0 proj14T1 proj14T2 proj14T3 proj14T4 proj14T5 proj14T6 proj14T7;
      proj14T9: @T9 proj14T0 proj14T1 proj14T2 proj14T3 proj14T4 proj14T5 proj14T6 proj14T7 proj14T8;
      proj14T10: @T10 proj14T0 proj14T1 proj14T2 proj14T3 proj14T4 proj14T5 proj14T6 proj14T7 proj14T8 proj14T9;
      proj14T11: @T11 proj14T0 proj14T1 proj14T2 proj14T3 proj14T4 proj14T5 proj14T6 proj14T7 proj14T8 proj14T9 proj14T10;
      proj14T12: @T12 proj14T0 proj14T1 proj14T2 proj14T3 proj14T4 proj14T5 proj14T6 proj14T7 proj14T8 proj14T9 proj14T10 proj14T11;
      proj14T13: @T13 proj14T0 proj14T1 proj14T2 proj14T3 proj14T4 proj14T5 proj14T6 proj14T7 proj14T8 proj14T9 proj14T10 proj14T11 proj14T12;
    }.

Definition uncurry14 (R: rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13): rel1 sig14T := fun x => R (proj14T0 x) (proj14T1 x) (proj14T2 x) (proj14T3 x) (proj14T4 x) (proj14T5 x) (proj14T6 x) (proj14T7 x) (proj14T8 x) (proj14T9 x) (proj14T10 x) (proj14T11 x) (proj14T12 x) (proj14T13 x).

Definition curry14 (R: rel1 sig14T): rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 :=
  fun x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 => R (exist14T x13).

Lemma uncurry_map14 r0 r1 (LE : r0 <14== r1) : uncurry14 r0 <1== uncurry14 r1.
Proof. intros [] H. apply LE. apply H. Qed.

Lemma uncurry_map_rev14 r0 r1 (LE: uncurry14 r0 <1== uncurry14 r1) : r0 <14== r1.
Proof.
  repeat_intros 14. intros H. apply (LE (exist14T x13) H).
Qed.

Lemma curry_map14 r0 r1 (LE: r0 <1== r1) : curry14 r0 <14== curry14 r1.
Proof. 
  repeat_intros 14. intros H. apply (LE (exist14T x13) H).
Qed.

Lemma curry_map_rev14 r0 r1 (LE: curry14 r0 <14== curry14 r1) : r0 <1== r1.
Proof. 
  intros [] H. apply LE. apply H.
Qed.

Lemma uncurry_bij1_14 r : curry14 (uncurry14 r) <14== r.
Proof. unfold le14. repeat_intros 14. intros H. apply H. Qed.

Lemma uncurry_bij2_14 r : r <14== curry14 (uncurry14 r).
Proof. unfold le14. repeat_intros 14. intros H. apply H. Qed.

Lemma curry_bij1_14 r : uncurry14 (curry14 r) <1== r.
Proof. intros []. intro H. apply H. Qed.

Lemma curry_bij2_14 r : r <1== uncurry14 (curry14 r).
Proof. intros []. intro H. apply H. Qed.

Lemma uncurry_adjoint1_14 r0 r1 (LE: uncurry14 r0 <1== r1) : r0 <14== curry14 r1.
Proof.
  apply uncurry_map_rev14. eapply le1_trans; [apply LE|]. apply curry_bij2_14.
Qed.

Lemma uncurry_adjoint2_14 r0 r1 (LE: r0 <14== curry14 r1) : uncurry14 r0 <1== r1.
Proof.
  apply curry_map_rev14. eapply le14_trans; [|apply LE]. apply uncurry_bij2_14.
Qed.

Lemma curry_adjoint1_14 r0 r1 (LE: curry14 r0 <14== r1) : r0 <1== uncurry14 r1.
Proof.
  apply curry_map_rev14. eapply le14_trans; [apply LE|]. apply uncurry_bij2_14.
Qed.

Lemma curry_adjoint2_14 r0 r1 (LE: r0 <1== uncurry14 r1) : curry14 r0 <14== r1.
Proof.
  apply uncurry_map_rev14. eapply le1_trans; [|apply LE]. apply curry_bij1_14.
Qed.

(** ** Predicates of Arity 14
*)

Section Arg14_def.
Variable gf : rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13.
Arguments gf : clear implicits.

Definition paco14( r: rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13) : rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 :=
  curry14 (paco (fun R0 => uncurry14 (gf (curry14 R0))) (uncurry14 r)).

Definition upaco14( r: rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13) := paco14 r \14/ r.
End Arg14_def.
Arguments paco14 : clear implicits.
Arguments upaco14 : clear implicits.
Hint Unfold upaco14.

Section Arg14_2_def.
Variable gf_0 gf_1 : rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.

Definition paco14_2_0( r_0 r_1: rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13) : rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 :=
  curry14 (paco_2_0 (fun R0 R1 => uncurry14 (gf_0 (curry14 R0) (curry14 R1))) (fun R0 R1 => uncurry14 (gf_1 (curry14 R0) (curry14 R1))) (uncurry14 r_0) (uncurry14 r_1)).

Definition paco14_2_1( r_0 r_1: rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13) : rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 :=
  curry14 (paco_2_1 (fun R0 R1 => uncurry14 (gf_0 (curry14 R0) (curry14 R1))) (fun R0 R1 => uncurry14 (gf_1 (curry14 R0) (curry14 R1))) (uncurry14 r_0) (uncurry14 r_1)).

Definition upaco14_2_0( r_0 r_1: rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13) := paco14_2_0 r_0 r_1 \14/ r_0.
Definition upaco14_2_1( r_0 r_1: rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13) := paco14_2_1 r_0 r_1 \14/ r_1.
End Arg14_2_def.
Arguments paco14_2_0 : clear implicits.
Arguments upaco14_2_0 : clear implicits.
Hint Unfold upaco14_2_0.
Arguments paco14_2_1 : clear implicits.
Arguments upaco14_2_1 : clear implicits.
Hint Unfold upaco14_2_1.

Section Arg14_3_def.
Variable gf_0 gf_1 gf_2 : rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.
Arguments gf_2 : clear implicits.

Definition paco14_3_0( r_0 r_1 r_2: rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13) : rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 :=
  curry14 (paco_3_0 (fun R0 R1 R2 => uncurry14 (gf_0 (curry14 R0) (curry14 R1) (curry14 R2))) (fun R0 R1 R2 => uncurry14 (gf_1 (curry14 R0) (curry14 R1) (curry14 R2))) (fun R0 R1 R2 => uncurry14 (gf_2 (curry14 R0) (curry14 R1) (curry14 R2))) (uncurry14 r_0) (uncurry14 r_1) (uncurry14 r_2)).

Definition paco14_3_1( r_0 r_1 r_2: rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13) : rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 :=
  curry14 (paco_3_1 (fun R0 R1 R2 => uncurry14 (gf_0 (curry14 R0) (curry14 R1) (curry14 R2))) (fun R0 R1 R2 => uncurry14 (gf_1 (curry14 R0) (curry14 R1) (curry14 R2))) (fun R0 R1 R2 => uncurry14 (gf_2 (curry14 R0) (curry14 R1) (curry14 R2))) (uncurry14 r_0) (uncurry14 r_1) (uncurry14 r_2)).

Definition paco14_3_2( r_0 r_1 r_2: rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13) : rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 :=
  curry14 (paco_3_2 (fun R0 R1 R2 => uncurry14 (gf_0 (curry14 R0) (curry14 R1) (curry14 R2))) (fun R0 R1 R2 => uncurry14 (gf_1 (curry14 R0) (curry14 R1) (curry14 R2))) (fun R0 R1 R2 => uncurry14 (gf_2 (curry14 R0) (curry14 R1) (curry14 R2))) (uncurry14 r_0) (uncurry14 r_1) (uncurry14 r_2)).

Definition upaco14_3_0( r_0 r_1 r_2: rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13) := paco14_3_0 r_0 r_1 r_2 \14/ r_0.
Definition upaco14_3_1( r_0 r_1 r_2: rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13) := paco14_3_1 r_0 r_1 r_2 \14/ r_1.
Definition upaco14_3_2( r_0 r_1 r_2: rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13) := paco14_3_2 r_0 r_1 r_2 \14/ r_2.
End Arg14_3_def.
Arguments paco14_3_0 : clear implicits.
Arguments upaco14_3_0 : clear implicits.
Hint Unfold upaco14_3_0.
Arguments paco14_3_1 : clear implicits.
Arguments upaco14_3_1 : clear implicits.
Hint Unfold upaco14_3_1.
Arguments paco14_3_2 : clear implicits.
Arguments upaco14_3_2 : clear implicits.
Hint Unfold upaco14_3_2.

(** 1 Mutual Coinduction *)

Section Arg14_1.

Definition monotone14 (gf: rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13) :=
  forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 r r' (IN: gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) (LE: r <14= r'), gf r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13.

Definition _monotone14 (gf: rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13) :=
  forall r r'(LE: r <14= r'), gf r <14== gf r'.

Lemma monotone14_eq (gf: rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13) :
  monotone14 gf <-> _monotone14 gf.
Proof. unfold monotone14, _monotone14, le14. split; intros; eapply H; eassumption. Qed.

Lemma monotone14_map (gf: rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13)
      (MON: _monotone14 gf) :
  _monotone (fun R0 => uncurry14 (gf (curry14 R0))).
Proof.
  repeat_intros 3. apply uncurry_map14. apply MON; apply curry_map14; assumption.
Qed.

Variable gf : rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13.
Arguments gf : clear implicits.

Theorem _paco14_mon: _monotone14 (paco14 gf).
Proof.
  repeat_intros 3. eapply curry_map14, _paco_mon; apply uncurry_map14; assumption.
Qed.

Theorem _paco14_acc: forall
  l r (OBG: forall rr (INC: r <14== rr) (CIH: l <14== rr), l <14== paco14 gf rr),
  l <14== paco14 gf r.
Proof.
  intros. apply uncurry_adjoint1_14.
  eapply _paco_acc. intros.
  apply uncurry_adjoint1_14 in INC. apply uncurry_adjoint1_14 in CIH.
  apply uncurry_adjoint2_14.
  eapply le14_trans. eapply (OBG _ INC CIH).
  apply curry_map14.
  apply _paco_mon; try apply le1_refl; apply curry_bij1_14.
Qed.

Theorem _paco14_mult_strong: forall r,
  paco14 gf (upaco14 gf r) <14== paco14 gf r.
Proof.
  intros. apply curry_map14.
  eapply le1_trans; [| eapply _paco_mult_strong].
  apply _paco_mon; intros []; intros H; apply H.
Qed.

Theorem _paco14_fold: forall r,
  gf (upaco14 gf r) <14== paco14 gf r.
Proof.
  intros. apply uncurry_adjoint1_14.
  eapply le1_trans; [| apply _paco_fold]. apply le1_refl.
Qed.

Theorem _paco14_unfold: forall (MON: _monotone14 gf) r,
  paco14 gf r <14== gf (upaco14 gf r).
Proof.
  intros. apply curry_adjoint2_14.
  eapply _paco_unfold; apply monotone14_map; assumption.
Qed.

Theorem paco14_acc: forall
  l r (OBG: forall rr (INC: r <14= rr) (CIH: l <14= rr), l <14= paco14 gf rr),
  l <14= paco14 gf r.
Proof.
  apply _paco14_acc.
Qed.

Theorem paco14_mon: monotone14 (paco14 gf).
Proof.
  apply monotone14_eq.
  apply _paco14_mon.
Qed.

Theorem upaco14_mon: monotone14 (upaco14 gf).
Proof.
  repeat_intros 16. intros R  LE0.
  destruct R.
  - left. eapply paco14_mon. apply H. apply LE0.
  - right. apply LE0, H.
Qed.
Theorem paco14_mult_strong: forall r,
  paco14 gf (upaco14 gf r) <14= paco14 gf r.
Proof.
  apply _paco14_mult_strong.
Qed.

Corollary paco14_mult: forall r,
  paco14 gf (paco14 gf r) <14= paco14 gf r.
Proof. intros; eapply paco14_mult_strong, paco14_mon; [apply PR|..]; intros; left; assumption. Qed.

Theorem paco14_fold: forall r,
  gf (upaco14 gf r) <14= paco14 gf r.
Proof.
  apply _paco14_fold.
Qed.

Theorem paco14_unfold: forall (MON: monotone14 gf) r,
  paco14 gf r <14= gf (upaco14 gf r).
Proof.
  repeat_intros 1. eapply _paco14_unfold; apply monotone14_eq; assumption.
Qed.

End Arg14_1.

Arguments paco14_acc : clear implicits.
Arguments paco14_mon : clear implicits.
Arguments upaco14_mon : clear implicits.
Arguments paco14_mult_strong : clear implicits.
Arguments paco14_mult : clear implicits.
Arguments paco14_fold : clear implicits.
Arguments paco14_unfold : clear implicits.

Global Instance paco14_inst  (gf : rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13->_) r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : paco_class (paco14 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) :=
{ pacoacc    := paco14_acc gf;
  pacomult   := paco14_mult gf;
  pacofold   := paco14_fold gf;
  pacounfold := paco14_unfold gf }.

(** 2 Mutual Coinduction *)

Section Arg14_2.

Definition monotone14_2 (gf: rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13) :=
  forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 r_0 r_1 r'_0 r'_1 (IN: gf r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) (LE_0: r_0 <14= r'_0)(LE_1: r_1 <14= r'_1), gf r'_0 r'_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13.

Definition _monotone14_2 (gf: rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13) :=
  forall r_0 r_1 r'_0 r'_1(LE_0: r_0 <14= r'_0)(LE_1: r_1 <14= r'_1), gf r_0 r_1 <14== gf r'_0 r'_1.

Lemma monotone14_2_eq (gf: rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13) :
  monotone14_2 gf <-> _monotone14_2 gf.
Proof. unfold monotone14_2, _monotone14_2, le14. split; intros; eapply H; eassumption. Qed.

Lemma monotone14_2_map (gf: rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13)
      (MON: _monotone14_2 gf) :
  _monotone_2 (fun R0 R1 => uncurry14 (gf (curry14 R0) (curry14 R1))).
Proof.
  repeat_intros 6. apply uncurry_map14. apply MON; apply curry_map14; assumption.
Qed.

Variable gf_0 gf_1 : rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.

Theorem _paco14_2_0_mon: _monotone14_2 (paco14_2_0 gf_0 gf_1).
Proof.
  repeat_intros 6. eapply curry_map14, _paco_2_0_mon; apply uncurry_map14; assumption.
Qed.

Theorem _paco14_2_1_mon: _monotone14_2 (paco14_2_1 gf_0 gf_1).
Proof.
  repeat_intros 6. eapply curry_map14, _paco_2_1_mon; apply uncurry_map14; assumption.
Qed.

Theorem _paco14_2_0_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_0 <14== rr) (CIH: l <14== rr), l <14== paco14_2_0 gf_0 gf_1 rr r_1),
  l <14== paco14_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_14.
  eapply _paco_2_0_acc. intros.
  apply uncurry_adjoint1_14 in INC. apply uncurry_adjoint1_14 in CIH.
  apply uncurry_adjoint2_14.
  eapply le14_trans. eapply (OBG _ INC CIH).
  apply curry_map14.
  apply _paco_2_0_mon; try apply le1_refl; apply curry_bij1_14.
Qed.

Theorem _paco14_2_1_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_1 <14== rr) (CIH: l <14== rr), l <14== paco14_2_1 gf_0 gf_1 r_0 rr),
  l <14== paco14_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_14.
  eapply _paco_2_1_acc. intros.
  apply uncurry_adjoint1_14 in INC. apply uncurry_adjoint1_14 in CIH.
  apply uncurry_adjoint2_14.
  eapply le14_trans. eapply (OBG _ INC CIH).
  apply curry_map14.
  apply _paco_2_1_mon; try apply le1_refl; apply curry_bij1_14.
Qed.

Theorem _paco14_2_0_mult_strong: forall r_0 r_1,
  paco14_2_0 gf_0 gf_1 (upaco14_2_0 gf_0 gf_1 r_0 r_1) (upaco14_2_1 gf_0 gf_1 r_0 r_1) <14== paco14_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply curry_map14.
  eapply le1_trans; [| eapply _paco_2_0_mult_strong].
  apply _paco_2_0_mon; intros []; intros H; apply H.
Qed.

Theorem _paco14_2_1_mult_strong: forall r_0 r_1,
  paco14_2_1 gf_0 gf_1 (upaco14_2_0 gf_0 gf_1 r_0 r_1) (upaco14_2_1 gf_0 gf_1 r_0 r_1) <14== paco14_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply curry_map14.
  eapply le1_trans; [| eapply _paco_2_1_mult_strong].
  apply _paco_2_1_mon; intros []; intros H; apply H.
Qed.

Theorem _paco14_2_0_fold: forall r_0 r_1,
  gf_0 (upaco14_2_0 gf_0 gf_1 r_0 r_1) (upaco14_2_1 gf_0 gf_1 r_0 r_1) <14== paco14_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_14.
  eapply le1_trans; [| apply _paco_2_0_fold]. apply le1_refl.
Qed.

Theorem _paco14_2_1_fold: forall r_0 r_1,
  gf_1 (upaco14_2_0 gf_0 gf_1 r_0 r_1) (upaco14_2_1 gf_0 gf_1 r_0 r_1) <14== paco14_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_14.
  eapply le1_trans; [| apply _paco_2_1_fold]. apply le1_refl.
Qed.

Theorem _paco14_2_0_unfold: forall (MON: _monotone14_2 gf_0) (MON: _monotone14_2 gf_1) r_0 r_1,
  paco14_2_0 gf_0 gf_1 r_0 r_1 <14== gf_0 (upaco14_2_0 gf_0 gf_1 r_0 r_1) (upaco14_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  intros. apply curry_adjoint2_14.
  eapply _paco_2_0_unfold; apply monotone14_2_map; assumption.
Qed.

Theorem _paco14_2_1_unfold: forall (MON: _monotone14_2 gf_0) (MON: _monotone14_2 gf_1) r_0 r_1,
  paco14_2_1 gf_0 gf_1 r_0 r_1 <14== gf_1 (upaco14_2_0 gf_0 gf_1 r_0 r_1) (upaco14_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  intros. apply curry_adjoint2_14.
  eapply _paco_2_1_unfold; apply monotone14_2_map; assumption.
Qed.

Theorem paco14_2_0_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_0 <14= rr) (CIH: l <14= rr), l <14= paco14_2_0 gf_0 gf_1 rr r_1),
  l <14= paco14_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco14_2_0_acc.
Qed.

Theorem paco14_2_1_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_1 <14= rr) (CIH: l <14= rr), l <14= paco14_2_1 gf_0 gf_1 r_0 rr),
  l <14= paco14_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco14_2_1_acc.
Qed.

Theorem paco14_2_0_mon: monotone14_2 (paco14_2_0 gf_0 gf_1).
Proof.
  apply monotone14_2_eq.
  apply _paco14_2_0_mon.
Qed.

Theorem paco14_2_1_mon: monotone14_2 (paco14_2_1 gf_0 gf_1).
Proof.
  apply monotone14_2_eq.
  apply _paco14_2_1_mon.
Qed.

Theorem upaco14_2_0_mon: monotone14_2 (upaco14_2_0 gf_0 gf_1).
Proof.
  repeat_intros 18. intros R  LE0 LE1.
  destruct R.
  - left. eapply paco14_2_0_mon. apply H. apply LE0. apply LE1.
  - right. apply LE0, H.
Qed.
Theorem upaco14_2_1_mon: monotone14_2 (upaco14_2_1 gf_0 gf_1).
Proof.
  repeat_intros 18. intros R  LE0 LE1.
  destruct R.
  - left. eapply paco14_2_1_mon. apply H. apply LE0. apply LE1.
  - right. apply LE1, H.
Qed.
Theorem paco14_2_0_mult_strong: forall r_0 r_1,
  paco14_2_0 gf_0 gf_1 (upaco14_2_0 gf_0 gf_1 r_0 r_1) (upaco14_2_1 gf_0 gf_1 r_0 r_1) <14= paco14_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco14_2_0_mult_strong.
Qed.

Theorem paco14_2_1_mult_strong: forall r_0 r_1,
  paco14_2_1 gf_0 gf_1 (upaco14_2_0 gf_0 gf_1 r_0 r_1) (upaco14_2_1 gf_0 gf_1 r_0 r_1) <14= paco14_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco14_2_1_mult_strong.
Qed.

Corollary paco14_2_0_mult: forall r_0 r_1,
  paco14_2_0 gf_0 gf_1 (paco14_2_0 gf_0 gf_1 r_0 r_1) (paco14_2_1 gf_0 gf_1 r_0 r_1) <14= paco14_2_0 gf_0 gf_1 r_0 r_1.
Proof. intros; eapply paco14_2_0_mult_strong, paco14_2_0_mon; [apply PR|..]; intros; left; assumption. Qed.

Corollary paco14_2_1_mult: forall r_0 r_1,
  paco14_2_1 gf_0 gf_1 (paco14_2_0 gf_0 gf_1 r_0 r_1) (paco14_2_1 gf_0 gf_1 r_0 r_1) <14= paco14_2_1 gf_0 gf_1 r_0 r_1.
Proof. intros; eapply paco14_2_1_mult_strong, paco14_2_1_mon; [apply PR|..]; intros; left; assumption. Qed.

Theorem paco14_2_0_fold: forall r_0 r_1,
  gf_0 (upaco14_2_0 gf_0 gf_1 r_0 r_1) (upaco14_2_1 gf_0 gf_1 r_0 r_1) <14= paco14_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco14_2_0_fold.
Qed.

Theorem paco14_2_1_fold: forall r_0 r_1,
  gf_1 (upaco14_2_0 gf_0 gf_1 r_0 r_1) (upaco14_2_1 gf_0 gf_1 r_0 r_1) <14= paco14_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco14_2_1_fold.
Qed.

Theorem paco14_2_0_unfold: forall (MON: monotone14_2 gf_0) (MON: monotone14_2 gf_1) r_0 r_1,
  paco14_2_0 gf_0 gf_1 r_0 r_1 <14= gf_0 (upaco14_2_0 gf_0 gf_1 r_0 r_1) (upaco14_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  repeat_intros 2. eapply _paco14_2_0_unfold; apply monotone14_2_eq; assumption.
Qed.

Theorem paco14_2_1_unfold: forall (MON: monotone14_2 gf_0) (MON: monotone14_2 gf_1) r_0 r_1,
  paco14_2_1 gf_0 gf_1 r_0 r_1 <14= gf_1 (upaco14_2_0 gf_0 gf_1 r_0 r_1) (upaco14_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  repeat_intros 2. eapply _paco14_2_1_unfold; apply monotone14_2_eq; assumption.
Qed.

End Arg14_2.

Arguments paco14_2_0_acc : clear implicits.
Arguments paco14_2_1_acc : clear implicits.
Arguments paco14_2_0_mon : clear implicits.
Arguments paco14_2_1_mon : clear implicits.
Arguments upaco14_2_0_mon : clear implicits.
Arguments upaco14_2_1_mon : clear implicits.
Arguments paco14_2_0_mult_strong : clear implicits.
Arguments paco14_2_1_mult_strong : clear implicits.
Arguments paco14_2_0_mult : clear implicits.
Arguments paco14_2_1_mult : clear implicits.
Arguments paco14_2_0_fold : clear implicits.
Arguments paco14_2_1_fold : clear implicits.
Arguments paco14_2_0_unfold : clear implicits.
Arguments paco14_2_1_unfold : clear implicits.

Global Instance paco14_2_0_inst  (gf_0 gf_1 : rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13->_) r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : paco_class (paco14_2_0 gf_0 gf_1 r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) :=
{ pacoacc    := paco14_2_0_acc gf_0 gf_1;
  pacomult   := paco14_2_0_mult gf_0 gf_1;
  pacofold   := paco14_2_0_fold gf_0 gf_1;
  pacounfold := paco14_2_0_unfold gf_0 gf_1 }.

Global Instance paco14_2_1_inst  (gf_0 gf_1 : rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13->_) r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : paco_class (paco14_2_1 gf_0 gf_1 r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) :=
{ pacoacc    := paco14_2_1_acc gf_0 gf_1;
  pacomult   := paco14_2_1_mult gf_0 gf_1;
  pacofold   := paco14_2_1_fold gf_0 gf_1;
  pacounfold := paco14_2_1_unfold gf_0 gf_1 }.

(** 3 Mutual Coinduction *)

Section Arg14_3.

Definition monotone14_3 (gf: rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13) :=
  forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 r_0 r_1 r_2 r'_0 r'_1 r'_2 (IN: gf r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) (LE_0: r_0 <14= r'_0)(LE_1: r_1 <14= r'_1)(LE_2: r_2 <14= r'_2), gf r'_0 r'_1 r'_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13.

Definition _monotone14_3 (gf: rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13) :=
  forall r_0 r_1 r_2 r'_0 r'_1 r'_2(LE_0: r_0 <14= r'_0)(LE_1: r_1 <14= r'_1)(LE_2: r_2 <14= r'_2), gf r_0 r_1 r_2 <14== gf r'_0 r'_1 r'_2.

Lemma monotone14_3_eq (gf: rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13) :
  monotone14_3 gf <-> _monotone14_3 gf.
Proof. unfold monotone14_3, _monotone14_3, le14. split; intros; eapply H; eassumption. Qed.

Lemma monotone14_3_map (gf: rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13)
      (MON: _monotone14_3 gf) :
  _monotone_3 (fun R0 R1 R2 => uncurry14 (gf (curry14 R0) (curry14 R1) (curry14 R2))).
Proof.
  repeat_intros 9. apply uncurry_map14. apply MON; apply curry_map14; assumption.
Qed.

Variable gf_0 gf_1 gf_2 : rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.
Arguments gf_2 : clear implicits.

Theorem _paco14_3_0_mon: _monotone14_3 (paco14_3_0 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 9. eapply curry_map14, _paco_3_0_mon; apply uncurry_map14; assumption.
Qed.

Theorem _paco14_3_1_mon: _monotone14_3 (paco14_3_1 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 9. eapply curry_map14, _paco_3_1_mon; apply uncurry_map14; assumption.
Qed.

Theorem _paco14_3_2_mon: _monotone14_3 (paco14_3_2 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 9. eapply curry_map14, _paco_3_2_mon; apply uncurry_map14; assumption.
Qed.

Theorem _paco14_3_0_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_0 <14== rr) (CIH: l <14== rr), l <14== paco14_3_0 gf_0 gf_1 gf_2 rr r_1 r_2),
  l <14== paco14_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_14.
  eapply _paco_3_0_acc. intros.
  apply uncurry_adjoint1_14 in INC. apply uncurry_adjoint1_14 in CIH.
  apply uncurry_adjoint2_14.
  eapply le14_trans. eapply (OBG _ INC CIH).
  apply curry_map14.
  apply _paco_3_0_mon; try apply le1_refl; apply curry_bij1_14.
Qed.

Theorem _paco14_3_1_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_1 <14== rr) (CIH: l <14== rr), l <14== paco14_3_1 gf_0 gf_1 gf_2 r_0 rr r_2),
  l <14== paco14_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_14.
  eapply _paco_3_1_acc. intros.
  apply uncurry_adjoint1_14 in INC. apply uncurry_adjoint1_14 in CIH.
  apply uncurry_adjoint2_14.
  eapply le14_trans. eapply (OBG _ INC CIH).
  apply curry_map14.
  apply _paco_3_1_mon; try apply le1_refl; apply curry_bij1_14.
Qed.

Theorem _paco14_3_2_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_2 <14== rr) (CIH: l <14== rr), l <14== paco14_3_2 gf_0 gf_1 gf_2 r_0 r_1 rr),
  l <14== paco14_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_14.
  eapply _paco_3_2_acc. intros.
  apply uncurry_adjoint1_14 in INC. apply uncurry_adjoint1_14 in CIH.
  apply uncurry_adjoint2_14.
  eapply le14_trans. eapply (OBG _ INC CIH).
  apply curry_map14.
  apply _paco_3_2_mon; try apply le1_refl; apply curry_bij1_14.
Qed.

Theorem _paco14_3_0_mult_strong: forall r_0 r_1 r_2,
  paco14_3_0 gf_0 gf_1 gf_2 (upaco14_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco14_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco14_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <14== paco14_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply curry_map14.
  eapply le1_trans; [| eapply _paco_3_0_mult_strong].
  apply _paco_3_0_mon; intros []; intros H; apply H.
Qed.

Theorem _paco14_3_1_mult_strong: forall r_0 r_1 r_2,
  paco14_3_1 gf_0 gf_1 gf_2 (upaco14_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco14_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco14_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <14== paco14_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply curry_map14.
  eapply le1_trans; [| eapply _paco_3_1_mult_strong].
  apply _paco_3_1_mon; intros []; intros H; apply H.
Qed.

Theorem _paco14_3_2_mult_strong: forall r_0 r_1 r_2,
  paco14_3_2 gf_0 gf_1 gf_2 (upaco14_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco14_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco14_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <14== paco14_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply curry_map14.
  eapply le1_trans; [| eapply _paco_3_2_mult_strong].
  apply _paco_3_2_mon; intros []; intros H; apply H.
Qed.

Theorem _paco14_3_0_fold: forall r_0 r_1 r_2,
  gf_0 (upaco14_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco14_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco14_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <14== paco14_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_14.
  eapply le1_trans; [| apply _paco_3_0_fold]. apply le1_refl.
Qed.

Theorem _paco14_3_1_fold: forall r_0 r_1 r_2,
  gf_1 (upaco14_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco14_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco14_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <14== paco14_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_14.
  eapply le1_trans; [| apply _paco_3_1_fold]. apply le1_refl.
Qed.

Theorem _paco14_3_2_fold: forall r_0 r_1 r_2,
  gf_2 (upaco14_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco14_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco14_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <14== paco14_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_14.
  eapply le1_trans; [| apply _paco_3_2_fold]. apply le1_refl.
Qed.

Theorem _paco14_3_0_unfold: forall (MON: _monotone14_3 gf_0) (MON: _monotone14_3 gf_1) (MON: _monotone14_3 gf_2) r_0 r_1 r_2,
  paco14_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 <14== gf_0 (upaco14_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco14_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco14_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  intros. apply curry_adjoint2_14.
  eapply _paco_3_0_unfold; apply monotone14_3_map; assumption.
Qed.

Theorem _paco14_3_1_unfold: forall (MON: _monotone14_3 gf_0) (MON: _monotone14_3 gf_1) (MON: _monotone14_3 gf_2) r_0 r_1 r_2,
  paco14_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 <14== gf_1 (upaco14_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco14_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco14_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  intros. apply curry_adjoint2_14.
  eapply _paco_3_1_unfold; apply monotone14_3_map; assumption.
Qed.

Theorem _paco14_3_2_unfold: forall (MON: _monotone14_3 gf_0) (MON: _monotone14_3 gf_1) (MON: _monotone14_3 gf_2) r_0 r_1 r_2,
  paco14_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 <14== gf_2 (upaco14_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco14_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco14_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  intros. apply curry_adjoint2_14.
  eapply _paco_3_2_unfold; apply monotone14_3_map; assumption.
Qed.

Theorem paco14_3_0_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_0 <14= rr) (CIH: l <14= rr), l <14= paco14_3_0 gf_0 gf_1 gf_2 rr r_1 r_2),
  l <14= paco14_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco14_3_0_acc.
Qed.

Theorem paco14_3_1_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_1 <14= rr) (CIH: l <14= rr), l <14= paco14_3_1 gf_0 gf_1 gf_2 r_0 rr r_2),
  l <14= paco14_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco14_3_1_acc.
Qed.

Theorem paco14_3_2_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_2 <14= rr) (CIH: l <14= rr), l <14= paco14_3_2 gf_0 gf_1 gf_2 r_0 r_1 rr),
  l <14= paco14_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco14_3_2_acc.
Qed.

Theorem paco14_3_0_mon: monotone14_3 (paco14_3_0 gf_0 gf_1 gf_2).
Proof.
  apply monotone14_3_eq.
  apply _paco14_3_0_mon.
Qed.

Theorem paco14_3_1_mon: monotone14_3 (paco14_3_1 gf_0 gf_1 gf_2).
Proof.
  apply monotone14_3_eq.
  apply _paco14_3_1_mon.
Qed.

Theorem paco14_3_2_mon: monotone14_3 (paco14_3_2 gf_0 gf_1 gf_2).
Proof.
  apply monotone14_3_eq.
  apply _paco14_3_2_mon.
Qed.

Theorem upaco14_3_0_mon: monotone14_3 (upaco14_3_0 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 20. intros R  LE0 LE1 LE2.
  destruct R.
  - left. eapply paco14_3_0_mon. apply H. apply LE0. apply LE1. apply LE2.
  - right. apply LE0, H.
Qed.
Theorem upaco14_3_1_mon: monotone14_3 (upaco14_3_1 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 20. intros R  LE0 LE1 LE2.
  destruct R.
  - left. eapply paco14_3_1_mon. apply H. apply LE0. apply LE1. apply LE2.
  - right. apply LE1, H.
Qed.
Theorem upaco14_3_2_mon: monotone14_3 (upaco14_3_2 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 20. intros R  LE0 LE1 LE2.
  destruct R.
  - left. eapply paco14_3_2_mon. apply H. apply LE0. apply LE1. apply LE2.
  - right. apply LE2, H.
Qed.
Theorem paco14_3_0_mult_strong: forall r_0 r_1 r_2,
  paco14_3_0 gf_0 gf_1 gf_2 (upaco14_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco14_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco14_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <14= paco14_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco14_3_0_mult_strong.
Qed.

Theorem paco14_3_1_mult_strong: forall r_0 r_1 r_2,
  paco14_3_1 gf_0 gf_1 gf_2 (upaco14_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco14_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco14_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <14= paco14_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco14_3_1_mult_strong.
Qed.

Theorem paco14_3_2_mult_strong: forall r_0 r_1 r_2,
  paco14_3_2 gf_0 gf_1 gf_2 (upaco14_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco14_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco14_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <14= paco14_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco14_3_2_mult_strong.
Qed.

Corollary paco14_3_0_mult: forall r_0 r_1 r_2,
  paco14_3_0 gf_0 gf_1 gf_2 (paco14_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco14_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco14_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <14= paco14_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco14_3_0_mult_strong, paco14_3_0_mon; [apply PR|..]; intros; left; assumption. Qed.

Corollary paco14_3_1_mult: forall r_0 r_1 r_2,
  paco14_3_1 gf_0 gf_1 gf_2 (paco14_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco14_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco14_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <14= paco14_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco14_3_1_mult_strong, paco14_3_1_mon; [apply PR|..]; intros; left; assumption. Qed.

Corollary paco14_3_2_mult: forall r_0 r_1 r_2,
  paco14_3_2 gf_0 gf_1 gf_2 (paco14_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco14_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco14_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <14= paco14_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco14_3_2_mult_strong, paco14_3_2_mon; [apply PR|..]; intros; left; assumption. Qed.

Theorem paco14_3_0_fold: forall r_0 r_1 r_2,
  gf_0 (upaco14_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco14_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco14_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <14= paco14_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco14_3_0_fold.
Qed.

Theorem paco14_3_1_fold: forall r_0 r_1 r_2,
  gf_1 (upaco14_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco14_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco14_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <14= paco14_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco14_3_1_fold.
Qed.

Theorem paco14_3_2_fold: forall r_0 r_1 r_2,
  gf_2 (upaco14_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco14_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco14_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <14= paco14_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco14_3_2_fold.
Qed.

Theorem paco14_3_0_unfold: forall (MON: monotone14_3 gf_0) (MON: monotone14_3 gf_1) (MON: monotone14_3 gf_2) r_0 r_1 r_2,
  paco14_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 <14= gf_0 (upaco14_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco14_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco14_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  repeat_intros 3. eapply _paco14_3_0_unfold; apply monotone14_3_eq; assumption.
Qed.

Theorem paco14_3_1_unfold: forall (MON: monotone14_3 gf_0) (MON: monotone14_3 gf_1) (MON: monotone14_3 gf_2) r_0 r_1 r_2,
  paco14_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 <14= gf_1 (upaco14_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco14_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco14_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  repeat_intros 3. eapply _paco14_3_1_unfold; apply monotone14_3_eq; assumption.
Qed.

Theorem paco14_3_2_unfold: forall (MON: monotone14_3 gf_0) (MON: monotone14_3 gf_1) (MON: monotone14_3 gf_2) r_0 r_1 r_2,
  paco14_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 <14= gf_2 (upaco14_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco14_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco14_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  repeat_intros 3. eapply _paco14_3_2_unfold; apply monotone14_3_eq; assumption.
Qed.

End Arg14_3.

Arguments paco14_3_0_acc : clear implicits.
Arguments paco14_3_1_acc : clear implicits.
Arguments paco14_3_2_acc : clear implicits.
Arguments paco14_3_0_mon : clear implicits.
Arguments paco14_3_1_mon : clear implicits.
Arguments paco14_3_2_mon : clear implicits.
Arguments upaco14_3_0_mon : clear implicits.
Arguments upaco14_3_1_mon : clear implicits.
Arguments upaco14_3_2_mon : clear implicits.
Arguments paco14_3_0_mult_strong : clear implicits.
Arguments paco14_3_1_mult_strong : clear implicits.
Arguments paco14_3_2_mult_strong : clear implicits.
Arguments paco14_3_0_mult : clear implicits.
Arguments paco14_3_1_mult : clear implicits.
Arguments paco14_3_2_mult : clear implicits.
Arguments paco14_3_0_fold : clear implicits.
Arguments paco14_3_1_fold : clear implicits.
Arguments paco14_3_2_fold : clear implicits.
Arguments paco14_3_0_unfold : clear implicits.
Arguments paco14_3_1_unfold : clear implicits.
Arguments paco14_3_2_unfold : clear implicits.

Global Instance paco14_3_0_inst  (gf_0 gf_1 gf_2 : rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : paco_class (paco14_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) :=
{ pacoacc    := paco14_3_0_acc gf_0 gf_1 gf_2;
  pacomult   := paco14_3_0_mult gf_0 gf_1 gf_2;
  pacofold   := paco14_3_0_fold gf_0 gf_1 gf_2;
  pacounfold := paco14_3_0_unfold gf_0 gf_1 gf_2 }.

Global Instance paco14_3_1_inst  (gf_0 gf_1 gf_2 : rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : paco_class (paco14_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) :=
{ pacoacc    := paco14_3_1_acc gf_0 gf_1 gf_2;
  pacomult   := paco14_3_1_mult gf_0 gf_1 gf_2;
  pacofold   := paco14_3_1_fold gf_0 gf_1 gf_2;
  pacounfold := paco14_3_1_unfold gf_0 gf_1 gf_2 }.

Global Instance paco14_3_2_inst  (gf_0 gf_1 gf_2 : rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : paco_class (paco14_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) :=
{ pacoacc    := paco14_3_2_acc gf_0 gf_1 gf_2;
  pacomult   := paco14_3_2_mult gf_0 gf_1 gf_2;
  pacofold   := paco14_3_2_fold gf_0 gf_1 gf_2;
  pacounfold := paco14_3_2_unfold gf_0 gf_1 gf_2 }.

End PACO14.

Global Opaque paco14.

Hint Unfold upaco14.
Hint Resolve paco14_fold.
Hint Unfold monotone14.

Global Opaque paco14_2_0.
Global Opaque paco14_2_1.

Hint Unfold upaco14_2_0.
Hint Unfold upaco14_2_1.
Hint Resolve paco14_2_0_fold.
Hint Resolve paco14_2_1_fold.
Hint Unfold monotone14_2.

Global Opaque paco14_3_0.
Global Opaque paco14_3_1.
Global Opaque paco14_3_2.

Hint Unfold upaco14_3_0.
Hint Unfold upaco14_3_1.
Hint Unfold upaco14_3_2.
Hint Resolve paco14_3_0_fold.
Hint Resolve paco14_3_1_fold.
Hint Resolve paco14_3_2_fold.
Hint Unfold monotone14_3.

