Require Export paconotation pacotacuser.
Require Import paconotation_internal pacotac pacon.
Set Implicit Arguments.

Section PACO18.

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
Variable T14 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) (x12: @T12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) (x13: @T13 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12), Type.
Variable T15 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) (x12: @T12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) (x13: @T13 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) (x14: @T14 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13), Type.
Variable T16 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) (x12: @T12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) (x13: @T13 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) (x14: @T14 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) (x15: @T15 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14), Type.
Variable T17 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) (x12: @T12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) (x13: @T13 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) (x14: @T14 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) (x15: @T15 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14) (x16: @T16 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15), Type.

Record sig18T :=
  exist18T { 
      proj18T0: @T0;
      proj18T1: @T1 proj18T0;
      proj18T2: @T2 proj18T0 proj18T1;
      proj18T3: @T3 proj18T0 proj18T1 proj18T2;
      proj18T4: @T4 proj18T0 proj18T1 proj18T2 proj18T3;
      proj18T5: @T5 proj18T0 proj18T1 proj18T2 proj18T3 proj18T4;
      proj18T6: @T6 proj18T0 proj18T1 proj18T2 proj18T3 proj18T4 proj18T5;
      proj18T7: @T7 proj18T0 proj18T1 proj18T2 proj18T3 proj18T4 proj18T5 proj18T6;
      proj18T8: @T8 proj18T0 proj18T1 proj18T2 proj18T3 proj18T4 proj18T5 proj18T6 proj18T7;
      proj18T9: @T9 proj18T0 proj18T1 proj18T2 proj18T3 proj18T4 proj18T5 proj18T6 proj18T7 proj18T8;
      proj18T10: @T10 proj18T0 proj18T1 proj18T2 proj18T3 proj18T4 proj18T5 proj18T6 proj18T7 proj18T8 proj18T9;
      proj18T11: @T11 proj18T0 proj18T1 proj18T2 proj18T3 proj18T4 proj18T5 proj18T6 proj18T7 proj18T8 proj18T9 proj18T10;
      proj18T12: @T12 proj18T0 proj18T1 proj18T2 proj18T3 proj18T4 proj18T5 proj18T6 proj18T7 proj18T8 proj18T9 proj18T10 proj18T11;
      proj18T13: @T13 proj18T0 proj18T1 proj18T2 proj18T3 proj18T4 proj18T5 proj18T6 proj18T7 proj18T8 proj18T9 proj18T10 proj18T11 proj18T12;
      proj18T14: @T14 proj18T0 proj18T1 proj18T2 proj18T3 proj18T4 proj18T5 proj18T6 proj18T7 proj18T8 proj18T9 proj18T10 proj18T11 proj18T12 proj18T13;
      proj18T15: @T15 proj18T0 proj18T1 proj18T2 proj18T3 proj18T4 proj18T5 proj18T6 proj18T7 proj18T8 proj18T9 proj18T10 proj18T11 proj18T12 proj18T13 proj18T14;
      proj18T16: @T16 proj18T0 proj18T1 proj18T2 proj18T3 proj18T4 proj18T5 proj18T6 proj18T7 proj18T8 proj18T9 proj18T10 proj18T11 proj18T12 proj18T13 proj18T14 proj18T15;
      proj18T17: @T17 proj18T0 proj18T1 proj18T2 proj18T3 proj18T4 proj18T5 proj18T6 proj18T7 proj18T8 proj18T9 proj18T10 proj18T11 proj18T12 proj18T13 proj18T14 proj18T15 proj18T16;
    }.

Definition uncurry18 (R: rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17): rel1 sig18T := fun x => R (proj18T0 x) (proj18T1 x) (proj18T2 x) (proj18T3 x) (proj18T4 x) (proj18T5 x) (proj18T6 x) (proj18T7 x) (proj18T8 x) (proj18T9 x) (proj18T10 x) (proj18T11 x) (proj18T12 x) (proj18T13 x) (proj18T14 x) (proj18T15 x) (proj18T16 x) (proj18T17 x).

Definition curry18 (R: rel1 sig18T): rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 :=
  fun x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 => R (exist18T x17).

Lemma uncurry_map18 r0 r1 (LE : r0 <18== r1) : uncurry18 r0 <1== uncurry18 r1.
Proof. intros [] H. apply LE. apply H. Qed.

Lemma uncurry_map_rev18 r0 r1 (LE: uncurry18 r0 <1== uncurry18 r1) : r0 <18== r1.
Proof.
  repeat_intros 18. intros H. apply (LE (exist18T x17) H).
Qed.

Lemma curry_map18 r0 r1 (LE: r0 <1== r1) : curry18 r0 <18== curry18 r1.
Proof. 
  repeat_intros 18. intros H. apply (LE (exist18T x17) H).
Qed.

Lemma curry_map_rev18 r0 r1 (LE: curry18 r0 <18== curry18 r1) : r0 <1== r1.
Proof. 
  intros [] H. apply LE. apply H.
Qed.

Lemma uncurry_bij1_18 r : curry18 (uncurry18 r) <18== r.
Proof. unfold le18. repeat_intros 18. intros H. apply H. Qed.

Lemma uncurry_bij2_18 r : r <18== curry18 (uncurry18 r).
Proof. unfold le18. repeat_intros 18. intros H. apply H. Qed.

Lemma curry_bij1_18 r : uncurry18 (curry18 r) <1== r.
Proof. intros []. intro H. apply H. Qed.

Lemma curry_bij2_18 r : r <1== uncurry18 (curry18 r).
Proof. intros []. intro H. apply H. Qed.

Lemma uncurry_adjoint1_18 r0 r1 (LE: uncurry18 r0 <1== r1) : r0 <18== curry18 r1.
Proof.
  apply uncurry_map_rev18. eapply le1_trans; [apply LE|]. apply curry_bij2_18.
Qed.

Lemma uncurry_adjoint2_18 r0 r1 (LE: r0 <18== curry18 r1) : uncurry18 r0 <1== r1.
Proof.
  apply curry_map_rev18. eapply le18_trans; [|apply LE]. apply uncurry_bij2_18.
Qed.

Lemma curry_adjoint1_18 r0 r1 (LE: curry18 r0 <18== r1) : r0 <1== uncurry18 r1.
Proof.
  apply curry_map_rev18. eapply le18_trans; [apply LE|]. apply uncurry_bij2_18.
Qed.

Lemma curry_adjoint2_18 r0 r1 (LE: r0 <1== uncurry18 r1) : curry18 r0 <18== r1.
Proof.
  apply uncurry_map_rev18. eapply le1_trans; [|apply LE]. apply curry_bij1_18.
Qed.

(** ** Predicates of Arity 18
*)

Section Arg18_def.
Variable gf : rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 -> rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17.
Arguments gf : clear implicits.

Definition paco18( r: rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17) : rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 :=
  curry18 (paco (fun R0 => uncurry18 (gf (curry18 R0))) (uncurry18 r)).

Definition upaco18( r: rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17) := paco18 r \18/ r.
End Arg18_def.
Arguments paco18 : clear implicits.
Arguments upaco18 : clear implicits.
Hint Unfold upaco18.

Section Arg18_2_def.
Variable gf_0 gf_1 : rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 -> rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 -> rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.

Definition paco18_2_0( r_0 r_1: rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17) : rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 :=
  curry18 (paco_2_0 (fun R0 R1 => uncurry18 (gf_0 (curry18 R0) (curry18 R1))) (fun R0 R1 => uncurry18 (gf_1 (curry18 R0) (curry18 R1))) (uncurry18 r_0) (uncurry18 r_1)).

Definition paco18_2_1( r_0 r_1: rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17) : rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 :=
  curry18 (paco_2_1 (fun R0 R1 => uncurry18 (gf_0 (curry18 R0) (curry18 R1))) (fun R0 R1 => uncurry18 (gf_1 (curry18 R0) (curry18 R1))) (uncurry18 r_0) (uncurry18 r_1)).

Definition upaco18_2_0( r_0 r_1: rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17) := paco18_2_0 r_0 r_1 \18/ r_0.
Definition upaco18_2_1( r_0 r_1: rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17) := paco18_2_1 r_0 r_1 \18/ r_1.
End Arg18_2_def.
Arguments paco18_2_0 : clear implicits.
Arguments upaco18_2_0 : clear implicits.
Hint Unfold upaco18_2_0.
Arguments paco18_2_1 : clear implicits.
Arguments upaco18_2_1 : clear implicits.
Hint Unfold upaco18_2_1.

Section Arg18_3_def.
Variable gf_0 gf_1 gf_2 : rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 -> rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 -> rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 -> rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.
Arguments gf_2 : clear implicits.

Definition paco18_3_0( r_0 r_1 r_2: rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17) : rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 :=
  curry18 (paco_3_0 (fun R0 R1 R2 => uncurry18 (gf_0 (curry18 R0) (curry18 R1) (curry18 R2))) (fun R0 R1 R2 => uncurry18 (gf_1 (curry18 R0) (curry18 R1) (curry18 R2))) (fun R0 R1 R2 => uncurry18 (gf_2 (curry18 R0) (curry18 R1) (curry18 R2))) (uncurry18 r_0) (uncurry18 r_1) (uncurry18 r_2)).

Definition paco18_3_1( r_0 r_1 r_2: rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17) : rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 :=
  curry18 (paco_3_1 (fun R0 R1 R2 => uncurry18 (gf_0 (curry18 R0) (curry18 R1) (curry18 R2))) (fun R0 R1 R2 => uncurry18 (gf_1 (curry18 R0) (curry18 R1) (curry18 R2))) (fun R0 R1 R2 => uncurry18 (gf_2 (curry18 R0) (curry18 R1) (curry18 R2))) (uncurry18 r_0) (uncurry18 r_1) (uncurry18 r_2)).

Definition paco18_3_2( r_0 r_1 r_2: rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17) : rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 :=
  curry18 (paco_3_2 (fun R0 R1 R2 => uncurry18 (gf_0 (curry18 R0) (curry18 R1) (curry18 R2))) (fun R0 R1 R2 => uncurry18 (gf_1 (curry18 R0) (curry18 R1) (curry18 R2))) (fun R0 R1 R2 => uncurry18 (gf_2 (curry18 R0) (curry18 R1) (curry18 R2))) (uncurry18 r_0) (uncurry18 r_1) (uncurry18 r_2)).

Definition upaco18_3_0( r_0 r_1 r_2: rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17) := paco18_3_0 r_0 r_1 r_2 \18/ r_0.
Definition upaco18_3_1( r_0 r_1 r_2: rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17) := paco18_3_1 r_0 r_1 r_2 \18/ r_1.
Definition upaco18_3_2( r_0 r_1 r_2: rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17) := paco18_3_2 r_0 r_1 r_2 \18/ r_2.
End Arg18_3_def.
Arguments paco18_3_0 : clear implicits.
Arguments upaco18_3_0 : clear implicits.
Hint Unfold upaco18_3_0.
Arguments paco18_3_1 : clear implicits.
Arguments upaco18_3_1 : clear implicits.
Hint Unfold upaco18_3_1.
Arguments paco18_3_2 : clear implicits.
Arguments upaco18_3_2 : clear implicits.
Hint Unfold upaco18_3_2.

(** 1 Mutual Coinduction *)

Section Arg18_1.

Definition monotone18 (gf: rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 -> rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17) :=
  forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 r r' (IN: gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17) (LE: r <18= r'), gf r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17.

Definition _monotone18 (gf: rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 -> rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17) :=
  forall r r'(LE: r <18= r'), gf r <18== gf r'.

Lemma monotone18_eq (gf: rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 -> rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17) :
  monotone18 gf <-> _monotone18 gf.
Proof. unfold monotone18, _monotone18, le18. split; intros; eapply H; eassumption. Qed.

Lemma monotone18_map (gf: rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 -> rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17)
      (MON: _monotone18 gf) :
  _monotone (fun R0 => uncurry18 (gf (curry18 R0))).
Proof.
  repeat_intros 3. apply uncurry_map18. apply MON; apply curry_map18; assumption.
Qed.

Variable gf : rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 -> rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17.
Arguments gf : clear implicits.

Theorem _paco18_mon: _monotone18 (paco18 gf).
Proof.
  repeat_intros 3. eapply curry_map18, _paco_mon; apply uncurry_map18; assumption.
Qed.

Theorem _paco18_acc: forall
  l r (OBG: forall rr (INC: r <18== rr) (CIH: l <18== rr), l <18== paco18 gf rr),
  l <18== paco18 gf r.
Proof.
  intros. apply uncurry_adjoint1_18.
  eapply _paco_acc. intros.
  apply uncurry_adjoint1_18 in INC. apply uncurry_adjoint1_18 in CIH.
  apply uncurry_adjoint2_18.
  eapply le18_trans. eapply (OBG _ INC CIH).
  apply curry_map18.
  apply _paco_mon; try apply le1_refl; apply curry_bij1_18.
Qed.

Theorem _paco18_mult_strong: forall r,
  paco18 gf (upaco18 gf r) <18== paco18 gf r.
Proof.
  intros. apply curry_map18.
  eapply le1_trans; [| eapply _paco_mult_strong].
  apply _paco_mon; intros []; intros H; apply H.
Qed.

Theorem _paco18_fold: forall r,
  gf (upaco18 gf r) <18== paco18 gf r.
Proof.
  intros. apply uncurry_adjoint1_18.
  eapply le1_trans; [| apply _paco_fold]. apply le1_refl.
Qed.

Theorem _paco18_unfold: forall (MON: _monotone18 gf) r,
  paco18 gf r <18== gf (upaco18 gf r).
Proof.
  intros. apply curry_adjoint2_18.
  eapply _paco_unfold; apply monotone18_map; assumption.
Qed.

Theorem paco18_acc: forall
  l r (OBG: forall rr (INC: r <18= rr) (CIH: l <18= rr), l <18= paco18 gf rr),
  l <18= paco18 gf r.
Proof.
  apply _paco18_acc.
Qed.

Theorem paco18_mon: monotone18 (paco18 gf).
Proof.
  apply monotone18_eq.
  apply _paco18_mon.
Qed.

Theorem upaco18_mon: monotone18 (upaco18 gf).
Proof.
  repeat_intros 20. intros R  LE0.
  destruct R.
  - left. eapply paco18_mon. apply H. apply LE0.
  - right. apply LE0, H.
Qed.
Theorem paco18_mult_strong: forall r,
  paco18 gf (upaco18 gf r) <18= paco18 gf r.
Proof.
  apply _paco18_mult_strong.
Qed.

Corollary paco18_mult: forall r,
  paco18 gf (paco18 gf r) <18= paco18 gf r.
Proof. intros; eapply paco18_mult_strong, paco18_mon; [apply PR|..]; intros; left; assumption. Qed.

Theorem paco18_fold: forall r,
  gf (upaco18 gf r) <18= paco18 gf r.
Proof.
  apply _paco18_fold.
Qed.

Theorem paco18_unfold: forall (MON: monotone18 gf) r,
  paco18 gf r <18= gf (upaco18 gf r).
Proof.
  repeat_intros 1. eapply _paco18_unfold; apply monotone18_eq; assumption.
Qed.

End Arg18_1.

Arguments paco18_acc : clear implicits.
Arguments paco18_mon : clear implicits.
Arguments upaco18_mon : clear implicits.
Arguments paco18_mult_strong : clear implicits.
Arguments paco18_mult : clear implicits.
Arguments paco18_fold : clear implicits.
Arguments paco18_unfold : clear implicits.

Global Instance paco18_inst  (gf : rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17->_) r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : paco_class (paco18 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17) :=
{ pacoacc    := paco18_acc gf;
  pacomult   := paco18_mult gf;
  pacofold   := paco18_fold gf;
  pacounfold := paco18_unfold gf }.

(** 2 Mutual Coinduction *)

Section Arg18_2.

Definition monotone18_2 (gf: rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 -> rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 -> rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17) :=
  forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 r_0 r_1 r'_0 r'_1 (IN: gf r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17) (LE_0: r_0 <18= r'_0)(LE_1: r_1 <18= r'_1), gf r'_0 r'_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17.

Definition _monotone18_2 (gf: rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 -> rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 -> rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17) :=
  forall r_0 r_1 r'_0 r'_1(LE_0: r_0 <18= r'_0)(LE_1: r_1 <18= r'_1), gf r_0 r_1 <18== gf r'_0 r'_1.

Lemma monotone18_2_eq (gf: rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 -> rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 -> rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17) :
  monotone18_2 gf <-> _monotone18_2 gf.
Proof. unfold monotone18_2, _monotone18_2, le18. split; intros; eapply H; eassumption. Qed.

Lemma monotone18_2_map (gf: rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 -> rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 -> rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17)
      (MON: _monotone18_2 gf) :
  _monotone_2 (fun R0 R1 => uncurry18 (gf (curry18 R0) (curry18 R1))).
Proof.
  repeat_intros 6. apply uncurry_map18. apply MON; apply curry_map18; assumption.
Qed.

Variable gf_0 gf_1 : rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 -> rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 -> rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.

Theorem _paco18_2_0_mon: _monotone18_2 (paco18_2_0 gf_0 gf_1).
Proof.
  repeat_intros 6. eapply curry_map18, _paco_2_0_mon; apply uncurry_map18; assumption.
Qed.

Theorem _paco18_2_1_mon: _monotone18_2 (paco18_2_1 gf_0 gf_1).
Proof.
  repeat_intros 6. eapply curry_map18, _paco_2_1_mon; apply uncurry_map18; assumption.
Qed.

Theorem _paco18_2_0_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_0 <18== rr) (CIH: l <18== rr), l <18== paco18_2_0 gf_0 gf_1 rr r_1),
  l <18== paco18_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_18.
  eapply _paco_2_0_acc. intros.
  apply uncurry_adjoint1_18 in INC. apply uncurry_adjoint1_18 in CIH.
  apply uncurry_adjoint2_18.
  eapply le18_trans. eapply (OBG _ INC CIH).
  apply curry_map18.
  apply _paco_2_0_mon; try apply le1_refl; apply curry_bij1_18.
Qed.

Theorem _paco18_2_1_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_1 <18== rr) (CIH: l <18== rr), l <18== paco18_2_1 gf_0 gf_1 r_0 rr),
  l <18== paco18_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_18.
  eapply _paco_2_1_acc. intros.
  apply uncurry_adjoint1_18 in INC. apply uncurry_adjoint1_18 in CIH.
  apply uncurry_adjoint2_18.
  eapply le18_trans. eapply (OBG _ INC CIH).
  apply curry_map18.
  apply _paco_2_1_mon; try apply le1_refl; apply curry_bij1_18.
Qed.

Theorem _paco18_2_0_mult_strong: forall r_0 r_1,
  paco18_2_0 gf_0 gf_1 (upaco18_2_0 gf_0 gf_1 r_0 r_1) (upaco18_2_1 gf_0 gf_1 r_0 r_1) <18== paco18_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply curry_map18.
  eapply le1_trans; [| eapply _paco_2_0_mult_strong].
  apply _paco_2_0_mon; intros []; intros H; apply H.
Qed.

Theorem _paco18_2_1_mult_strong: forall r_0 r_1,
  paco18_2_1 gf_0 gf_1 (upaco18_2_0 gf_0 gf_1 r_0 r_1) (upaco18_2_1 gf_0 gf_1 r_0 r_1) <18== paco18_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply curry_map18.
  eapply le1_trans; [| eapply _paco_2_1_mult_strong].
  apply _paco_2_1_mon; intros []; intros H; apply H.
Qed.

Theorem _paco18_2_0_fold: forall r_0 r_1,
  gf_0 (upaco18_2_0 gf_0 gf_1 r_0 r_1) (upaco18_2_1 gf_0 gf_1 r_0 r_1) <18== paco18_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_18.
  eapply le1_trans; [| apply _paco_2_0_fold]. apply le1_refl.
Qed.

Theorem _paco18_2_1_fold: forall r_0 r_1,
  gf_1 (upaco18_2_0 gf_0 gf_1 r_0 r_1) (upaco18_2_1 gf_0 gf_1 r_0 r_1) <18== paco18_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_18.
  eapply le1_trans; [| apply _paco_2_1_fold]. apply le1_refl.
Qed.

Theorem _paco18_2_0_unfold: forall (MON: _monotone18_2 gf_0) (MON: _monotone18_2 gf_1) r_0 r_1,
  paco18_2_0 gf_0 gf_1 r_0 r_1 <18== gf_0 (upaco18_2_0 gf_0 gf_1 r_0 r_1) (upaco18_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  intros. apply curry_adjoint2_18.
  eapply _paco_2_0_unfold; apply monotone18_2_map; assumption.
Qed.

Theorem _paco18_2_1_unfold: forall (MON: _monotone18_2 gf_0) (MON: _monotone18_2 gf_1) r_0 r_1,
  paco18_2_1 gf_0 gf_1 r_0 r_1 <18== gf_1 (upaco18_2_0 gf_0 gf_1 r_0 r_1) (upaco18_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  intros. apply curry_adjoint2_18.
  eapply _paco_2_1_unfold; apply monotone18_2_map; assumption.
Qed.

Theorem paco18_2_0_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_0 <18= rr) (CIH: l <18= rr), l <18= paco18_2_0 gf_0 gf_1 rr r_1),
  l <18= paco18_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco18_2_0_acc.
Qed.

Theorem paco18_2_1_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_1 <18= rr) (CIH: l <18= rr), l <18= paco18_2_1 gf_0 gf_1 r_0 rr),
  l <18= paco18_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco18_2_1_acc.
Qed.

Theorem paco18_2_0_mon: monotone18_2 (paco18_2_0 gf_0 gf_1).
Proof.
  apply monotone18_2_eq.
  apply _paco18_2_0_mon.
Qed.

Theorem paco18_2_1_mon: monotone18_2 (paco18_2_1 gf_0 gf_1).
Proof.
  apply monotone18_2_eq.
  apply _paco18_2_1_mon.
Qed.

Theorem upaco18_2_0_mon: monotone18_2 (upaco18_2_0 gf_0 gf_1).
Proof.
  repeat_intros 22. intros R  LE0 LE1.
  destruct R.
  - left. eapply paco18_2_0_mon. apply H. apply LE0. apply LE1.
  - right. apply LE0, H.
Qed.
Theorem upaco18_2_1_mon: monotone18_2 (upaco18_2_1 gf_0 gf_1).
Proof.
  repeat_intros 22. intros R  LE0 LE1.
  destruct R.
  - left. eapply paco18_2_1_mon. apply H. apply LE0. apply LE1.
  - right. apply LE1, H.
Qed.
Theorem paco18_2_0_mult_strong: forall r_0 r_1,
  paco18_2_0 gf_0 gf_1 (upaco18_2_0 gf_0 gf_1 r_0 r_1) (upaco18_2_1 gf_0 gf_1 r_0 r_1) <18= paco18_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco18_2_0_mult_strong.
Qed.

Theorem paco18_2_1_mult_strong: forall r_0 r_1,
  paco18_2_1 gf_0 gf_1 (upaco18_2_0 gf_0 gf_1 r_0 r_1) (upaco18_2_1 gf_0 gf_1 r_0 r_1) <18= paco18_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco18_2_1_mult_strong.
Qed.

Corollary paco18_2_0_mult: forall r_0 r_1,
  paco18_2_0 gf_0 gf_1 (paco18_2_0 gf_0 gf_1 r_0 r_1) (paco18_2_1 gf_0 gf_1 r_0 r_1) <18= paco18_2_0 gf_0 gf_1 r_0 r_1.
Proof. intros; eapply paco18_2_0_mult_strong, paco18_2_0_mon; [apply PR|..]; intros; left; assumption. Qed.

Corollary paco18_2_1_mult: forall r_0 r_1,
  paco18_2_1 gf_0 gf_1 (paco18_2_0 gf_0 gf_1 r_0 r_1) (paco18_2_1 gf_0 gf_1 r_0 r_1) <18= paco18_2_1 gf_0 gf_1 r_0 r_1.
Proof. intros; eapply paco18_2_1_mult_strong, paco18_2_1_mon; [apply PR|..]; intros; left; assumption. Qed.

Theorem paco18_2_0_fold: forall r_0 r_1,
  gf_0 (upaco18_2_0 gf_0 gf_1 r_0 r_1) (upaco18_2_1 gf_0 gf_1 r_0 r_1) <18= paco18_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco18_2_0_fold.
Qed.

Theorem paco18_2_1_fold: forall r_0 r_1,
  gf_1 (upaco18_2_0 gf_0 gf_1 r_0 r_1) (upaco18_2_1 gf_0 gf_1 r_0 r_1) <18= paco18_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco18_2_1_fold.
Qed.

Theorem paco18_2_0_unfold: forall (MON: monotone18_2 gf_0) (MON: monotone18_2 gf_1) r_0 r_1,
  paco18_2_0 gf_0 gf_1 r_0 r_1 <18= gf_0 (upaco18_2_0 gf_0 gf_1 r_0 r_1) (upaco18_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  repeat_intros 2. eapply _paco18_2_0_unfold; apply monotone18_2_eq; assumption.
Qed.

Theorem paco18_2_1_unfold: forall (MON: monotone18_2 gf_0) (MON: monotone18_2 gf_1) r_0 r_1,
  paco18_2_1 gf_0 gf_1 r_0 r_1 <18= gf_1 (upaco18_2_0 gf_0 gf_1 r_0 r_1) (upaco18_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  repeat_intros 2. eapply _paco18_2_1_unfold; apply monotone18_2_eq; assumption.
Qed.

End Arg18_2.

Arguments paco18_2_0_acc : clear implicits.
Arguments paco18_2_1_acc : clear implicits.
Arguments paco18_2_0_mon : clear implicits.
Arguments paco18_2_1_mon : clear implicits.
Arguments upaco18_2_0_mon : clear implicits.
Arguments upaco18_2_1_mon : clear implicits.
Arguments paco18_2_0_mult_strong : clear implicits.
Arguments paco18_2_1_mult_strong : clear implicits.
Arguments paco18_2_0_mult : clear implicits.
Arguments paco18_2_1_mult : clear implicits.
Arguments paco18_2_0_fold : clear implicits.
Arguments paco18_2_1_fold : clear implicits.
Arguments paco18_2_0_unfold : clear implicits.
Arguments paco18_2_1_unfold : clear implicits.

Global Instance paco18_2_0_inst  (gf_0 gf_1 : rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17->_) r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : paco_class (paco18_2_0 gf_0 gf_1 r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17) :=
{ pacoacc    := paco18_2_0_acc gf_0 gf_1;
  pacomult   := paco18_2_0_mult gf_0 gf_1;
  pacofold   := paco18_2_0_fold gf_0 gf_1;
  pacounfold := paco18_2_0_unfold gf_0 gf_1 }.

Global Instance paco18_2_1_inst  (gf_0 gf_1 : rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17->_) r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : paco_class (paco18_2_1 gf_0 gf_1 r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17) :=
{ pacoacc    := paco18_2_1_acc gf_0 gf_1;
  pacomult   := paco18_2_1_mult gf_0 gf_1;
  pacofold   := paco18_2_1_fold gf_0 gf_1;
  pacounfold := paco18_2_1_unfold gf_0 gf_1 }.

(** 3 Mutual Coinduction *)

Section Arg18_3.

Definition monotone18_3 (gf: rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 -> rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 -> rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 -> rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17) :=
  forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 r_0 r_1 r_2 r'_0 r'_1 r'_2 (IN: gf r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17) (LE_0: r_0 <18= r'_0)(LE_1: r_1 <18= r'_1)(LE_2: r_2 <18= r'_2), gf r'_0 r'_1 r'_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17.

Definition _monotone18_3 (gf: rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 -> rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 -> rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 -> rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17) :=
  forall r_0 r_1 r_2 r'_0 r'_1 r'_2(LE_0: r_0 <18= r'_0)(LE_1: r_1 <18= r'_1)(LE_2: r_2 <18= r'_2), gf r_0 r_1 r_2 <18== gf r'_0 r'_1 r'_2.

Lemma monotone18_3_eq (gf: rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 -> rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 -> rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 -> rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17) :
  monotone18_3 gf <-> _monotone18_3 gf.
Proof. unfold monotone18_3, _monotone18_3, le18. split; intros; eapply H; eassumption. Qed.

Lemma monotone18_3_map (gf: rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 -> rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 -> rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 -> rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17)
      (MON: _monotone18_3 gf) :
  _monotone_3 (fun R0 R1 R2 => uncurry18 (gf (curry18 R0) (curry18 R1) (curry18 R2))).
Proof.
  repeat_intros 9. apply uncurry_map18. apply MON; apply curry_map18; assumption.
Qed.

Variable gf_0 gf_1 gf_2 : rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 -> rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 -> rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 -> rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.
Arguments gf_2 : clear implicits.

Theorem _paco18_3_0_mon: _monotone18_3 (paco18_3_0 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 9. eapply curry_map18, _paco_3_0_mon; apply uncurry_map18; assumption.
Qed.

Theorem _paco18_3_1_mon: _monotone18_3 (paco18_3_1 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 9. eapply curry_map18, _paco_3_1_mon; apply uncurry_map18; assumption.
Qed.

Theorem _paco18_3_2_mon: _monotone18_3 (paco18_3_2 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 9. eapply curry_map18, _paco_3_2_mon; apply uncurry_map18; assumption.
Qed.

Theorem _paco18_3_0_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_0 <18== rr) (CIH: l <18== rr), l <18== paco18_3_0 gf_0 gf_1 gf_2 rr r_1 r_2),
  l <18== paco18_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_18.
  eapply _paco_3_0_acc. intros.
  apply uncurry_adjoint1_18 in INC. apply uncurry_adjoint1_18 in CIH.
  apply uncurry_adjoint2_18.
  eapply le18_trans. eapply (OBG _ INC CIH).
  apply curry_map18.
  apply _paco_3_0_mon; try apply le1_refl; apply curry_bij1_18.
Qed.

Theorem _paco18_3_1_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_1 <18== rr) (CIH: l <18== rr), l <18== paco18_3_1 gf_0 gf_1 gf_2 r_0 rr r_2),
  l <18== paco18_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_18.
  eapply _paco_3_1_acc. intros.
  apply uncurry_adjoint1_18 in INC. apply uncurry_adjoint1_18 in CIH.
  apply uncurry_adjoint2_18.
  eapply le18_trans. eapply (OBG _ INC CIH).
  apply curry_map18.
  apply _paco_3_1_mon; try apply le1_refl; apply curry_bij1_18.
Qed.

Theorem _paco18_3_2_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_2 <18== rr) (CIH: l <18== rr), l <18== paco18_3_2 gf_0 gf_1 gf_2 r_0 r_1 rr),
  l <18== paco18_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_18.
  eapply _paco_3_2_acc. intros.
  apply uncurry_adjoint1_18 in INC. apply uncurry_adjoint1_18 in CIH.
  apply uncurry_adjoint2_18.
  eapply le18_trans. eapply (OBG _ INC CIH).
  apply curry_map18.
  apply _paco_3_2_mon; try apply le1_refl; apply curry_bij1_18.
Qed.

Theorem _paco18_3_0_mult_strong: forall r_0 r_1 r_2,
  paco18_3_0 gf_0 gf_1 gf_2 (upaco18_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco18_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco18_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <18== paco18_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply curry_map18.
  eapply le1_trans; [| eapply _paco_3_0_mult_strong].
  apply _paco_3_0_mon; intros []; intros H; apply H.
Qed.

Theorem _paco18_3_1_mult_strong: forall r_0 r_1 r_2,
  paco18_3_1 gf_0 gf_1 gf_2 (upaco18_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco18_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco18_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <18== paco18_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply curry_map18.
  eapply le1_trans; [| eapply _paco_3_1_mult_strong].
  apply _paco_3_1_mon; intros []; intros H; apply H.
Qed.

Theorem _paco18_3_2_mult_strong: forall r_0 r_1 r_2,
  paco18_3_2 gf_0 gf_1 gf_2 (upaco18_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco18_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco18_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <18== paco18_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply curry_map18.
  eapply le1_trans; [| eapply _paco_3_2_mult_strong].
  apply _paco_3_2_mon; intros []; intros H; apply H.
Qed.

Theorem _paco18_3_0_fold: forall r_0 r_1 r_2,
  gf_0 (upaco18_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco18_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco18_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <18== paco18_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_18.
  eapply le1_trans; [| apply _paco_3_0_fold]. apply le1_refl.
Qed.

Theorem _paco18_3_1_fold: forall r_0 r_1 r_2,
  gf_1 (upaco18_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco18_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco18_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <18== paco18_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_18.
  eapply le1_trans; [| apply _paco_3_1_fold]. apply le1_refl.
Qed.

Theorem _paco18_3_2_fold: forall r_0 r_1 r_2,
  gf_2 (upaco18_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco18_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco18_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <18== paco18_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_18.
  eapply le1_trans; [| apply _paco_3_2_fold]. apply le1_refl.
Qed.

Theorem _paco18_3_0_unfold: forall (MON: _monotone18_3 gf_0) (MON: _monotone18_3 gf_1) (MON: _monotone18_3 gf_2) r_0 r_1 r_2,
  paco18_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 <18== gf_0 (upaco18_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco18_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco18_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  intros. apply curry_adjoint2_18.
  eapply _paco_3_0_unfold; apply monotone18_3_map; assumption.
Qed.

Theorem _paco18_3_1_unfold: forall (MON: _monotone18_3 gf_0) (MON: _monotone18_3 gf_1) (MON: _monotone18_3 gf_2) r_0 r_1 r_2,
  paco18_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 <18== gf_1 (upaco18_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco18_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco18_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  intros. apply curry_adjoint2_18.
  eapply _paco_3_1_unfold; apply monotone18_3_map; assumption.
Qed.

Theorem _paco18_3_2_unfold: forall (MON: _monotone18_3 gf_0) (MON: _monotone18_3 gf_1) (MON: _monotone18_3 gf_2) r_0 r_1 r_2,
  paco18_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 <18== gf_2 (upaco18_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco18_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco18_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  intros. apply curry_adjoint2_18.
  eapply _paco_3_2_unfold; apply monotone18_3_map; assumption.
Qed.

Theorem paco18_3_0_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_0 <18= rr) (CIH: l <18= rr), l <18= paco18_3_0 gf_0 gf_1 gf_2 rr r_1 r_2),
  l <18= paco18_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco18_3_0_acc.
Qed.

Theorem paco18_3_1_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_1 <18= rr) (CIH: l <18= rr), l <18= paco18_3_1 gf_0 gf_1 gf_2 r_0 rr r_2),
  l <18= paco18_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco18_3_1_acc.
Qed.

Theorem paco18_3_2_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_2 <18= rr) (CIH: l <18= rr), l <18= paco18_3_2 gf_0 gf_1 gf_2 r_0 r_1 rr),
  l <18= paco18_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco18_3_2_acc.
Qed.

Theorem paco18_3_0_mon: monotone18_3 (paco18_3_0 gf_0 gf_1 gf_2).
Proof.
  apply monotone18_3_eq.
  apply _paco18_3_0_mon.
Qed.

Theorem paco18_3_1_mon: monotone18_3 (paco18_3_1 gf_0 gf_1 gf_2).
Proof.
  apply monotone18_3_eq.
  apply _paco18_3_1_mon.
Qed.

Theorem paco18_3_2_mon: monotone18_3 (paco18_3_2 gf_0 gf_1 gf_2).
Proof.
  apply monotone18_3_eq.
  apply _paco18_3_2_mon.
Qed.

Theorem upaco18_3_0_mon: monotone18_3 (upaco18_3_0 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 24. intros R  LE0 LE1 LE2.
  destruct R.
  - left. eapply paco18_3_0_mon. apply H. apply LE0. apply LE1. apply LE2.
  - right. apply LE0, H.
Qed.
Theorem upaco18_3_1_mon: monotone18_3 (upaco18_3_1 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 24. intros R  LE0 LE1 LE2.
  destruct R.
  - left. eapply paco18_3_1_mon. apply H. apply LE0. apply LE1. apply LE2.
  - right. apply LE1, H.
Qed.
Theorem upaco18_3_2_mon: monotone18_3 (upaco18_3_2 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 24. intros R  LE0 LE1 LE2.
  destruct R.
  - left. eapply paco18_3_2_mon. apply H. apply LE0. apply LE1. apply LE2.
  - right. apply LE2, H.
Qed.
Theorem paco18_3_0_mult_strong: forall r_0 r_1 r_2,
  paco18_3_0 gf_0 gf_1 gf_2 (upaco18_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco18_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco18_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <18= paco18_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco18_3_0_mult_strong.
Qed.

Theorem paco18_3_1_mult_strong: forall r_0 r_1 r_2,
  paco18_3_1 gf_0 gf_1 gf_2 (upaco18_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco18_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco18_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <18= paco18_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco18_3_1_mult_strong.
Qed.

Theorem paco18_3_2_mult_strong: forall r_0 r_1 r_2,
  paco18_3_2 gf_0 gf_1 gf_2 (upaco18_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco18_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco18_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <18= paco18_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco18_3_2_mult_strong.
Qed.

Corollary paco18_3_0_mult: forall r_0 r_1 r_2,
  paco18_3_0 gf_0 gf_1 gf_2 (paco18_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco18_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco18_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <18= paco18_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco18_3_0_mult_strong, paco18_3_0_mon; [apply PR|..]; intros; left; assumption. Qed.

Corollary paco18_3_1_mult: forall r_0 r_1 r_2,
  paco18_3_1 gf_0 gf_1 gf_2 (paco18_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco18_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco18_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <18= paco18_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco18_3_1_mult_strong, paco18_3_1_mon; [apply PR|..]; intros; left; assumption. Qed.

Corollary paco18_3_2_mult: forall r_0 r_1 r_2,
  paco18_3_2 gf_0 gf_1 gf_2 (paco18_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco18_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco18_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <18= paco18_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco18_3_2_mult_strong, paco18_3_2_mon; [apply PR|..]; intros; left; assumption. Qed.

Theorem paco18_3_0_fold: forall r_0 r_1 r_2,
  gf_0 (upaco18_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco18_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco18_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <18= paco18_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco18_3_0_fold.
Qed.

Theorem paco18_3_1_fold: forall r_0 r_1 r_2,
  gf_1 (upaco18_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco18_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco18_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <18= paco18_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco18_3_1_fold.
Qed.

Theorem paco18_3_2_fold: forall r_0 r_1 r_2,
  gf_2 (upaco18_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco18_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco18_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <18= paco18_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco18_3_2_fold.
Qed.

Theorem paco18_3_0_unfold: forall (MON: monotone18_3 gf_0) (MON: monotone18_3 gf_1) (MON: monotone18_3 gf_2) r_0 r_1 r_2,
  paco18_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 <18= gf_0 (upaco18_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco18_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco18_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  repeat_intros 3. eapply _paco18_3_0_unfold; apply monotone18_3_eq; assumption.
Qed.

Theorem paco18_3_1_unfold: forall (MON: monotone18_3 gf_0) (MON: monotone18_3 gf_1) (MON: monotone18_3 gf_2) r_0 r_1 r_2,
  paco18_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 <18= gf_1 (upaco18_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco18_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco18_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  repeat_intros 3. eapply _paco18_3_1_unfold; apply monotone18_3_eq; assumption.
Qed.

Theorem paco18_3_2_unfold: forall (MON: monotone18_3 gf_0) (MON: monotone18_3 gf_1) (MON: monotone18_3 gf_2) r_0 r_1 r_2,
  paco18_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 <18= gf_2 (upaco18_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco18_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco18_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  repeat_intros 3. eapply _paco18_3_2_unfold; apply monotone18_3_eq; assumption.
Qed.

End Arg18_3.

Arguments paco18_3_0_acc : clear implicits.
Arguments paco18_3_1_acc : clear implicits.
Arguments paco18_3_2_acc : clear implicits.
Arguments paco18_3_0_mon : clear implicits.
Arguments paco18_3_1_mon : clear implicits.
Arguments paco18_3_2_mon : clear implicits.
Arguments upaco18_3_0_mon : clear implicits.
Arguments upaco18_3_1_mon : clear implicits.
Arguments upaco18_3_2_mon : clear implicits.
Arguments paco18_3_0_mult_strong : clear implicits.
Arguments paco18_3_1_mult_strong : clear implicits.
Arguments paco18_3_2_mult_strong : clear implicits.
Arguments paco18_3_0_mult : clear implicits.
Arguments paco18_3_1_mult : clear implicits.
Arguments paco18_3_2_mult : clear implicits.
Arguments paco18_3_0_fold : clear implicits.
Arguments paco18_3_1_fold : clear implicits.
Arguments paco18_3_2_fold : clear implicits.
Arguments paco18_3_0_unfold : clear implicits.
Arguments paco18_3_1_unfold : clear implicits.
Arguments paco18_3_2_unfold : clear implicits.

Global Instance paco18_3_0_inst  (gf_0 gf_1 gf_2 : rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : paco_class (paco18_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17) :=
{ pacoacc    := paco18_3_0_acc gf_0 gf_1 gf_2;
  pacomult   := paco18_3_0_mult gf_0 gf_1 gf_2;
  pacofold   := paco18_3_0_fold gf_0 gf_1 gf_2;
  pacounfold := paco18_3_0_unfold gf_0 gf_1 gf_2 }.

Global Instance paco18_3_1_inst  (gf_0 gf_1 gf_2 : rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : paco_class (paco18_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17) :=
{ pacoacc    := paco18_3_1_acc gf_0 gf_1 gf_2;
  pacomult   := paco18_3_1_mult gf_0 gf_1 gf_2;
  pacofold   := paco18_3_1_fold gf_0 gf_1 gf_2;
  pacounfold := paco18_3_1_unfold gf_0 gf_1 gf_2 }.

Global Instance paco18_3_2_inst  (gf_0 gf_1 gf_2 : rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : paco_class (paco18_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17) :=
{ pacoacc    := paco18_3_2_acc gf_0 gf_1 gf_2;
  pacomult   := paco18_3_2_mult gf_0 gf_1 gf_2;
  pacofold   := paco18_3_2_fold gf_0 gf_1 gf_2;
  pacounfold := paco18_3_2_unfold gf_0 gf_1 gf_2 }.

End PACO18.

Global Opaque paco18.

Hint Unfold upaco18.
Hint Resolve paco18_fold.
Hint Unfold monotone18.

Global Opaque paco18_2_0.
Global Opaque paco18_2_1.

Hint Unfold upaco18_2_0.
Hint Unfold upaco18_2_1.
Hint Resolve paco18_2_0_fold.
Hint Resolve paco18_2_1_fold.
Hint Unfold monotone18_2.

Global Opaque paco18_3_0.
Global Opaque paco18_3_1.
Global Opaque paco18_3_2.

Hint Unfold upaco18_3_0.
Hint Unfold upaco18_3_1.
Hint Unfold upaco18_3_2.
Hint Resolve paco18_3_0_fold.
Hint Resolve paco18_3_1_fold.
Hint Resolve paco18_3_2_fold.
Hint Unfold monotone18_3.

