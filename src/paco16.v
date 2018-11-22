Require Export paconotation pacotacuser.
Require Import paconotation_internal pacotac pacon.
Set Implicit Arguments.

Section PACO16.

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

Record sig16T :=
  exist16T { 
      proj16T0: @T0;
      proj16T1: @T1 proj16T0;
      proj16T2: @T2 proj16T0 proj16T1;
      proj16T3: @T3 proj16T0 proj16T1 proj16T2;
      proj16T4: @T4 proj16T0 proj16T1 proj16T2 proj16T3;
      proj16T5: @T5 proj16T0 proj16T1 proj16T2 proj16T3 proj16T4;
      proj16T6: @T6 proj16T0 proj16T1 proj16T2 proj16T3 proj16T4 proj16T5;
      proj16T7: @T7 proj16T0 proj16T1 proj16T2 proj16T3 proj16T4 proj16T5 proj16T6;
      proj16T8: @T8 proj16T0 proj16T1 proj16T2 proj16T3 proj16T4 proj16T5 proj16T6 proj16T7;
      proj16T9: @T9 proj16T0 proj16T1 proj16T2 proj16T3 proj16T4 proj16T5 proj16T6 proj16T7 proj16T8;
      proj16T10: @T10 proj16T0 proj16T1 proj16T2 proj16T3 proj16T4 proj16T5 proj16T6 proj16T7 proj16T8 proj16T9;
      proj16T11: @T11 proj16T0 proj16T1 proj16T2 proj16T3 proj16T4 proj16T5 proj16T6 proj16T7 proj16T8 proj16T9 proj16T10;
      proj16T12: @T12 proj16T0 proj16T1 proj16T2 proj16T3 proj16T4 proj16T5 proj16T6 proj16T7 proj16T8 proj16T9 proj16T10 proj16T11;
      proj16T13: @T13 proj16T0 proj16T1 proj16T2 proj16T3 proj16T4 proj16T5 proj16T6 proj16T7 proj16T8 proj16T9 proj16T10 proj16T11 proj16T12;
      proj16T14: @T14 proj16T0 proj16T1 proj16T2 proj16T3 proj16T4 proj16T5 proj16T6 proj16T7 proj16T8 proj16T9 proj16T10 proj16T11 proj16T12 proj16T13;
      proj16T15: @T15 proj16T0 proj16T1 proj16T2 proj16T3 proj16T4 proj16T5 proj16T6 proj16T7 proj16T8 proj16T9 proj16T10 proj16T11 proj16T12 proj16T13 proj16T14;
    }.

Definition uncurry16 (R: rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15): rel1 sig16T := fun x => R (proj16T0 x) (proj16T1 x) (proj16T2 x) (proj16T3 x) (proj16T4 x) (proj16T5 x) (proj16T6 x) (proj16T7 x) (proj16T8 x) (proj16T9 x) (proj16T10 x) (proj16T11 x) (proj16T12 x) (proj16T13 x) (proj16T14 x) (proj16T15 x).

Definition curry16 (R: rel1 sig16T): rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 :=
  fun x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 => R (exist16T x15).

Lemma uncurry_map16 r0 r1 (LE : r0 <16== r1) : uncurry16 r0 <1== uncurry16 r1.
Proof. intros [] H. apply LE. apply H. Qed.

Lemma uncurry_map_rev16 r0 r1 (LE: uncurry16 r0 <1== uncurry16 r1) : r0 <16== r1.
Proof.
  repeat_intros 16. intros H. apply (LE (exist16T x15) H).
Qed.

Lemma curry_map16 r0 r1 (LE: r0 <1== r1) : curry16 r0 <16== curry16 r1.
Proof. 
  repeat_intros 16. intros H. apply (LE (exist16T x15) H).
Qed.

Lemma curry_map_rev16 r0 r1 (LE: curry16 r0 <16== curry16 r1) : r0 <1== r1.
Proof. 
  intros [] H. apply LE. apply H.
Qed.

Lemma uncurry_bij1_16 r : curry16 (uncurry16 r) <16== r.
Proof. unfold le16. repeat_intros 16. intros H. apply H. Qed.

Lemma uncurry_bij2_16 r : r <16== curry16 (uncurry16 r).
Proof. unfold le16. repeat_intros 16. intros H. apply H. Qed.

Lemma curry_bij1_16 r : uncurry16 (curry16 r) <1== r.
Proof. intros []. intro H. apply H. Qed.

Lemma curry_bij2_16 r : r <1== uncurry16 (curry16 r).
Proof. intros []. intro H. apply H. Qed.

Lemma uncurry_adjoint1_16 r0 r1 (LE: uncurry16 r0 <1== r1) : r0 <16== curry16 r1.
Proof.
  apply uncurry_map_rev16. eapply le1_trans; [apply LE|]. apply curry_bij2_16.
Qed.

Lemma uncurry_adjoint2_16 r0 r1 (LE: r0 <16== curry16 r1) : uncurry16 r0 <1== r1.
Proof.
  apply curry_map_rev16. eapply le16_trans; [|apply LE]. apply uncurry_bij2_16.
Qed.

Lemma curry_adjoint1_16 r0 r1 (LE: curry16 r0 <16== r1) : r0 <1== uncurry16 r1.
Proof.
  apply curry_map_rev16. eapply le16_trans; [apply LE|]. apply uncurry_bij2_16.
Qed.

Lemma curry_adjoint2_16 r0 r1 (LE: r0 <1== uncurry16 r1) : curry16 r0 <16== r1.
Proof.
  apply uncurry_map_rev16. eapply le1_trans; [|apply LE]. apply curry_bij1_16.
Qed.

(** ** Predicates of Arity 16
*)

Section Arg16_def.
Variable gf : rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 -> rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15.
Arguments gf : clear implicits.

Definition paco16( r: rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15) : rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 :=
  curry16 (paco (fun R0 => uncurry16 (gf (curry16 R0))) (uncurry16 r)).

Definition upaco16( r: rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15) := paco16 r \16/ r.
End Arg16_def.
Arguments paco16 : clear implicits.
Arguments upaco16 : clear implicits.
Hint Unfold upaco16.

Section Arg16_2_def.
Variable gf_0 gf_1 : rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 -> rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 -> rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.

Definition paco16_2_0( r_0 r_1: rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15) : rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 :=
  curry16 (paco_2_0 (fun R0 R1 => uncurry16 (gf_0 (curry16 R0) (curry16 R1))) (fun R0 R1 => uncurry16 (gf_1 (curry16 R0) (curry16 R1))) (uncurry16 r_0) (uncurry16 r_1)).

Definition paco16_2_1( r_0 r_1: rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15) : rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 :=
  curry16 (paco_2_1 (fun R0 R1 => uncurry16 (gf_0 (curry16 R0) (curry16 R1))) (fun R0 R1 => uncurry16 (gf_1 (curry16 R0) (curry16 R1))) (uncurry16 r_0) (uncurry16 r_1)).

Definition upaco16_2_0( r_0 r_1: rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15) := paco16_2_0 r_0 r_1 \16/ r_0.
Definition upaco16_2_1( r_0 r_1: rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15) := paco16_2_1 r_0 r_1 \16/ r_1.
End Arg16_2_def.
Arguments paco16_2_0 : clear implicits.
Arguments upaco16_2_0 : clear implicits.
Hint Unfold upaco16_2_0.
Arguments paco16_2_1 : clear implicits.
Arguments upaco16_2_1 : clear implicits.
Hint Unfold upaco16_2_1.

Section Arg16_3_def.
Variable gf_0 gf_1 gf_2 : rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 -> rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 -> rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 -> rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.
Arguments gf_2 : clear implicits.

Definition paco16_3_0( r_0 r_1 r_2: rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15) : rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 :=
  curry16 (paco_3_0 (fun R0 R1 R2 => uncurry16 (gf_0 (curry16 R0) (curry16 R1) (curry16 R2))) (fun R0 R1 R2 => uncurry16 (gf_1 (curry16 R0) (curry16 R1) (curry16 R2))) (fun R0 R1 R2 => uncurry16 (gf_2 (curry16 R0) (curry16 R1) (curry16 R2))) (uncurry16 r_0) (uncurry16 r_1) (uncurry16 r_2)).

Definition paco16_3_1( r_0 r_1 r_2: rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15) : rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 :=
  curry16 (paco_3_1 (fun R0 R1 R2 => uncurry16 (gf_0 (curry16 R0) (curry16 R1) (curry16 R2))) (fun R0 R1 R2 => uncurry16 (gf_1 (curry16 R0) (curry16 R1) (curry16 R2))) (fun R0 R1 R2 => uncurry16 (gf_2 (curry16 R0) (curry16 R1) (curry16 R2))) (uncurry16 r_0) (uncurry16 r_1) (uncurry16 r_2)).

Definition paco16_3_2( r_0 r_1 r_2: rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15) : rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 :=
  curry16 (paco_3_2 (fun R0 R1 R2 => uncurry16 (gf_0 (curry16 R0) (curry16 R1) (curry16 R2))) (fun R0 R1 R2 => uncurry16 (gf_1 (curry16 R0) (curry16 R1) (curry16 R2))) (fun R0 R1 R2 => uncurry16 (gf_2 (curry16 R0) (curry16 R1) (curry16 R2))) (uncurry16 r_0) (uncurry16 r_1) (uncurry16 r_2)).

Definition upaco16_3_0( r_0 r_1 r_2: rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15) := paco16_3_0 r_0 r_1 r_2 \16/ r_0.
Definition upaco16_3_1( r_0 r_1 r_2: rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15) := paco16_3_1 r_0 r_1 r_2 \16/ r_1.
Definition upaco16_3_2( r_0 r_1 r_2: rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15) := paco16_3_2 r_0 r_1 r_2 \16/ r_2.
End Arg16_3_def.
Arguments paco16_3_0 : clear implicits.
Arguments upaco16_3_0 : clear implicits.
Hint Unfold upaco16_3_0.
Arguments paco16_3_1 : clear implicits.
Arguments upaco16_3_1 : clear implicits.
Hint Unfold upaco16_3_1.
Arguments paco16_3_2 : clear implicits.
Arguments upaco16_3_2 : clear implicits.
Hint Unfold upaco16_3_2.

(** 1 Mutual Coinduction *)

Section Arg16_1.

Definition monotone16 (gf: rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 -> rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15) :=
  forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 r r' (IN: gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15) (LE: r <16= r'), gf r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15.

Definition _monotone16 (gf: rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 -> rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15) :=
  forall r r'(LE: r <16= r'), gf r <16== gf r'.

Lemma monotone16_eq (gf: rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 -> rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15) :
  monotone16 gf <-> _monotone16 gf.
Proof. unfold monotone16, _monotone16, le16. split; intros; eapply H; eassumption. Qed.

Lemma monotone16_map (gf: rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 -> rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15)
      (MON: _monotone16 gf) :
  _monotone (fun R0 => uncurry16 (gf (curry16 R0))).
Proof.
  repeat_intros 3. apply uncurry_map16. apply MON; apply curry_map16; assumption.
Qed.

Variable gf : rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 -> rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15.
Arguments gf : clear implicits.

Theorem _paco16_mon: _monotone16 (paco16 gf).
Proof.
  repeat_intros 3. eapply curry_map16, _paco_mon; apply uncurry_map16; assumption.
Qed.

Theorem _paco16_acc: forall
  l r (OBG: forall rr (INC: r <16== rr) (CIH: l <16== rr), l <16== paco16 gf rr),
  l <16== paco16 gf r.
Proof.
  intros. apply uncurry_adjoint1_16.
  eapply _paco_acc. intros.
  apply uncurry_adjoint1_16 in INC. apply uncurry_adjoint1_16 in CIH.
  apply uncurry_adjoint2_16.
  eapply le16_trans. eapply (OBG _ INC CIH).
  apply curry_map16.
  apply _paco_mon; try apply le1_refl; apply curry_bij1_16.
Qed.

Theorem _paco16_mult_strong: forall r,
  paco16 gf (upaco16 gf r) <16== paco16 gf r.
Proof.
  intros. apply curry_map16.
  eapply le1_trans; [| eapply _paco_mult_strong].
  apply _paco_mon; intros []; intros H; apply H.
Qed.

Theorem _paco16_fold: forall r,
  gf (upaco16 gf r) <16== paco16 gf r.
Proof.
  intros. apply uncurry_adjoint1_16.
  eapply le1_trans; [| apply _paco_fold]. apply le1_refl.
Qed.

Theorem _paco16_unfold: forall (MON: _monotone16 gf) r,
  paco16 gf r <16== gf (upaco16 gf r).
Proof.
  intros. apply curry_adjoint2_16.
  eapply _paco_unfold; apply monotone16_map; assumption.
Qed.

Theorem paco16_acc: forall
  l r (OBG: forall rr (INC: r <16= rr) (CIH: l <16= rr), l <16= paco16 gf rr),
  l <16= paco16 gf r.
Proof.
  apply _paco16_acc.
Qed.

Theorem paco16_mon: monotone16 (paco16 gf).
Proof.
  apply monotone16_eq.
  apply _paco16_mon.
Qed.

Theorem paco16_mult_strong: forall r,
  paco16 gf (upaco16 gf r) <16= paco16 gf r.
Proof.
  apply _paco16_mult_strong.
Qed.

Corollary paco16_mult: forall r,
  paco16 gf (paco16 gf r) <16= paco16 gf r.
Proof. intros; eapply paco16_mult_strong, paco16_mon; [apply PR|..]; intros; left; assumption. Qed.

Theorem paco16_fold: forall r,
  gf (upaco16 gf r) <16= paco16 gf r.
Proof.
  apply _paco16_fold.
Qed.

Theorem paco16_unfold: forall (MON: monotone16 gf) r,
  paco16 gf r <16= gf (upaco16 gf r).
Proof.
  repeat_intros 1. eapply _paco16_unfold; apply monotone16_eq; assumption.
Qed.

End Arg16_1.

Arguments paco16_acc : clear implicits.
Arguments paco16_mon : clear implicits.
Arguments paco16_mult_strong : clear implicits.
Arguments paco16_mult : clear implicits.
Arguments paco16_fold : clear implicits.
Arguments paco16_unfold : clear implicits.

Global Instance paco16_inst  (gf : rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15->_) r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : paco_class (paco16 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15) :=
{ pacoacc    := paco16_acc gf;
  pacomult   := paco16_mult gf;
  pacofold   := paco16_fold gf;
  pacounfold := paco16_unfold gf }.

(** 2 Mutual Coinduction *)

Section Arg16_2.

Definition monotone16_2 (gf: rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 -> rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 -> rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15) :=
  forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 r_0 r_1 r'_0 r'_1 (IN: gf r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15) (LE_0: r_0 <16= r'_0)(LE_1: r_1 <16= r'_1), gf r'_0 r'_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15.

Definition _monotone16_2 (gf: rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 -> rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 -> rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15) :=
  forall r_0 r_1 r'_0 r'_1(LE_0: r_0 <16= r'_0)(LE_1: r_1 <16= r'_1), gf r_0 r_1 <16== gf r'_0 r'_1.

Lemma monotone16_2_eq (gf: rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 -> rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 -> rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15) :
  monotone16_2 gf <-> _monotone16_2 gf.
Proof. unfold monotone16_2, _monotone16_2, le16. split; intros; eapply H; eassumption. Qed.

Lemma monotone16_2_map (gf: rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 -> rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 -> rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15)
      (MON: _monotone16_2 gf) :
  _monotone_2 (fun R0 R1 => uncurry16 (gf (curry16 R0) (curry16 R1))).
Proof.
  repeat_intros 6. apply uncurry_map16. apply MON; apply curry_map16; assumption.
Qed.

Variable gf_0 gf_1 : rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 -> rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 -> rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.

Theorem _paco16_2_0_mon: _monotone16_2 (paco16_2_0 gf_0 gf_1).
Proof.
  repeat_intros 6. eapply curry_map16, _paco_2_0_mon; apply uncurry_map16; assumption.
Qed.

Theorem _paco16_2_1_mon: _monotone16_2 (paco16_2_1 gf_0 gf_1).
Proof.
  repeat_intros 6. eapply curry_map16, _paco_2_1_mon; apply uncurry_map16; assumption.
Qed.

Theorem _paco16_2_0_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_0 <16== rr) (CIH: l <16== rr), l <16== paco16_2_0 gf_0 gf_1 rr r_1),
  l <16== paco16_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_16.
  eapply _paco_2_0_acc. intros.
  apply uncurry_adjoint1_16 in INC. apply uncurry_adjoint1_16 in CIH.
  apply uncurry_adjoint2_16.
  eapply le16_trans. eapply (OBG _ INC CIH).
  apply curry_map16.
  apply _paco_2_0_mon; try apply le1_refl; apply curry_bij1_16.
Qed.

Theorem _paco16_2_1_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_1 <16== rr) (CIH: l <16== rr), l <16== paco16_2_1 gf_0 gf_1 r_0 rr),
  l <16== paco16_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_16.
  eapply _paco_2_1_acc. intros.
  apply uncurry_adjoint1_16 in INC. apply uncurry_adjoint1_16 in CIH.
  apply uncurry_adjoint2_16.
  eapply le16_trans. eapply (OBG _ INC CIH).
  apply curry_map16.
  apply _paco_2_1_mon; try apply le1_refl; apply curry_bij1_16.
Qed.

Theorem _paco16_2_0_mult_strong: forall r_0 r_1,
  paco16_2_0 gf_0 gf_1 (upaco16_2_0 gf_0 gf_1 r_0 r_1) (upaco16_2_1 gf_0 gf_1 r_0 r_1) <16== paco16_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply curry_map16.
  eapply le1_trans; [| eapply _paco_2_0_mult_strong].
  apply _paco_2_0_mon; intros []; intros H; apply H.
Qed.

Theorem _paco16_2_1_mult_strong: forall r_0 r_1,
  paco16_2_1 gf_0 gf_1 (upaco16_2_0 gf_0 gf_1 r_0 r_1) (upaco16_2_1 gf_0 gf_1 r_0 r_1) <16== paco16_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply curry_map16.
  eapply le1_trans; [| eapply _paco_2_1_mult_strong].
  apply _paco_2_1_mon; intros []; intros H; apply H.
Qed.

Theorem _paco16_2_0_fold: forall r_0 r_1,
  gf_0 (upaco16_2_0 gf_0 gf_1 r_0 r_1) (upaco16_2_1 gf_0 gf_1 r_0 r_1) <16== paco16_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_16.
  eapply le1_trans; [| apply _paco_2_0_fold]. apply le1_refl.
Qed.

Theorem _paco16_2_1_fold: forall r_0 r_1,
  gf_1 (upaco16_2_0 gf_0 gf_1 r_0 r_1) (upaco16_2_1 gf_0 gf_1 r_0 r_1) <16== paco16_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_16.
  eapply le1_trans; [| apply _paco_2_1_fold]. apply le1_refl.
Qed.

Theorem _paco16_2_0_unfold: forall (MON: _monotone16_2 gf_0) (MON: _monotone16_2 gf_1) r_0 r_1,
  paco16_2_0 gf_0 gf_1 r_0 r_1 <16== gf_0 (upaco16_2_0 gf_0 gf_1 r_0 r_1) (upaco16_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  intros. apply curry_adjoint2_16.
  eapply _paco_2_0_unfold; apply monotone16_2_map; assumption.
Qed.

Theorem _paco16_2_1_unfold: forall (MON: _monotone16_2 gf_0) (MON: _monotone16_2 gf_1) r_0 r_1,
  paco16_2_1 gf_0 gf_1 r_0 r_1 <16== gf_1 (upaco16_2_0 gf_0 gf_1 r_0 r_1) (upaco16_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  intros. apply curry_adjoint2_16.
  eapply _paco_2_1_unfold; apply monotone16_2_map; assumption.
Qed.

Theorem paco16_2_0_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_0 <16= rr) (CIH: l <16= rr), l <16= paco16_2_0 gf_0 gf_1 rr r_1),
  l <16= paco16_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco16_2_0_acc.
Qed.

Theorem paco16_2_1_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_1 <16= rr) (CIH: l <16= rr), l <16= paco16_2_1 gf_0 gf_1 r_0 rr),
  l <16= paco16_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco16_2_1_acc.
Qed.

Theorem paco16_2_0_mon: monotone16_2 (paco16_2_0 gf_0 gf_1).
Proof.
  apply monotone16_2_eq.
  apply _paco16_2_0_mon.
Qed.

Theorem paco16_2_1_mon: monotone16_2 (paco16_2_1 gf_0 gf_1).
Proof.
  apply monotone16_2_eq.
  apply _paco16_2_1_mon.
Qed.

Theorem paco16_2_0_mult_strong: forall r_0 r_1,
  paco16_2_0 gf_0 gf_1 (upaco16_2_0 gf_0 gf_1 r_0 r_1) (upaco16_2_1 gf_0 gf_1 r_0 r_1) <16= paco16_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco16_2_0_mult_strong.
Qed.

Theorem paco16_2_1_mult_strong: forall r_0 r_1,
  paco16_2_1 gf_0 gf_1 (upaco16_2_0 gf_0 gf_1 r_0 r_1) (upaco16_2_1 gf_0 gf_1 r_0 r_1) <16= paco16_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco16_2_1_mult_strong.
Qed.

Corollary paco16_2_0_mult: forall r_0 r_1,
  paco16_2_0 gf_0 gf_1 (paco16_2_0 gf_0 gf_1 r_0 r_1) (paco16_2_1 gf_0 gf_1 r_0 r_1) <16= paco16_2_0 gf_0 gf_1 r_0 r_1.
Proof. intros; eapply paco16_2_0_mult_strong, paco16_2_0_mon; [apply PR|..]; intros; left; assumption. Qed.

Corollary paco16_2_1_mult: forall r_0 r_1,
  paco16_2_1 gf_0 gf_1 (paco16_2_0 gf_0 gf_1 r_0 r_1) (paco16_2_1 gf_0 gf_1 r_0 r_1) <16= paco16_2_1 gf_0 gf_1 r_0 r_1.
Proof. intros; eapply paco16_2_1_mult_strong, paco16_2_1_mon; [apply PR|..]; intros; left; assumption. Qed.

Theorem paco16_2_0_fold: forall r_0 r_1,
  gf_0 (upaco16_2_0 gf_0 gf_1 r_0 r_1) (upaco16_2_1 gf_0 gf_1 r_0 r_1) <16= paco16_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco16_2_0_fold.
Qed.

Theorem paco16_2_1_fold: forall r_0 r_1,
  gf_1 (upaco16_2_0 gf_0 gf_1 r_0 r_1) (upaco16_2_1 gf_0 gf_1 r_0 r_1) <16= paco16_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco16_2_1_fold.
Qed.

Theorem paco16_2_0_unfold: forall (MON: monotone16_2 gf_0) (MON: monotone16_2 gf_1) r_0 r_1,
  paco16_2_0 gf_0 gf_1 r_0 r_1 <16= gf_0 (upaco16_2_0 gf_0 gf_1 r_0 r_1) (upaco16_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  repeat_intros 2. eapply _paco16_2_0_unfold; apply monotone16_2_eq; assumption.
Qed.

Theorem paco16_2_1_unfold: forall (MON: monotone16_2 gf_0) (MON: monotone16_2 gf_1) r_0 r_1,
  paco16_2_1 gf_0 gf_1 r_0 r_1 <16= gf_1 (upaco16_2_0 gf_0 gf_1 r_0 r_1) (upaco16_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  repeat_intros 2. eapply _paco16_2_1_unfold; apply monotone16_2_eq; assumption.
Qed.

End Arg16_2.

Arguments paco16_2_0_acc : clear implicits.
Arguments paco16_2_1_acc : clear implicits.
Arguments paco16_2_0_mon : clear implicits.
Arguments paco16_2_1_mon : clear implicits.
Arguments paco16_2_0_mult_strong : clear implicits.
Arguments paco16_2_1_mult_strong : clear implicits.
Arguments paco16_2_0_mult : clear implicits.
Arguments paco16_2_1_mult : clear implicits.
Arguments paco16_2_0_fold : clear implicits.
Arguments paco16_2_1_fold : clear implicits.
Arguments paco16_2_0_unfold : clear implicits.
Arguments paco16_2_1_unfold : clear implicits.

Global Instance paco16_2_0_inst  (gf_0 gf_1 : rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15->_) r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : paco_class (paco16_2_0 gf_0 gf_1 r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15) :=
{ pacoacc    := paco16_2_0_acc gf_0 gf_1;
  pacomult   := paco16_2_0_mult gf_0 gf_1;
  pacofold   := paco16_2_0_fold gf_0 gf_1;
  pacounfold := paco16_2_0_unfold gf_0 gf_1 }.

Global Instance paco16_2_1_inst  (gf_0 gf_1 : rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15->_) r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : paco_class (paco16_2_1 gf_0 gf_1 r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15) :=
{ pacoacc    := paco16_2_1_acc gf_0 gf_1;
  pacomult   := paco16_2_1_mult gf_0 gf_1;
  pacofold   := paco16_2_1_fold gf_0 gf_1;
  pacounfold := paco16_2_1_unfold gf_0 gf_1 }.

(** 3 Mutual Coinduction *)

Section Arg16_3.

Definition monotone16_3 (gf: rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 -> rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 -> rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 -> rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15) :=
  forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 r_0 r_1 r_2 r'_0 r'_1 r'_2 (IN: gf r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15) (LE_0: r_0 <16= r'_0)(LE_1: r_1 <16= r'_1)(LE_2: r_2 <16= r'_2), gf r'_0 r'_1 r'_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15.

Definition _monotone16_3 (gf: rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 -> rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 -> rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 -> rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15) :=
  forall r_0 r_1 r_2 r'_0 r'_1 r'_2(LE_0: r_0 <16= r'_0)(LE_1: r_1 <16= r'_1)(LE_2: r_2 <16= r'_2), gf r_0 r_1 r_2 <16== gf r'_0 r'_1 r'_2.

Lemma monotone16_3_eq (gf: rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 -> rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 -> rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 -> rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15) :
  monotone16_3 gf <-> _monotone16_3 gf.
Proof. unfold monotone16_3, _monotone16_3, le16. split; intros; eapply H; eassumption. Qed.

Lemma monotone16_3_map (gf: rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 -> rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 -> rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 -> rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15)
      (MON: _monotone16_3 gf) :
  _monotone_3 (fun R0 R1 R2 => uncurry16 (gf (curry16 R0) (curry16 R1) (curry16 R2))).
Proof.
  repeat_intros 9. apply uncurry_map16. apply MON; apply curry_map16; assumption.
Qed.

Variable gf_0 gf_1 gf_2 : rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 -> rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 -> rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 -> rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.
Arguments gf_2 : clear implicits.

Theorem _paco16_3_0_mon: _monotone16_3 (paco16_3_0 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 9. eapply curry_map16, _paco_3_0_mon; apply uncurry_map16; assumption.
Qed.

Theorem _paco16_3_1_mon: _monotone16_3 (paco16_3_1 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 9. eapply curry_map16, _paco_3_1_mon; apply uncurry_map16; assumption.
Qed.

Theorem _paco16_3_2_mon: _monotone16_3 (paco16_3_2 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 9. eapply curry_map16, _paco_3_2_mon; apply uncurry_map16; assumption.
Qed.

Theorem _paco16_3_0_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_0 <16== rr) (CIH: l <16== rr), l <16== paco16_3_0 gf_0 gf_1 gf_2 rr r_1 r_2),
  l <16== paco16_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_16.
  eapply _paco_3_0_acc. intros.
  apply uncurry_adjoint1_16 in INC. apply uncurry_adjoint1_16 in CIH.
  apply uncurry_adjoint2_16.
  eapply le16_trans. eapply (OBG _ INC CIH).
  apply curry_map16.
  apply _paco_3_0_mon; try apply le1_refl; apply curry_bij1_16.
Qed.

Theorem _paco16_3_1_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_1 <16== rr) (CIH: l <16== rr), l <16== paco16_3_1 gf_0 gf_1 gf_2 r_0 rr r_2),
  l <16== paco16_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_16.
  eapply _paco_3_1_acc. intros.
  apply uncurry_adjoint1_16 in INC. apply uncurry_adjoint1_16 in CIH.
  apply uncurry_adjoint2_16.
  eapply le16_trans. eapply (OBG _ INC CIH).
  apply curry_map16.
  apply _paco_3_1_mon; try apply le1_refl; apply curry_bij1_16.
Qed.

Theorem _paco16_3_2_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_2 <16== rr) (CIH: l <16== rr), l <16== paco16_3_2 gf_0 gf_1 gf_2 r_0 r_1 rr),
  l <16== paco16_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_16.
  eapply _paco_3_2_acc. intros.
  apply uncurry_adjoint1_16 in INC. apply uncurry_adjoint1_16 in CIH.
  apply uncurry_adjoint2_16.
  eapply le16_trans. eapply (OBG _ INC CIH).
  apply curry_map16.
  apply _paco_3_2_mon; try apply le1_refl; apply curry_bij1_16.
Qed.

Theorem _paco16_3_0_mult_strong: forall r_0 r_1 r_2,
  paco16_3_0 gf_0 gf_1 gf_2 (upaco16_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco16_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco16_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <16== paco16_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply curry_map16.
  eapply le1_trans; [| eapply _paco_3_0_mult_strong].
  apply _paco_3_0_mon; intros []; intros H; apply H.
Qed.

Theorem _paco16_3_1_mult_strong: forall r_0 r_1 r_2,
  paco16_3_1 gf_0 gf_1 gf_2 (upaco16_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco16_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco16_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <16== paco16_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply curry_map16.
  eapply le1_trans; [| eapply _paco_3_1_mult_strong].
  apply _paco_3_1_mon; intros []; intros H; apply H.
Qed.

Theorem _paco16_3_2_mult_strong: forall r_0 r_1 r_2,
  paco16_3_2 gf_0 gf_1 gf_2 (upaco16_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco16_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco16_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <16== paco16_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply curry_map16.
  eapply le1_trans; [| eapply _paco_3_2_mult_strong].
  apply _paco_3_2_mon; intros []; intros H; apply H.
Qed.

Theorem _paco16_3_0_fold: forall r_0 r_1 r_2,
  gf_0 (upaco16_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco16_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco16_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <16== paco16_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_16.
  eapply le1_trans; [| apply _paco_3_0_fold]. apply le1_refl.
Qed.

Theorem _paco16_3_1_fold: forall r_0 r_1 r_2,
  gf_1 (upaco16_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco16_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco16_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <16== paco16_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_16.
  eapply le1_trans; [| apply _paco_3_1_fold]. apply le1_refl.
Qed.

Theorem _paco16_3_2_fold: forall r_0 r_1 r_2,
  gf_2 (upaco16_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco16_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco16_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <16== paco16_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_16.
  eapply le1_trans; [| apply _paco_3_2_fold]. apply le1_refl.
Qed.

Theorem _paco16_3_0_unfold: forall (MON: _monotone16_3 gf_0) (MON: _monotone16_3 gf_1) (MON: _monotone16_3 gf_2) r_0 r_1 r_2,
  paco16_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 <16== gf_0 (upaco16_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco16_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco16_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  intros. apply curry_adjoint2_16.
  eapply _paco_3_0_unfold; apply monotone16_3_map; assumption.
Qed.

Theorem _paco16_3_1_unfold: forall (MON: _monotone16_3 gf_0) (MON: _monotone16_3 gf_1) (MON: _monotone16_3 gf_2) r_0 r_1 r_2,
  paco16_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 <16== gf_1 (upaco16_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco16_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco16_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  intros. apply curry_adjoint2_16.
  eapply _paco_3_1_unfold; apply monotone16_3_map; assumption.
Qed.

Theorem _paco16_3_2_unfold: forall (MON: _monotone16_3 gf_0) (MON: _monotone16_3 gf_1) (MON: _monotone16_3 gf_2) r_0 r_1 r_2,
  paco16_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 <16== gf_2 (upaco16_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco16_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco16_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  intros. apply curry_adjoint2_16.
  eapply _paco_3_2_unfold; apply monotone16_3_map; assumption.
Qed.

Theorem paco16_3_0_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_0 <16= rr) (CIH: l <16= rr), l <16= paco16_3_0 gf_0 gf_1 gf_2 rr r_1 r_2),
  l <16= paco16_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco16_3_0_acc.
Qed.

Theorem paco16_3_1_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_1 <16= rr) (CIH: l <16= rr), l <16= paco16_3_1 gf_0 gf_1 gf_2 r_0 rr r_2),
  l <16= paco16_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco16_3_1_acc.
Qed.

Theorem paco16_3_2_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_2 <16= rr) (CIH: l <16= rr), l <16= paco16_3_2 gf_0 gf_1 gf_2 r_0 r_1 rr),
  l <16= paco16_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco16_3_2_acc.
Qed.

Theorem paco16_3_0_mon: monotone16_3 (paco16_3_0 gf_0 gf_1 gf_2).
Proof.
  apply monotone16_3_eq.
  apply _paco16_3_0_mon.
Qed.

Theorem paco16_3_1_mon: monotone16_3 (paco16_3_1 gf_0 gf_1 gf_2).
Proof.
  apply monotone16_3_eq.
  apply _paco16_3_1_mon.
Qed.

Theorem paco16_3_2_mon: monotone16_3 (paco16_3_2 gf_0 gf_1 gf_2).
Proof.
  apply monotone16_3_eq.
  apply _paco16_3_2_mon.
Qed.

Theorem paco16_3_0_mult_strong: forall r_0 r_1 r_2,
  paco16_3_0 gf_0 gf_1 gf_2 (upaco16_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco16_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco16_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <16= paco16_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco16_3_0_mult_strong.
Qed.

Theorem paco16_3_1_mult_strong: forall r_0 r_1 r_2,
  paco16_3_1 gf_0 gf_1 gf_2 (upaco16_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco16_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco16_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <16= paco16_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco16_3_1_mult_strong.
Qed.

Theorem paco16_3_2_mult_strong: forall r_0 r_1 r_2,
  paco16_3_2 gf_0 gf_1 gf_2 (upaco16_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco16_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco16_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <16= paco16_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco16_3_2_mult_strong.
Qed.

Corollary paco16_3_0_mult: forall r_0 r_1 r_2,
  paco16_3_0 gf_0 gf_1 gf_2 (paco16_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco16_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco16_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <16= paco16_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco16_3_0_mult_strong, paco16_3_0_mon; [apply PR|..]; intros; left; assumption. Qed.

Corollary paco16_3_1_mult: forall r_0 r_1 r_2,
  paco16_3_1 gf_0 gf_1 gf_2 (paco16_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco16_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco16_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <16= paco16_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco16_3_1_mult_strong, paco16_3_1_mon; [apply PR|..]; intros; left; assumption. Qed.

Corollary paco16_3_2_mult: forall r_0 r_1 r_2,
  paco16_3_2 gf_0 gf_1 gf_2 (paco16_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco16_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco16_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <16= paco16_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco16_3_2_mult_strong, paco16_3_2_mon; [apply PR|..]; intros; left; assumption. Qed.

Theorem paco16_3_0_fold: forall r_0 r_1 r_2,
  gf_0 (upaco16_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco16_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco16_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <16= paco16_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco16_3_0_fold.
Qed.

Theorem paco16_3_1_fold: forall r_0 r_1 r_2,
  gf_1 (upaco16_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco16_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco16_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <16= paco16_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco16_3_1_fold.
Qed.

Theorem paco16_3_2_fold: forall r_0 r_1 r_2,
  gf_2 (upaco16_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco16_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco16_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <16= paco16_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco16_3_2_fold.
Qed.

Theorem paco16_3_0_unfold: forall (MON: monotone16_3 gf_0) (MON: monotone16_3 gf_1) (MON: monotone16_3 gf_2) r_0 r_1 r_2,
  paco16_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 <16= gf_0 (upaco16_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco16_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco16_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  repeat_intros 3. eapply _paco16_3_0_unfold; apply monotone16_3_eq; assumption.
Qed.

Theorem paco16_3_1_unfold: forall (MON: monotone16_3 gf_0) (MON: monotone16_3 gf_1) (MON: monotone16_3 gf_2) r_0 r_1 r_2,
  paco16_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 <16= gf_1 (upaco16_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco16_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco16_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  repeat_intros 3. eapply _paco16_3_1_unfold; apply monotone16_3_eq; assumption.
Qed.

Theorem paco16_3_2_unfold: forall (MON: monotone16_3 gf_0) (MON: monotone16_3 gf_1) (MON: monotone16_3 gf_2) r_0 r_1 r_2,
  paco16_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 <16= gf_2 (upaco16_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco16_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco16_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  repeat_intros 3. eapply _paco16_3_2_unfold; apply monotone16_3_eq; assumption.
Qed.

End Arg16_3.

Arguments paco16_3_0_acc : clear implicits.
Arguments paco16_3_1_acc : clear implicits.
Arguments paco16_3_2_acc : clear implicits.
Arguments paco16_3_0_mon : clear implicits.
Arguments paco16_3_1_mon : clear implicits.
Arguments paco16_3_2_mon : clear implicits.
Arguments paco16_3_0_mult_strong : clear implicits.
Arguments paco16_3_1_mult_strong : clear implicits.
Arguments paco16_3_2_mult_strong : clear implicits.
Arguments paco16_3_0_mult : clear implicits.
Arguments paco16_3_1_mult : clear implicits.
Arguments paco16_3_2_mult : clear implicits.
Arguments paco16_3_0_fold : clear implicits.
Arguments paco16_3_1_fold : clear implicits.
Arguments paco16_3_2_fold : clear implicits.
Arguments paco16_3_0_unfold : clear implicits.
Arguments paco16_3_1_unfold : clear implicits.
Arguments paco16_3_2_unfold : clear implicits.

Global Instance paco16_3_0_inst  (gf_0 gf_1 gf_2 : rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : paco_class (paco16_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15) :=
{ pacoacc    := paco16_3_0_acc gf_0 gf_1 gf_2;
  pacomult   := paco16_3_0_mult gf_0 gf_1 gf_2;
  pacofold   := paco16_3_0_fold gf_0 gf_1 gf_2;
  pacounfold := paco16_3_0_unfold gf_0 gf_1 gf_2 }.

Global Instance paco16_3_1_inst  (gf_0 gf_1 gf_2 : rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : paco_class (paco16_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15) :=
{ pacoacc    := paco16_3_1_acc gf_0 gf_1 gf_2;
  pacomult   := paco16_3_1_mult gf_0 gf_1 gf_2;
  pacofold   := paco16_3_1_fold gf_0 gf_1 gf_2;
  pacounfold := paco16_3_1_unfold gf_0 gf_1 gf_2 }.

Global Instance paco16_3_2_inst  (gf_0 gf_1 gf_2 : rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : paco_class (paco16_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15) :=
{ pacoacc    := paco16_3_2_acc gf_0 gf_1 gf_2;
  pacomult   := paco16_3_2_mult gf_0 gf_1 gf_2;
  pacofold   := paco16_3_2_fold gf_0 gf_1 gf_2;
  pacounfold := paco16_3_2_unfold gf_0 gf_1 gf_2 }.

End PACO16.

Global Opaque paco16.

Hint Unfold upaco16.
Hint Resolve paco16_fold.
Hint Unfold monotone16.

Global Opaque paco16_2_0.
Global Opaque paco16_2_1.

Hint Unfold upaco16_2_0.
Hint Unfold upaco16_2_1.
Hint Resolve paco16_2_0_fold.
Hint Resolve paco16_2_1_fold.
Hint Unfold monotone16_2.

Global Opaque paco16_3_0.
Global Opaque paco16_3_1.
Global Opaque paco16_3_2.

Hint Unfold upaco16_3_0.
Hint Unfold upaco16_3_1.
Hint Unfold upaco16_3_2.
Hint Resolve paco16_3_0_fold.
Hint Resolve paco16_3_1_fold.
Hint Resolve paco16_3_2_fold.
Hint Unfold monotone16_3.

