Require Export paconotation pacotacuser.
Require Import paconotation_internal pacotac pacon.
Set Implicit Arguments.

Section PACO15.

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

Record sig15T :=
  exist15T { 
      proj15T0: @T0;
      proj15T1: @T1 proj15T0;
      proj15T2: @T2 proj15T0 proj15T1;
      proj15T3: @T3 proj15T0 proj15T1 proj15T2;
      proj15T4: @T4 proj15T0 proj15T1 proj15T2 proj15T3;
      proj15T5: @T5 proj15T0 proj15T1 proj15T2 proj15T3 proj15T4;
      proj15T6: @T6 proj15T0 proj15T1 proj15T2 proj15T3 proj15T4 proj15T5;
      proj15T7: @T7 proj15T0 proj15T1 proj15T2 proj15T3 proj15T4 proj15T5 proj15T6;
      proj15T8: @T8 proj15T0 proj15T1 proj15T2 proj15T3 proj15T4 proj15T5 proj15T6 proj15T7;
      proj15T9: @T9 proj15T0 proj15T1 proj15T2 proj15T3 proj15T4 proj15T5 proj15T6 proj15T7 proj15T8;
      proj15T10: @T10 proj15T0 proj15T1 proj15T2 proj15T3 proj15T4 proj15T5 proj15T6 proj15T7 proj15T8 proj15T9;
      proj15T11: @T11 proj15T0 proj15T1 proj15T2 proj15T3 proj15T4 proj15T5 proj15T6 proj15T7 proj15T8 proj15T9 proj15T10;
      proj15T12: @T12 proj15T0 proj15T1 proj15T2 proj15T3 proj15T4 proj15T5 proj15T6 proj15T7 proj15T8 proj15T9 proj15T10 proj15T11;
      proj15T13: @T13 proj15T0 proj15T1 proj15T2 proj15T3 proj15T4 proj15T5 proj15T6 proj15T7 proj15T8 proj15T9 proj15T10 proj15T11 proj15T12;
      proj15T14: @T14 proj15T0 proj15T1 proj15T2 proj15T3 proj15T4 proj15T5 proj15T6 proj15T7 proj15T8 proj15T9 proj15T10 proj15T11 proj15T12 proj15T13;
    }.

Definition uncurry15 (R: rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14): rel1 sig15T := fun x => R (proj15T0 x) (proj15T1 x) (proj15T2 x) (proj15T3 x) (proj15T4 x) (proj15T5 x) (proj15T6 x) (proj15T7 x) (proj15T8 x) (proj15T9 x) (proj15T10 x) (proj15T11 x) (proj15T12 x) (proj15T13 x) (proj15T14 x).

Definition curry15 (R: rel1 sig15T): rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 :=
  fun x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 => R (exist15T x14).

Lemma uncurry_map15 r0 r1 (LE : r0 <15== r1) : uncurry15 r0 <1== uncurry15 r1.
Proof. intros [] H. apply LE. apply H. Qed.

Lemma uncurry_map_rev15 r0 r1 (LE: uncurry15 r0 <1== uncurry15 r1) : r0 <15== r1.
Proof.
  repeat_intros 15. intros H. apply (LE (exist15T x14) H).
Qed.

Lemma curry_map15 r0 r1 (LE: r0 <1== r1) : curry15 r0 <15== curry15 r1.
Proof. 
  repeat_intros 15. intros H. apply (LE (exist15T x14) H).
Qed.

Lemma curry_map_rev15 r0 r1 (LE: curry15 r0 <15== curry15 r1) : r0 <1== r1.
Proof. 
  intros [] H. apply LE. apply H.
Qed.

Lemma uncurry_bij1_15 r : curry15 (uncurry15 r) <15== r.
Proof. unfold le15. repeat_intros 15. intros H. apply H. Qed.

Lemma uncurry_bij2_15 r : r <15== curry15 (uncurry15 r).
Proof. unfold le15. repeat_intros 15. intros H. apply H. Qed.

Lemma curry_bij1_15 r : uncurry15 (curry15 r) <1== r.
Proof. intros []. intro H. apply H. Qed.

Lemma curry_bij2_15 r : r <1== uncurry15 (curry15 r).
Proof. intros []. intro H. apply H. Qed.

Lemma uncurry_adjoint1_15 r0 r1 (LE: uncurry15 r0 <1== r1) : r0 <15== curry15 r1.
Proof.
  apply uncurry_map_rev15. eapply le1_trans; [apply LE|]. apply curry_bij2_15.
Qed.

Lemma uncurry_adjoint2_15 r0 r1 (LE: r0 <15== curry15 r1) : uncurry15 r0 <1== r1.
Proof.
  apply curry_map_rev15. eapply le15_trans; [|apply LE]. apply uncurry_bij2_15.
Qed.

Lemma curry_adjoint1_15 r0 r1 (LE: curry15 r0 <15== r1) : r0 <1== uncurry15 r1.
Proof.
  apply curry_map_rev15. eapply le15_trans; [apply LE|]. apply uncurry_bij2_15.
Qed.

Lemma curry_adjoint2_15 r0 r1 (LE: r0 <1== uncurry15 r1) : curry15 r0 <15== r1.
Proof.
  apply uncurry_map_rev15. eapply le1_trans; [|apply LE]. apply curry_bij1_15.
Qed.

(** ** Predicates of Arity 15
*)

Section Arg15_def.
Variable gf : rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 -> rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14.
Arguments gf : clear implicits.

Definition paco15( r: rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14) : rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 :=
  curry15 (paco (fun R0 => uncurry15 (gf (curry15 R0))) (uncurry15 r)).

Definition upaco15( r: rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14) := paco15 r \15/ r.
End Arg15_def.
Arguments paco15 : clear implicits.
Arguments upaco15 : clear implicits.
Hint Unfold upaco15.

Section Arg15_2_def.
Variable gf_0 gf_1 : rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 -> rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 -> rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.

Definition paco15_2_0( r_0 r_1: rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14) : rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 :=
  curry15 (paco_2_0 (fun R0 R1 => uncurry15 (gf_0 (curry15 R0) (curry15 R1))) (fun R0 R1 => uncurry15 (gf_1 (curry15 R0) (curry15 R1))) (uncurry15 r_0) (uncurry15 r_1)).

Definition paco15_2_1( r_0 r_1: rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14) : rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 :=
  curry15 (paco_2_1 (fun R0 R1 => uncurry15 (gf_0 (curry15 R0) (curry15 R1))) (fun R0 R1 => uncurry15 (gf_1 (curry15 R0) (curry15 R1))) (uncurry15 r_0) (uncurry15 r_1)).

Definition upaco15_2_0( r_0 r_1: rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14) := paco15_2_0 r_0 r_1 \15/ r_0.
Definition upaco15_2_1( r_0 r_1: rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14) := paco15_2_1 r_0 r_1 \15/ r_1.
End Arg15_2_def.
Arguments paco15_2_0 : clear implicits.
Arguments upaco15_2_0 : clear implicits.
Hint Unfold upaco15_2_0.
Arguments paco15_2_1 : clear implicits.
Arguments upaco15_2_1 : clear implicits.
Hint Unfold upaco15_2_1.

Section Arg15_3_def.
Variable gf_0 gf_1 gf_2 : rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 -> rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 -> rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 -> rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.
Arguments gf_2 : clear implicits.

Definition paco15_3_0( r_0 r_1 r_2: rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14) : rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 :=
  curry15 (paco_3_0 (fun R0 R1 R2 => uncurry15 (gf_0 (curry15 R0) (curry15 R1) (curry15 R2))) (fun R0 R1 R2 => uncurry15 (gf_1 (curry15 R0) (curry15 R1) (curry15 R2))) (fun R0 R1 R2 => uncurry15 (gf_2 (curry15 R0) (curry15 R1) (curry15 R2))) (uncurry15 r_0) (uncurry15 r_1) (uncurry15 r_2)).

Definition paco15_3_1( r_0 r_1 r_2: rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14) : rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 :=
  curry15 (paco_3_1 (fun R0 R1 R2 => uncurry15 (gf_0 (curry15 R0) (curry15 R1) (curry15 R2))) (fun R0 R1 R2 => uncurry15 (gf_1 (curry15 R0) (curry15 R1) (curry15 R2))) (fun R0 R1 R2 => uncurry15 (gf_2 (curry15 R0) (curry15 R1) (curry15 R2))) (uncurry15 r_0) (uncurry15 r_1) (uncurry15 r_2)).

Definition paco15_3_2( r_0 r_1 r_2: rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14) : rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 :=
  curry15 (paco_3_2 (fun R0 R1 R2 => uncurry15 (gf_0 (curry15 R0) (curry15 R1) (curry15 R2))) (fun R0 R1 R2 => uncurry15 (gf_1 (curry15 R0) (curry15 R1) (curry15 R2))) (fun R0 R1 R2 => uncurry15 (gf_2 (curry15 R0) (curry15 R1) (curry15 R2))) (uncurry15 r_0) (uncurry15 r_1) (uncurry15 r_2)).

Definition upaco15_3_0( r_0 r_1 r_2: rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14) := paco15_3_0 r_0 r_1 r_2 \15/ r_0.
Definition upaco15_3_1( r_0 r_1 r_2: rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14) := paco15_3_1 r_0 r_1 r_2 \15/ r_1.
Definition upaco15_3_2( r_0 r_1 r_2: rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14) := paco15_3_2 r_0 r_1 r_2 \15/ r_2.
End Arg15_3_def.
Arguments paco15_3_0 : clear implicits.
Arguments upaco15_3_0 : clear implicits.
Hint Unfold upaco15_3_0.
Arguments paco15_3_1 : clear implicits.
Arguments upaco15_3_1 : clear implicits.
Hint Unfold upaco15_3_1.
Arguments paco15_3_2 : clear implicits.
Arguments upaco15_3_2 : clear implicits.
Hint Unfold upaco15_3_2.

(** 1 Mutual Coinduction *)

Section Arg15_1.

Definition monotone15 (gf: rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 -> rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14) :=
  forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 r r' (IN: gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14) (LE: r <15= r'), gf r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14.

Definition _monotone15 (gf: rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 -> rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14) :=
  forall r r'(LE: r <15= r'), gf r <15== gf r'.

Lemma monotone15_eq (gf: rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 -> rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14) :
  monotone15 gf <-> _monotone15 gf.
Proof. unfold monotone15, _monotone15, le15. split; intros; eapply H; eassumption. Qed.

Lemma monotone15_map (gf: rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 -> rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14)
      (MON: _monotone15 gf) :
  _monotone (fun R0 => uncurry15 (gf (curry15 R0))).
Proof.
  repeat_intros 3. apply uncurry_map15. apply MON; apply curry_map15; assumption.
Qed.

Variable gf : rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 -> rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14.
Arguments gf : clear implicits.

Theorem _paco15_mon: _monotone15 (paco15 gf).
Proof.
  repeat_intros 3. eapply curry_map15, _paco_mon; apply uncurry_map15; assumption.
Qed.

Theorem _paco15_acc: forall
  l r (OBG: forall rr (INC: r <15== rr) (CIH: l <15== rr), l <15== paco15 gf rr),
  l <15== paco15 gf r.
Proof.
  intros. apply uncurry_adjoint1_15.
  eapply _paco_acc. intros.
  apply uncurry_adjoint1_15 in INC. apply uncurry_adjoint1_15 in CIH.
  apply uncurry_adjoint2_15.
  eapply le15_trans. eapply (OBG _ INC CIH).
  apply curry_map15.
  apply _paco_mon; try apply le1_refl; apply curry_bij1_15.
Qed.

Theorem _paco15_mult_strong: forall r,
  paco15 gf (upaco15 gf r) <15== paco15 gf r.
Proof.
  intros. apply curry_map15.
  eapply le1_trans; [| eapply _paco_mult_strong].
  apply _paco_mon; intros []; intros H; apply H.
Qed.

Theorem _paco15_fold: forall r,
  gf (upaco15 gf r) <15== paco15 gf r.
Proof.
  intros. apply uncurry_adjoint1_15.
  eapply le1_trans; [| apply _paco_fold]. apply le1_refl.
Qed.

Theorem _paco15_unfold: forall (MON: _monotone15 gf) r,
  paco15 gf r <15== gf (upaco15 gf r).
Proof.
  intros. apply curry_adjoint2_15.
  eapply _paco_unfold; apply monotone15_map; assumption.
Qed.

Theorem paco15_acc: forall
  l r (OBG: forall rr (INC: r <15= rr) (CIH: l <15= rr), l <15= paco15 gf rr),
  l <15= paco15 gf r.
Proof.
  apply _paco15_acc.
Qed.

Theorem paco15_mon: monotone15 (paco15 gf).
Proof.
  apply monotone15_eq.
  apply _paco15_mon.
Qed.

Theorem upaco15_mon: monotone15 (upaco15 gf).
Proof.
  repeat_intros 17. intros R  LE0.
  destruct R.
  - left. eapply paco15_mon. apply H. apply LE0.
  - right. apply LE0, H.
Qed.
Theorem paco15_mult_strong: forall r,
  paco15 gf (upaco15 gf r) <15= paco15 gf r.
Proof.
  apply _paco15_mult_strong.
Qed.

Corollary paco15_mult: forall r,
  paco15 gf (paco15 gf r) <15= paco15 gf r.
Proof. intros; eapply paco15_mult_strong, paco15_mon; [apply PR|..]; intros; left; assumption. Qed.

Theorem paco15_fold: forall r,
  gf (upaco15 gf r) <15= paco15 gf r.
Proof.
  apply _paco15_fold.
Qed.

Theorem paco15_unfold: forall (MON: monotone15 gf) r,
  paco15 gf r <15= gf (upaco15 gf r).
Proof.
  repeat_intros 1. eapply _paco15_unfold; apply monotone15_eq; assumption.
Qed.

End Arg15_1.

Arguments paco15_acc : clear implicits.
Arguments paco15_mon : clear implicits.
Arguments upaco15_mon : clear implicits.
Arguments paco15_mult_strong : clear implicits.
Arguments paco15_mult : clear implicits.
Arguments paco15_fold : clear implicits.
Arguments paco15_unfold : clear implicits.

Global Instance paco15_inst  (gf : rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14->_) r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : paco_class (paco15 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14) :=
{ pacoacc    := paco15_acc gf;
  pacomult   := paco15_mult gf;
  pacofold   := paco15_fold gf;
  pacounfold := paco15_unfold gf }.

(** 2 Mutual Coinduction *)

Section Arg15_2.

Definition monotone15_2 (gf: rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 -> rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 -> rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14) :=
  forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 r_0 r_1 r'_0 r'_1 (IN: gf r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14) (LE_0: r_0 <15= r'_0)(LE_1: r_1 <15= r'_1), gf r'_0 r'_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14.

Definition _monotone15_2 (gf: rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 -> rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 -> rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14) :=
  forall r_0 r_1 r'_0 r'_1(LE_0: r_0 <15= r'_0)(LE_1: r_1 <15= r'_1), gf r_0 r_1 <15== gf r'_0 r'_1.

Lemma monotone15_2_eq (gf: rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 -> rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 -> rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14) :
  monotone15_2 gf <-> _monotone15_2 gf.
Proof. unfold monotone15_2, _monotone15_2, le15. split; intros; eapply H; eassumption. Qed.

Lemma monotone15_2_map (gf: rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 -> rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 -> rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14)
      (MON: _monotone15_2 gf) :
  _monotone_2 (fun R0 R1 => uncurry15 (gf (curry15 R0) (curry15 R1))).
Proof.
  repeat_intros 6. apply uncurry_map15. apply MON; apply curry_map15; assumption.
Qed.

Variable gf_0 gf_1 : rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 -> rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 -> rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.

Theorem _paco15_2_0_mon: _monotone15_2 (paco15_2_0 gf_0 gf_1).
Proof.
  repeat_intros 6. eapply curry_map15, _paco_2_0_mon; apply uncurry_map15; assumption.
Qed.

Theorem _paco15_2_1_mon: _monotone15_2 (paco15_2_1 gf_0 gf_1).
Proof.
  repeat_intros 6. eapply curry_map15, _paco_2_1_mon; apply uncurry_map15; assumption.
Qed.

Theorem _paco15_2_0_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_0 <15== rr) (CIH: l <15== rr), l <15== paco15_2_0 gf_0 gf_1 rr r_1),
  l <15== paco15_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_15.
  eapply _paco_2_0_acc. intros.
  apply uncurry_adjoint1_15 in INC. apply uncurry_adjoint1_15 in CIH.
  apply uncurry_adjoint2_15.
  eapply le15_trans. eapply (OBG _ INC CIH).
  apply curry_map15.
  apply _paco_2_0_mon; try apply le1_refl; apply curry_bij1_15.
Qed.

Theorem _paco15_2_1_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_1 <15== rr) (CIH: l <15== rr), l <15== paco15_2_1 gf_0 gf_1 r_0 rr),
  l <15== paco15_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_15.
  eapply _paco_2_1_acc. intros.
  apply uncurry_adjoint1_15 in INC. apply uncurry_adjoint1_15 in CIH.
  apply uncurry_adjoint2_15.
  eapply le15_trans. eapply (OBG _ INC CIH).
  apply curry_map15.
  apply _paco_2_1_mon; try apply le1_refl; apply curry_bij1_15.
Qed.

Theorem _paco15_2_0_mult_strong: forall r_0 r_1,
  paco15_2_0 gf_0 gf_1 (upaco15_2_0 gf_0 gf_1 r_0 r_1) (upaco15_2_1 gf_0 gf_1 r_0 r_1) <15== paco15_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply curry_map15.
  eapply le1_trans; [| eapply _paco_2_0_mult_strong].
  apply _paco_2_0_mon; intros []; intros H; apply H.
Qed.

Theorem _paco15_2_1_mult_strong: forall r_0 r_1,
  paco15_2_1 gf_0 gf_1 (upaco15_2_0 gf_0 gf_1 r_0 r_1) (upaco15_2_1 gf_0 gf_1 r_0 r_1) <15== paco15_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply curry_map15.
  eapply le1_trans; [| eapply _paco_2_1_mult_strong].
  apply _paco_2_1_mon; intros []; intros H; apply H.
Qed.

Theorem _paco15_2_0_fold: forall r_0 r_1,
  gf_0 (upaco15_2_0 gf_0 gf_1 r_0 r_1) (upaco15_2_1 gf_0 gf_1 r_0 r_1) <15== paco15_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_15.
  eapply le1_trans; [| apply _paco_2_0_fold]. apply le1_refl.
Qed.

Theorem _paco15_2_1_fold: forall r_0 r_1,
  gf_1 (upaco15_2_0 gf_0 gf_1 r_0 r_1) (upaco15_2_1 gf_0 gf_1 r_0 r_1) <15== paco15_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_15.
  eapply le1_trans; [| apply _paco_2_1_fold]. apply le1_refl.
Qed.

Theorem _paco15_2_0_unfold: forall (MON: _monotone15_2 gf_0) (MON: _monotone15_2 gf_1) r_0 r_1,
  paco15_2_0 gf_0 gf_1 r_0 r_1 <15== gf_0 (upaco15_2_0 gf_0 gf_1 r_0 r_1) (upaco15_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  intros. apply curry_adjoint2_15.
  eapply _paco_2_0_unfold; apply monotone15_2_map; assumption.
Qed.

Theorem _paco15_2_1_unfold: forall (MON: _monotone15_2 gf_0) (MON: _monotone15_2 gf_1) r_0 r_1,
  paco15_2_1 gf_0 gf_1 r_0 r_1 <15== gf_1 (upaco15_2_0 gf_0 gf_1 r_0 r_1) (upaco15_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  intros. apply curry_adjoint2_15.
  eapply _paco_2_1_unfold; apply monotone15_2_map; assumption.
Qed.

Theorem paco15_2_0_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_0 <15= rr) (CIH: l <15= rr), l <15= paco15_2_0 gf_0 gf_1 rr r_1),
  l <15= paco15_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco15_2_0_acc.
Qed.

Theorem paco15_2_1_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_1 <15= rr) (CIH: l <15= rr), l <15= paco15_2_1 gf_0 gf_1 r_0 rr),
  l <15= paco15_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco15_2_1_acc.
Qed.

Theorem paco15_2_0_mon: monotone15_2 (paco15_2_0 gf_0 gf_1).
Proof.
  apply monotone15_2_eq.
  apply _paco15_2_0_mon.
Qed.

Theorem paco15_2_1_mon: monotone15_2 (paco15_2_1 gf_0 gf_1).
Proof.
  apply monotone15_2_eq.
  apply _paco15_2_1_mon.
Qed.

Theorem upaco15_2_0_mon: monotone15_2 (upaco15_2_0 gf_0 gf_1).
Proof.
  repeat_intros 19. intros R  LE0 LE1.
  destruct R.
  - left. eapply paco15_2_0_mon. apply H. apply LE0. apply LE1.
  - right. apply LE0, H.
Qed.
Theorem upaco15_2_1_mon: monotone15_2 (upaco15_2_1 gf_0 gf_1).
Proof.
  repeat_intros 19. intros R  LE0 LE1.
  destruct R.
  - left. eapply paco15_2_1_mon. apply H. apply LE0. apply LE1.
  - right. apply LE1, H.
Qed.
Theorem paco15_2_0_mult_strong: forall r_0 r_1,
  paco15_2_0 gf_0 gf_1 (upaco15_2_0 gf_0 gf_1 r_0 r_1) (upaco15_2_1 gf_0 gf_1 r_0 r_1) <15= paco15_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco15_2_0_mult_strong.
Qed.

Theorem paco15_2_1_mult_strong: forall r_0 r_1,
  paco15_2_1 gf_0 gf_1 (upaco15_2_0 gf_0 gf_1 r_0 r_1) (upaco15_2_1 gf_0 gf_1 r_0 r_1) <15= paco15_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco15_2_1_mult_strong.
Qed.

Corollary paco15_2_0_mult: forall r_0 r_1,
  paco15_2_0 gf_0 gf_1 (paco15_2_0 gf_0 gf_1 r_0 r_1) (paco15_2_1 gf_0 gf_1 r_0 r_1) <15= paco15_2_0 gf_0 gf_1 r_0 r_1.
Proof. intros; eapply paco15_2_0_mult_strong, paco15_2_0_mon; [apply PR|..]; intros; left; assumption. Qed.

Corollary paco15_2_1_mult: forall r_0 r_1,
  paco15_2_1 gf_0 gf_1 (paco15_2_0 gf_0 gf_1 r_0 r_1) (paco15_2_1 gf_0 gf_1 r_0 r_1) <15= paco15_2_1 gf_0 gf_1 r_0 r_1.
Proof. intros; eapply paco15_2_1_mult_strong, paco15_2_1_mon; [apply PR|..]; intros; left; assumption. Qed.

Theorem paco15_2_0_fold: forall r_0 r_1,
  gf_0 (upaco15_2_0 gf_0 gf_1 r_0 r_1) (upaco15_2_1 gf_0 gf_1 r_0 r_1) <15= paco15_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco15_2_0_fold.
Qed.

Theorem paco15_2_1_fold: forall r_0 r_1,
  gf_1 (upaco15_2_0 gf_0 gf_1 r_0 r_1) (upaco15_2_1 gf_0 gf_1 r_0 r_1) <15= paco15_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco15_2_1_fold.
Qed.

Theorem paco15_2_0_unfold: forall (MON: monotone15_2 gf_0) (MON: monotone15_2 gf_1) r_0 r_1,
  paco15_2_0 gf_0 gf_1 r_0 r_1 <15= gf_0 (upaco15_2_0 gf_0 gf_1 r_0 r_1) (upaco15_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  repeat_intros 2. eapply _paco15_2_0_unfold; apply monotone15_2_eq; assumption.
Qed.

Theorem paco15_2_1_unfold: forall (MON: monotone15_2 gf_0) (MON: monotone15_2 gf_1) r_0 r_1,
  paco15_2_1 gf_0 gf_1 r_0 r_1 <15= gf_1 (upaco15_2_0 gf_0 gf_1 r_0 r_1) (upaco15_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  repeat_intros 2. eapply _paco15_2_1_unfold; apply monotone15_2_eq; assumption.
Qed.

End Arg15_2.

Arguments paco15_2_0_acc : clear implicits.
Arguments paco15_2_1_acc : clear implicits.
Arguments paco15_2_0_mon : clear implicits.
Arguments paco15_2_1_mon : clear implicits.
Arguments upaco15_2_0_mon : clear implicits.
Arguments upaco15_2_1_mon : clear implicits.
Arguments paco15_2_0_mult_strong : clear implicits.
Arguments paco15_2_1_mult_strong : clear implicits.
Arguments paco15_2_0_mult : clear implicits.
Arguments paco15_2_1_mult : clear implicits.
Arguments paco15_2_0_fold : clear implicits.
Arguments paco15_2_1_fold : clear implicits.
Arguments paco15_2_0_unfold : clear implicits.
Arguments paco15_2_1_unfold : clear implicits.

Global Instance paco15_2_0_inst  (gf_0 gf_1 : rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14->_) r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : paco_class (paco15_2_0 gf_0 gf_1 r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14) :=
{ pacoacc    := paco15_2_0_acc gf_0 gf_1;
  pacomult   := paco15_2_0_mult gf_0 gf_1;
  pacofold   := paco15_2_0_fold gf_0 gf_1;
  pacounfold := paco15_2_0_unfold gf_0 gf_1 }.

Global Instance paco15_2_1_inst  (gf_0 gf_1 : rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14->_) r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : paco_class (paco15_2_1 gf_0 gf_1 r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14) :=
{ pacoacc    := paco15_2_1_acc gf_0 gf_1;
  pacomult   := paco15_2_1_mult gf_0 gf_1;
  pacofold   := paco15_2_1_fold gf_0 gf_1;
  pacounfold := paco15_2_1_unfold gf_0 gf_1 }.

(** 3 Mutual Coinduction *)

Section Arg15_3.

Definition monotone15_3 (gf: rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 -> rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 -> rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 -> rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14) :=
  forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 r_0 r_1 r_2 r'_0 r'_1 r'_2 (IN: gf r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14) (LE_0: r_0 <15= r'_0)(LE_1: r_1 <15= r'_1)(LE_2: r_2 <15= r'_2), gf r'_0 r'_1 r'_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14.

Definition _monotone15_3 (gf: rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 -> rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 -> rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 -> rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14) :=
  forall r_0 r_1 r_2 r'_0 r'_1 r'_2(LE_0: r_0 <15= r'_0)(LE_1: r_1 <15= r'_1)(LE_2: r_2 <15= r'_2), gf r_0 r_1 r_2 <15== gf r'_0 r'_1 r'_2.

Lemma monotone15_3_eq (gf: rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 -> rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 -> rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 -> rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14) :
  monotone15_3 gf <-> _monotone15_3 gf.
Proof. unfold monotone15_3, _monotone15_3, le15. split; intros; eapply H; eassumption. Qed.

Lemma monotone15_3_map (gf: rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 -> rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 -> rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 -> rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14)
      (MON: _monotone15_3 gf) :
  _monotone_3 (fun R0 R1 R2 => uncurry15 (gf (curry15 R0) (curry15 R1) (curry15 R2))).
Proof.
  repeat_intros 9. apply uncurry_map15. apply MON; apply curry_map15; assumption.
Qed.

Variable gf_0 gf_1 gf_2 : rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 -> rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 -> rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 -> rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.
Arguments gf_2 : clear implicits.

Theorem _paco15_3_0_mon: _monotone15_3 (paco15_3_0 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 9. eapply curry_map15, _paco_3_0_mon; apply uncurry_map15; assumption.
Qed.

Theorem _paco15_3_1_mon: _monotone15_3 (paco15_3_1 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 9. eapply curry_map15, _paco_3_1_mon; apply uncurry_map15; assumption.
Qed.

Theorem _paco15_3_2_mon: _monotone15_3 (paco15_3_2 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 9. eapply curry_map15, _paco_3_2_mon; apply uncurry_map15; assumption.
Qed.

Theorem _paco15_3_0_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_0 <15== rr) (CIH: l <15== rr), l <15== paco15_3_0 gf_0 gf_1 gf_2 rr r_1 r_2),
  l <15== paco15_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_15.
  eapply _paco_3_0_acc. intros.
  apply uncurry_adjoint1_15 in INC. apply uncurry_adjoint1_15 in CIH.
  apply uncurry_adjoint2_15.
  eapply le15_trans. eapply (OBG _ INC CIH).
  apply curry_map15.
  apply _paco_3_0_mon; try apply le1_refl; apply curry_bij1_15.
Qed.

Theorem _paco15_3_1_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_1 <15== rr) (CIH: l <15== rr), l <15== paco15_3_1 gf_0 gf_1 gf_2 r_0 rr r_2),
  l <15== paco15_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_15.
  eapply _paco_3_1_acc. intros.
  apply uncurry_adjoint1_15 in INC. apply uncurry_adjoint1_15 in CIH.
  apply uncurry_adjoint2_15.
  eapply le15_trans. eapply (OBG _ INC CIH).
  apply curry_map15.
  apply _paco_3_1_mon; try apply le1_refl; apply curry_bij1_15.
Qed.

Theorem _paco15_3_2_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_2 <15== rr) (CIH: l <15== rr), l <15== paco15_3_2 gf_0 gf_1 gf_2 r_0 r_1 rr),
  l <15== paco15_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_15.
  eapply _paco_3_2_acc. intros.
  apply uncurry_adjoint1_15 in INC. apply uncurry_adjoint1_15 in CIH.
  apply uncurry_adjoint2_15.
  eapply le15_trans. eapply (OBG _ INC CIH).
  apply curry_map15.
  apply _paco_3_2_mon; try apply le1_refl; apply curry_bij1_15.
Qed.

Theorem _paco15_3_0_mult_strong: forall r_0 r_1 r_2,
  paco15_3_0 gf_0 gf_1 gf_2 (upaco15_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco15_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco15_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <15== paco15_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply curry_map15.
  eapply le1_trans; [| eapply _paco_3_0_mult_strong].
  apply _paco_3_0_mon; intros []; intros H; apply H.
Qed.

Theorem _paco15_3_1_mult_strong: forall r_0 r_1 r_2,
  paco15_3_1 gf_0 gf_1 gf_2 (upaco15_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco15_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco15_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <15== paco15_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply curry_map15.
  eapply le1_trans; [| eapply _paco_3_1_mult_strong].
  apply _paco_3_1_mon; intros []; intros H; apply H.
Qed.

Theorem _paco15_3_2_mult_strong: forall r_0 r_1 r_2,
  paco15_3_2 gf_0 gf_1 gf_2 (upaco15_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco15_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco15_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <15== paco15_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply curry_map15.
  eapply le1_trans; [| eapply _paco_3_2_mult_strong].
  apply _paco_3_2_mon; intros []; intros H; apply H.
Qed.

Theorem _paco15_3_0_fold: forall r_0 r_1 r_2,
  gf_0 (upaco15_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco15_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco15_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <15== paco15_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_15.
  eapply le1_trans; [| apply _paco_3_0_fold]. apply le1_refl.
Qed.

Theorem _paco15_3_1_fold: forall r_0 r_1 r_2,
  gf_1 (upaco15_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco15_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco15_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <15== paco15_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_15.
  eapply le1_trans; [| apply _paco_3_1_fold]. apply le1_refl.
Qed.

Theorem _paco15_3_2_fold: forall r_0 r_1 r_2,
  gf_2 (upaco15_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco15_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco15_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <15== paco15_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_15.
  eapply le1_trans; [| apply _paco_3_2_fold]. apply le1_refl.
Qed.

Theorem _paco15_3_0_unfold: forall (MON: _monotone15_3 gf_0) (MON: _monotone15_3 gf_1) (MON: _monotone15_3 gf_2) r_0 r_1 r_2,
  paco15_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 <15== gf_0 (upaco15_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco15_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco15_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  intros. apply curry_adjoint2_15.
  eapply _paco_3_0_unfold; apply monotone15_3_map; assumption.
Qed.

Theorem _paco15_3_1_unfold: forall (MON: _monotone15_3 gf_0) (MON: _monotone15_3 gf_1) (MON: _monotone15_3 gf_2) r_0 r_1 r_2,
  paco15_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 <15== gf_1 (upaco15_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco15_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco15_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  intros. apply curry_adjoint2_15.
  eapply _paco_3_1_unfold; apply monotone15_3_map; assumption.
Qed.

Theorem _paco15_3_2_unfold: forall (MON: _monotone15_3 gf_0) (MON: _monotone15_3 gf_1) (MON: _monotone15_3 gf_2) r_0 r_1 r_2,
  paco15_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 <15== gf_2 (upaco15_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco15_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco15_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  intros. apply curry_adjoint2_15.
  eapply _paco_3_2_unfold; apply monotone15_3_map; assumption.
Qed.

Theorem paco15_3_0_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_0 <15= rr) (CIH: l <15= rr), l <15= paco15_3_0 gf_0 gf_1 gf_2 rr r_1 r_2),
  l <15= paco15_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco15_3_0_acc.
Qed.

Theorem paco15_3_1_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_1 <15= rr) (CIH: l <15= rr), l <15= paco15_3_1 gf_0 gf_1 gf_2 r_0 rr r_2),
  l <15= paco15_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco15_3_1_acc.
Qed.

Theorem paco15_3_2_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_2 <15= rr) (CIH: l <15= rr), l <15= paco15_3_2 gf_0 gf_1 gf_2 r_0 r_1 rr),
  l <15= paco15_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco15_3_2_acc.
Qed.

Theorem paco15_3_0_mon: monotone15_3 (paco15_3_0 gf_0 gf_1 gf_2).
Proof.
  apply monotone15_3_eq.
  apply _paco15_3_0_mon.
Qed.

Theorem paco15_3_1_mon: monotone15_3 (paco15_3_1 gf_0 gf_1 gf_2).
Proof.
  apply monotone15_3_eq.
  apply _paco15_3_1_mon.
Qed.

Theorem paco15_3_2_mon: monotone15_3 (paco15_3_2 gf_0 gf_1 gf_2).
Proof.
  apply monotone15_3_eq.
  apply _paco15_3_2_mon.
Qed.

Theorem upaco15_3_0_mon: monotone15_3 (upaco15_3_0 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 21. intros R  LE0 LE1 LE2.
  destruct R.
  - left. eapply paco15_3_0_mon. apply H. apply LE0. apply LE1. apply LE2.
  - right. apply LE0, H.
Qed.
Theorem upaco15_3_1_mon: monotone15_3 (upaco15_3_1 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 21. intros R  LE0 LE1 LE2.
  destruct R.
  - left. eapply paco15_3_1_mon. apply H. apply LE0. apply LE1. apply LE2.
  - right. apply LE1, H.
Qed.
Theorem upaco15_3_2_mon: monotone15_3 (upaco15_3_2 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 21. intros R  LE0 LE1 LE2.
  destruct R.
  - left. eapply paco15_3_2_mon. apply H. apply LE0. apply LE1. apply LE2.
  - right. apply LE2, H.
Qed.
Theorem paco15_3_0_mult_strong: forall r_0 r_1 r_2,
  paco15_3_0 gf_0 gf_1 gf_2 (upaco15_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco15_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco15_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <15= paco15_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco15_3_0_mult_strong.
Qed.

Theorem paco15_3_1_mult_strong: forall r_0 r_1 r_2,
  paco15_3_1 gf_0 gf_1 gf_2 (upaco15_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco15_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco15_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <15= paco15_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco15_3_1_mult_strong.
Qed.

Theorem paco15_3_2_mult_strong: forall r_0 r_1 r_2,
  paco15_3_2 gf_0 gf_1 gf_2 (upaco15_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco15_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco15_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <15= paco15_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco15_3_2_mult_strong.
Qed.

Corollary paco15_3_0_mult: forall r_0 r_1 r_2,
  paco15_3_0 gf_0 gf_1 gf_2 (paco15_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco15_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco15_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <15= paco15_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco15_3_0_mult_strong, paco15_3_0_mon; [apply PR|..]; intros; left; assumption. Qed.

Corollary paco15_3_1_mult: forall r_0 r_1 r_2,
  paco15_3_1 gf_0 gf_1 gf_2 (paco15_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco15_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco15_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <15= paco15_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco15_3_1_mult_strong, paco15_3_1_mon; [apply PR|..]; intros; left; assumption. Qed.

Corollary paco15_3_2_mult: forall r_0 r_1 r_2,
  paco15_3_2 gf_0 gf_1 gf_2 (paco15_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco15_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco15_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <15= paco15_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco15_3_2_mult_strong, paco15_3_2_mon; [apply PR|..]; intros; left; assumption. Qed.

Theorem paco15_3_0_fold: forall r_0 r_1 r_2,
  gf_0 (upaco15_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco15_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco15_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <15= paco15_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco15_3_0_fold.
Qed.

Theorem paco15_3_1_fold: forall r_0 r_1 r_2,
  gf_1 (upaco15_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco15_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco15_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <15= paco15_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco15_3_1_fold.
Qed.

Theorem paco15_3_2_fold: forall r_0 r_1 r_2,
  gf_2 (upaco15_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco15_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco15_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <15= paco15_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco15_3_2_fold.
Qed.

Theorem paco15_3_0_unfold: forall (MON: monotone15_3 gf_0) (MON: monotone15_3 gf_1) (MON: monotone15_3 gf_2) r_0 r_1 r_2,
  paco15_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 <15= gf_0 (upaco15_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco15_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco15_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  repeat_intros 3. eapply _paco15_3_0_unfold; apply monotone15_3_eq; assumption.
Qed.

Theorem paco15_3_1_unfold: forall (MON: monotone15_3 gf_0) (MON: monotone15_3 gf_1) (MON: monotone15_3 gf_2) r_0 r_1 r_2,
  paco15_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 <15= gf_1 (upaco15_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco15_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco15_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  repeat_intros 3. eapply _paco15_3_1_unfold; apply monotone15_3_eq; assumption.
Qed.

Theorem paco15_3_2_unfold: forall (MON: monotone15_3 gf_0) (MON: monotone15_3 gf_1) (MON: monotone15_3 gf_2) r_0 r_1 r_2,
  paco15_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 <15= gf_2 (upaco15_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco15_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco15_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  repeat_intros 3. eapply _paco15_3_2_unfold; apply monotone15_3_eq; assumption.
Qed.

End Arg15_3.

Arguments paco15_3_0_acc : clear implicits.
Arguments paco15_3_1_acc : clear implicits.
Arguments paco15_3_2_acc : clear implicits.
Arguments paco15_3_0_mon : clear implicits.
Arguments paco15_3_1_mon : clear implicits.
Arguments paco15_3_2_mon : clear implicits.
Arguments upaco15_3_0_mon : clear implicits.
Arguments upaco15_3_1_mon : clear implicits.
Arguments upaco15_3_2_mon : clear implicits.
Arguments paco15_3_0_mult_strong : clear implicits.
Arguments paco15_3_1_mult_strong : clear implicits.
Arguments paco15_3_2_mult_strong : clear implicits.
Arguments paco15_3_0_mult : clear implicits.
Arguments paco15_3_1_mult : clear implicits.
Arguments paco15_3_2_mult : clear implicits.
Arguments paco15_3_0_fold : clear implicits.
Arguments paco15_3_1_fold : clear implicits.
Arguments paco15_3_2_fold : clear implicits.
Arguments paco15_3_0_unfold : clear implicits.
Arguments paco15_3_1_unfold : clear implicits.
Arguments paco15_3_2_unfold : clear implicits.

Global Instance paco15_3_0_inst  (gf_0 gf_1 gf_2 : rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : paco_class (paco15_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14) :=
{ pacoacc    := paco15_3_0_acc gf_0 gf_1 gf_2;
  pacomult   := paco15_3_0_mult gf_0 gf_1 gf_2;
  pacofold   := paco15_3_0_fold gf_0 gf_1 gf_2;
  pacounfold := paco15_3_0_unfold gf_0 gf_1 gf_2 }.

Global Instance paco15_3_1_inst  (gf_0 gf_1 gf_2 : rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : paco_class (paco15_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14) :=
{ pacoacc    := paco15_3_1_acc gf_0 gf_1 gf_2;
  pacomult   := paco15_3_1_mult gf_0 gf_1 gf_2;
  pacofold   := paco15_3_1_fold gf_0 gf_1 gf_2;
  pacounfold := paco15_3_1_unfold gf_0 gf_1 gf_2 }.

Global Instance paco15_3_2_inst  (gf_0 gf_1 gf_2 : rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : paco_class (paco15_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14) :=
{ pacoacc    := paco15_3_2_acc gf_0 gf_1 gf_2;
  pacomult   := paco15_3_2_mult gf_0 gf_1 gf_2;
  pacofold   := paco15_3_2_fold gf_0 gf_1 gf_2;
  pacounfold := paco15_3_2_unfold gf_0 gf_1 gf_2 }.

Lemma upaco15_clear gf x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14:
  upaco15 gf bot15 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 <-> paco15 gf bot15 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14.
Proof. split; intros; [destruct H;[apply H|destruct H]|left; apply H]. Qed.

End PACO15.

Global Opaque paco15.

Hint Unfold upaco15.
Hint Resolve paco15_fold.
Hint Unfold monotone15.

Global Opaque paco15_2_0.
Global Opaque paco15_2_1.

Hint Unfold upaco15_2_0.
Hint Unfold upaco15_2_1.
Hint Resolve paco15_2_0_fold.
Hint Resolve paco15_2_1_fold.
Hint Unfold monotone15_2.

Global Opaque paco15_3_0.
Global Opaque paco15_3_1.
Global Opaque paco15_3_2.

Hint Unfold upaco15_3_0.
Hint Unfold upaco15_3_1.
Hint Unfold upaco15_3_2.
Hint Resolve paco15_3_0_fold.
Hint Resolve paco15_3_1_fold.
Hint Resolve paco15_3_2_fold.
Hint Unfold monotone15_3.

