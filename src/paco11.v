Require Export paconotation pacotacuser.
Require Import paconotation_internal pacotac pacon.
Set Implicit Arguments.

Section PACO11.

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

Record sig11T :=
  exist11T { 
      proj11T0: @T0;
      proj11T1: @T1 proj11T0;
      proj11T2: @T2 proj11T0 proj11T1;
      proj11T3: @T3 proj11T0 proj11T1 proj11T2;
      proj11T4: @T4 proj11T0 proj11T1 proj11T2 proj11T3;
      proj11T5: @T5 proj11T0 proj11T1 proj11T2 proj11T3 proj11T4;
      proj11T6: @T6 proj11T0 proj11T1 proj11T2 proj11T3 proj11T4 proj11T5;
      proj11T7: @T7 proj11T0 proj11T1 proj11T2 proj11T3 proj11T4 proj11T5 proj11T6;
      proj11T8: @T8 proj11T0 proj11T1 proj11T2 proj11T3 proj11T4 proj11T5 proj11T6 proj11T7;
      proj11T9: @T9 proj11T0 proj11T1 proj11T2 proj11T3 proj11T4 proj11T5 proj11T6 proj11T7 proj11T8;
      proj11T10: @T10 proj11T0 proj11T1 proj11T2 proj11T3 proj11T4 proj11T5 proj11T6 proj11T7 proj11T8 proj11T9;
    }.

Definition uncurry11 (R: rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10): rel1 sig11T := fun x => R (proj11T0 x) (proj11T1 x) (proj11T2 x) (proj11T3 x) (proj11T4 x) (proj11T5 x) (proj11T6 x) (proj11T7 x) (proj11T8 x) (proj11T9 x) (proj11T10 x).

Definition curry11 (R: rel1 sig11T): rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 :=
  fun x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 => R (exist11T x10).

Lemma uncurry_map11 r0 r1 (LE : r0 <11== r1) : uncurry11 r0 <1== uncurry11 r1.
Proof. intros [] H. apply LE. apply H. Qed.

Lemma uncurry_map_rev11 r0 r1 (LE: uncurry11 r0 <1== uncurry11 r1) : r0 <11== r1.
Proof.
  repeat_intros 11. intros H. apply (LE (exist11T x10) H).
Qed.

Lemma curry_map11 r0 r1 (LE: r0 <1== r1) : curry11 r0 <11== curry11 r1.
Proof. 
  repeat_intros 11. intros H. apply (LE (exist11T x10) H).
Qed.

Lemma curry_map_rev11 r0 r1 (LE: curry11 r0 <11== curry11 r1) : r0 <1== r1.
Proof. 
  intros [] H. apply LE. apply H.
Qed.

Lemma uncurry_bij1_11 r : curry11 (uncurry11 r) <11== r.
Proof. unfold le11. repeat_intros 11. intros H. apply H. Qed.

Lemma uncurry_bij2_11 r : r <11== curry11 (uncurry11 r).
Proof. unfold le11. repeat_intros 11. intros H. apply H. Qed.

Lemma curry_bij1_11 r : uncurry11 (curry11 r) <1== r.
Proof. intros []. intro H. apply H. Qed.

Lemma curry_bij2_11 r : r <1== uncurry11 (curry11 r).
Proof. intros []. intro H. apply H. Qed.

Lemma uncurry_adjoint1_11 r0 r1 (LE: uncurry11 r0 <1== r1) : r0 <11== curry11 r1.
Proof.
  apply uncurry_map_rev11. eapply le1_trans; [apply LE|]. apply curry_bij2_11.
Qed.

Lemma uncurry_adjoint2_11 r0 r1 (LE: r0 <11== curry11 r1) : uncurry11 r0 <1== r1.
Proof.
  apply curry_map_rev11. eapply le11_trans; [|apply LE]. apply uncurry_bij2_11.
Qed.

Lemma curry_adjoint1_11 r0 r1 (LE: curry11 r0 <11== r1) : r0 <1== uncurry11 r1.
Proof.
  apply curry_map_rev11. eapply le11_trans; [apply LE|]. apply uncurry_bij2_11.
Qed.

Lemma curry_adjoint2_11 r0 r1 (LE: r0 <1== uncurry11 r1) : curry11 r0 <11== r1.
Proof.
  apply uncurry_map_rev11. eapply le1_trans; [|apply LE]. apply curry_bij1_11.
Qed.

(** ** Predicates of Arity 11
*)

Section Arg11_def.
Variable gf : rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10.
Arguments gf : clear implicits.

Definition paco11( r: rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10) : rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 :=
  curry11 (paco (fun R0 => uncurry11 (gf (curry11 R0))) (uncurry11 r)).

Definition upaco11( r: rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10) := paco11 r \11/ r.
End Arg11_def.
Arguments paco11 : clear implicits.
Arguments upaco11 : clear implicits.
Hint Unfold upaco11.

Section Arg11_2_def.
Variable gf_0 gf_1 : rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.

Definition paco11_2_0( r_0 r_1: rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10) : rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 :=
  curry11 (paco_2_0 (fun R0 R1 => uncurry11 (gf_0 (curry11 R0) (curry11 R1))) (fun R0 R1 => uncurry11 (gf_1 (curry11 R0) (curry11 R1))) (uncurry11 r_0) (uncurry11 r_1)).

Definition paco11_2_1( r_0 r_1: rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10) : rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 :=
  curry11 (paco_2_1 (fun R0 R1 => uncurry11 (gf_0 (curry11 R0) (curry11 R1))) (fun R0 R1 => uncurry11 (gf_1 (curry11 R0) (curry11 R1))) (uncurry11 r_0) (uncurry11 r_1)).

Definition upaco11_2_0( r_0 r_1: rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10) := paco11_2_0 r_0 r_1 \11/ r_0.
Definition upaco11_2_1( r_0 r_1: rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10) := paco11_2_1 r_0 r_1 \11/ r_1.
End Arg11_2_def.
Arguments paco11_2_0 : clear implicits.
Arguments upaco11_2_0 : clear implicits.
Hint Unfold upaco11_2_0.
Arguments paco11_2_1 : clear implicits.
Arguments upaco11_2_1 : clear implicits.
Hint Unfold upaco11_2_1.

Section Arg11_3_def.
Variable gf_0 gf_1 gf_2 : rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.
Arguments gf_2 : clear implicits.

Definition paco11_3_0( r_0 r_1 r_2: rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10) : rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 :=
  curry11 (paco_3_0 (fun R0 R1 R2 => uncurry11 (gf_0 (curry11 R0) (curry11 R1) (curry11 R2))) (fun R0 R1 R2 => uncurry11 (gf_1 (curry11 R0) (curry11 R1) (curry11 R2))) (fun R0 R1 R2 => uncurry11 (gf_2 (curry11 R0) (curry11 R1) (curry11 R2))) (uncurry11 r_0) (uncurry11 r_1) (uncurry11 r_2)).

Definition paco11_3_1( r_0 r_1 r_2: rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10) : rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 :=
  curry11 (paco_3_1 (fun R0 R1 R2 => uncurry11 (gf_0 (curry11 R0) (curry11 R1) (curry11 R2))) (fun R0 R1 R2 => uncurry11 (gf_1 (curry11 R0) (curry11 R1) (curry11 R2))) (fun R0 R1 R2 => uncurry11 (gf_2 (curry11 R0) (curry11 R1) (curry11 R2))) (uncurry11 r_0) (uncurry11 r_1) (uncurry11 r_2)).

Definition paco11_3_2( r_0 r_1 r_2: rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10) : rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 :=
  curry11 (paco_3_2 (fun R0 R1 R2 => uncurry11 (gf_0 (curry11 R0) (curry11 R1) (curry11 R2))) (fun R0 R1 R2 => uncurry11 (gf_1 (curry11 R0) (curry11 R1) (curry11 R2))) (fun R0 R1 R2 => uncurry11 (gf_2 (curry11 R0) (curry11 R1) (curry11 R2))) (uncurry11 r_0) (uncurry11 r_1) (uncurry11 r_2)).

Definition upaco11_3_0( r_0 r_1 r_2: rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10) := paco11_3_0 r_0 r_1 r_2 \11/ r_0.
Definition upaco11_3_1( r_0 r_1 r_2: rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10) := paco11_3_1 r_0 r_1 r_2 \11/ r_1.
Definition upaco11_3_2( r_0 r_1 r_2: rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10) := paco11_3_2 r_0 r_1 r_2 \11/ r_2.
End Arg11_3_def.
Arguments paco11_3_0 : clear implicits.
Arguments upaco11_3_0 : clear implicits.
Hint Unfold upaco11_3_0.
Arguments paco11_3_1 : clear implicits.
Arguments upaco11_3_1 : clear implicits.
Hint Unfold upaco11_3_1.
Arguments paco11_3_2 : clear implicits.
Arguments upaco11_3_2 : clear implicits.
Hint Unfold upaco11_3_2.

(** 1 Mutual Coinduction *)

Section Arg11_1.

Definition monotone11 (gf: rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10) :=
  forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 r r' (IN: gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) (LE: r <11= r'), gf r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10.

Definition _monotone11 (gf: rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10) :=
  forall r r'(LE: r <11= r'), gf r <11== gf r'.

Lemma monotone11_eq (gf: rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10) :
  monotone11 gf <-> _monotone11 gf.
Proof. unfold monotone11, _monotone11, le11. split; intros; eapply H; eassumption. Qed.

Lemma monotone11_map (gf: rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10)
      (MON: _monotone11 gf) :
  _monotone (fun R0 => uncurry11 (gf (curry11 R0))).
Proof.
  repeat_intros 3. apply uncurry_map11. apply MON; apply curry_map11; assumption.
Qed.

Variable gf : rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10.
Arguments gf : clear implicits.

Theorem _paco11_mon: _monotone11 (paco11 gf).
Proof.
  repeat_intros 3. eapply curry_map11, _paco_mon; apply uncurry_map11; assumption.
Qed.

Theorem _paco11_acc: forall
  l r (OBG: forall rr (INC: r <11== rr) (CIH: l <11== rr), l <11== paco11 gf rr),
  l <11== paco11 gf r.
Proof.
  intros. apply uncurry_adjoint1_11.
  eapply _paco_acc. intros.
  apply uncurry_adjoint1_11 in INC. apply uncurry_adjoint1_11 in CIH.
  apply uncurry_adjoint2_11.
  eapply le11_trans. eapply (OBG _ INC CIH).
  apply curry_map11.
  apply _paco_mon; try apply le1_refl; apply curry_bij1_11.
Qed.

Theorem _paco11_mult_strong: forall r,
  paco11 gf (upaco11 gf r) <11== paco11 gf r.
Proof.
  intros. apply curry_map11.
  eapply le1_trans; [| eapply _paco_mult_strong].
  apply _paco_mon; intros []; intros H; apply H.
Qed.

Theorem _paco11_fold: forall r,
  gf (upaco11 gf r) <11== paco11 gf r.
Proof.
  intros. apply uncurry_adjoint1_11.
  eapply le1_trans; [| apply _paco_fold]. apply le1_refl.
Qed.

Theorem _paco11_unfold: forall (MON: _monotone11 gf) r,
  paco11 gf r <11== gf (upaco11 gf r).
Proof.
  intros. apply curry_adjoint2_11.
  eapply _paco_unfold; apply monotone11_map; assumption.
Qed.

Theorem paco11_acc: forall
  l r (OBG: forall rr (INC: r <11= rr) (CIH: l <11= rr), l <11= paco11 gf rr),
  l <11= paco11 gf r.
Proof.
  apply _paco11_acc.
Qed.

Theorem paco11_mon: monotone11 (paco11 gf).
Proof.
  apply monotone11_eq.
  apply _paco11_mon.
Qed.

Theorem upaco11_mon: monotone11 (upaco11 gf).
Proof.
  repeat_intros 13. intros R  LE0.
  destruct R.
  - left. eapply paco11_mon. apply H. apply LE0.
  - right. apply LE0, H.
Qed.
Theorem paco11_mult_strong: forall r,
  paco11 gf (upaco11 gf r) <11= paco11 gf r.
Proof.
  apply _paco11_mult_strong.
Qed.

Corollary paco11_mult: forall r,
  paco11 gf (paco11 gf r) <11= paco11 gf r.
Proof. intros; eapply paco11_mult_strong, paco11_mon; [apply PR|..]; intros; left; assumption. Qed.

Theorem paco11_fold: forall r,
  gf (upaco11 gf r) <11= paco11 gf r.
Proof.
  apply _paco11_fold.
Qed.

Theorem paco11_unfold: forall (MON: monotone11 gf) r,
  paco11 gf r <11= gf (upaco11 gf r).
Proof.
  repeat_intros 1. eapply _paco11_unfold; apply monotone11_eq; assumption.
Qed.

End Arg11_1.

Arguments paco11_acc : clear implicits.
Arguments paco11_mon : clear implicits.
Arguments upaco11_mon : clear implicits.
Arguments paco11_mult_strong : clear implicits.
Arguments paco11_mult : clear implicits.
Arguments paco11_fold : clear implicits.
Arguments paco11_unfold : clear implicits.

Global Instance paco11_inst  (gf : rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10->_) r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : paco_class (paco11 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) :=
{ pacoacc    := paco11_acc gf;
  pacomult   := paco11_mult gf;
  pacofold   := paco11_fold gf;
  pacounfold := paco11_unfold gf }.

(** 2 Mutual Coinduction *)

Section Arg11_2.

Definition monotone11_2 (gf: rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10) :=
  forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 r_0 r_1 r'_0 r'_1 (IN: gf r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) (LE_0: r_0 <11= r'_0)(LE_1: r_1 <11= r'_1), gf r'_0 r'_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10.

Definition _monotone11_2 (gf: rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10) :=
  forall r_0 r_1 r'_0 r'_1(LE_0: r_0 <11= r'_0)(LE_1: r_1 <11= r'_1), gf r_0 r_1 <11== gf r'_0 r'_1.

Lemma monotone11_2_eq (gf: rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10) :
  monotone11_2 gf <-> _monotone11_2 gf.
Proof. unfold monotone11_2, _monotone11_2, le11. split; intros; eapply H; eassumption. Qed.

Lemma monotone11_2_map (gf: rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10)
      (MON: _monotone11_2 gf) :
  _monotone_2 (fun R0 R1 => uncurry11 (gf (curry11 R0) (curry11 R1))).
Proof.
  repeat_intros 6. apply uncurry_map11. apply MON; apply curry_map11; assumption.
Qed.

Variable gf_0 gf_1 : rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.

Theorem _paco11_2_0_mon: _monotone11_2 (paco11_2_0 gf_0 gf_1).
Proof.
  repeat_intros 6. eapply curry_map11, _paco_2_0_mon; apply uncurry_map11; assumption.
Qed.

Theorem _paco11_2_1_mon: _monotone11_2 (paco11_2_1 gf_0 gf_1).
Proof.
  repeat_intros 6. eapply curry_map11, _paco_2_1_mon; apply uncurry_map11; assumption.
Qed.

Theorem _paco11_2_0_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_0 <11== rr) (CIH: l <11== rr), l <11== paco11_2_0 gf_0 gf_1 rr r_1),
  l <11== paco11_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_11.
  eapply _paco_2_0_acc. intros.
  apply uncurry_adjoint1_11 in INC. apply uncurry_adjoint1_11 in CIH.
  apply uncurry_adjoint2_11.
  eapply le11_trans. eapply (OBG _ INC CIH).
  apply curry_map11.
  apply _paco_2_0_mon; try apply le1_refl; apply curry_bij1_11.
Qed.

Theorem _paco11_2_1_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_1 <11== rr) (CIH: l <11== rr), l <11== paco11_2_1 gf_0 gf_1 r_0 rr),
  l <11== paco11_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_11.
  eapply _paco_2_1_acc. intros.
  apply uncurry_adjoint1_11 in INC. apply uncurry_adjoint1_11 in CIH.
  apply uncurry_adjoint2_11.
  eapply le11_trans. eapply (OBG _ INC CIH).
  apply curry_map11.
  apply _paco_2_1_mon; try apply le1_refl; apply curry_bij1_11.
Qed.

Theorem _paco11_2_0_mult_strong: forall r_0 r_1,
  paco11_2_0 gf_0 gf_1 (upaco11_2_0 gf_0 gf_1 r_0 r_1) (upaco11_2_1 gf_0 gf_1 r_0 r_1) <11== paco11_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply curry_map11.
  eapply le1_trans; [| eapply _paco_2_0_mult_strong].
  apply _paco_2_0_mon; intros []; intros H; apply H.
Qed.

Theorem _paco11_2_1_mult_strong: forall r_0 r_1,
  paco11_2_1 gf_0 gf_1 (upaco11_2_0 gf_0 gf_1 r_0 r_1) (upaco11_2_1 gf_0 gf_1 r_0 r_1) <11== paco11_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply curry_map11.
  eapply le1_trans; [| eapply _paco_2_1_mult_strong].
  apply _paco_2_1_mon; intros []; intros H; apply H.
Qed.

Theorem _paco11_2_0_fold: forall r_0 r_1,
  gf_0 (upaco11_2_0 gf_0 gf_1 r_0 r_1) (upaco11_2_1 gf_0 gf_1 r_0 r_1) <11== paco11_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_11.
  eapply le1_trans; [| apply _paco_2_0_fold]. apply le1_refl.
Qed.

Theorem _paco11_2_1_fold: forall r_0 r_1,
  gf_1 (upaco11_2_0 gf_0 gf_1 r_0 r_1) (upaco11_2_1 gf_0 gf_1 r_0 r_1) <11== paco11_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_11.
  eapply le1_trans; [| apply _paco_2_1_fold]. apply le1_refl.
Qed.

Theorem _paco11_2_0_unfold: forall (MON: _monotone11_2 gf_0) (MON: _monotone11_2 gf_1) r_0 r_1,
  paco11_2_0 gf_0 gf_1 r_0 r_1 <11== gf_0 (upaco11_2_0 gf_0 gf_1 r_0 r_1) (upaco11_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  intros. apply curry_adjoint2_11.
  eapply _paco_2_0_unfold; apply monotone11_2_map; assumption.
Qed.

Theorem _paco11_2_1_unfold: forall (MON: _monotone11_2 gf_0) (MON: _monotone11_2 gf_1) r_0 r_1,
  paco11_2_1 gf_0 gf_1 r_0 r_1 <11== gf_1 (upaco11_2_0 gf_0 gf_1 r_0 r_1) (upaco11_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  intros. apply curry_adjoint2_11.
  eapply _paco_2_1_unfold; apply monotone11_2_map; assumption.
Qed.

Theorem paco11_2_0_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_0 <11= rr) (CIH: l <11= rr), l <11= paco11_2_0 gf_0 gf_1 rr r_1),
  l <11= paco11_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco11_2_0_acc.
Qed.

Theorem paco11_2_1_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_1 <11= rr) (CIH: l <11= rr), l <11= paco11_2_1 gf_0 gf_1 r_0 rr),
  l <11= paco11_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco11_2_1_acc.
Qed.

Theorem paco11_2_0_mon: monotone11_2 (paco11_2_0 gf_0 gf_1).
Proof.
  apply monotone11_2_eq.
  apply _paco11_2_0_mon.
Qed.

Theorem paco11_2_1_mon: monotone11_2 (paco11_2_1 gf_0 gf_1).
Proof.
  apply monotone11_2_eq.
  apply _paco11_2_1_mon.
Qed.

Theorem upaco11_2_0_mon: monotone11_2 (upaco11_2_0 gf_0 gf_1).
Proof.
  repeat_intros 15. intros R  LE0 LE1.
  destruct R.
  - left. eapply paco11_2_0_mon. apply H. apply LE0. apply LE1.
  - right. apply LE0, H.
Qed.
Theorem upaco11_2_1_mon: monotone11_2 (upaco11_2_1 gf_0 gf_1).
Proof.
  repeat_intros 15. intros R  LE0 LE1.
  destruct R.
  - left. eapply paco11_2_1_mon. apply H. apply LE0. apply LE1.
  - right. apply LE1, H.
Qed.
Theorem paco11_2_0_mult_strong: forall r_0 r_1,
  paco11_2_0 gf_0 gf_1 (upaco11_2_0 gf_0 gf_1 r_0 r_1) (upaco11_2_1 gf_0 gf_1 r_0 r_1) <11= paco11_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco11_2_0_mult_strong.
Qed.

Theorem paco11_2_1_mult_strong: forall r_0 r_1,
  paco11_2_1 gf_0 gf_1 (upaco11_2_0 gf_0 gf_1 r_0 r_1) (upaco11_2_1 gf_0 gf_1 r_0 r_1) <11= paco11_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco11_2_1_mult_strong.
Qed.

Corollary paco11_2_0_mult: forall r_0 r_1,
  paco11_2_0 gf_0 gf_1 (paco11_2_0 gf_0 gf_1 r_0 r_1) (paco11_2_1 gf_0 gf_1 r_0 r_1) <11= paco11_2_0 gf_0 gf_1 r_0 r_1.
Proof. intros; eapply paco11_2_0_mult_strong, paco11_2_0_mon; [apply PR|..]; intros; left; assumption. Qed.

Corollary paco11_2_1_mult: forall r_0 r_1,
  paco11_2_1 gf_0 gf_1 (paco11_2_0 gf_0 gf_1 r_0 r_1) (paco11_2_1 gf_0 gf_1 r_0 r_1) <11= paco11_2_1 gf_0 gf_1 r_0 r_1.
Proof. intros; eapply paco11_2_1_mult_strong, paco11_2_1_mon; [apply PR|..]; intros; left; assumption. Qed.

Theorem paco11_2_0_fold: forall r_0 r_1,
  gf_0 (upaco11_2_0 gf_0 gf_1 r_0 r_1) (upaco11_2_1 gf_0 gf_1 r_0 r_1) <11= paco11_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco11_2_0_fold.
Qed.

Theorem paco11_2_1_fold: forall r_0 r_1,
  gf_1 (upaco11_2_0 gf_0 gf_1 r_0 r_1) (upaco11_2_1 gf_0 gf_1 r_0 r_1) <11= paco11_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco11_2_1_fold.
Qed.

Theorem paco11_2_0_unfold: forall (MON: monotone11_2 gf_0) (MON: monotone11_2 gf_1) r_0 r_1,
  paco11_2_0 gf_0 gf_1 r_0 r_1 <11= gf_0 (upaco11_2_0 gf_0 gf_1 r_0 r_1) (upaco11_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  repeat_intros 2. eapply _paco11_2_0_unfold; apply monotone11_2_eq; assumption.
Qed.

Theorem paco11_2_1_unfold: forall (MON: monotone11_2 gf_0) (MON: monotone11_2 gf_1) r_0 r_1,
  paco11_2_1 gf_0 gf_1 r_0 r_1 <11= gf_1 (upaco11_2_0 gf_0 gf_1 r_0 r_1) (upaco11_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  repeat_intros 2. eapply _paco11_2_1_unfold; apply monotone11_2_eq; assumption.
Qed.

End Arg11_2.

Arguments paco11_2_0_acc : clear implicits.
Arguments paco11_2_1_acc : clear implicits.
Arguments paco11_2_0_mon : clear implicits.
Arguments paco11_2_1_mon : clear implicits.
Arguments upaco11_2_0_mon : clear implicits.
Arguments upaco11_2_1_mon : clear implicits.
Arguments paco11_2_0_mult_strong : clear implicits.
Arguments paco11_2_1_mult_strong : clear implicits.
Arguments paco11_2_0_mult : clear implicits.
Arguments paco11_2_1_mult : clear implicits.
Arguments paco11_2_0_fold : clear implicits.
Arguments paco11_2_1_fold : clear implicits.
Arguments paco11_2_0_unfold : clear implicits.
Arguments paco11_2_1_unfold : clear implicits.

Global Instance paco11_2_0_inst  (gf_0 gf_1 : rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10->_) r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : paco_class (paco11_2_0 gf_0 gf_1 r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) :=
{ pacoacc    := paco11_2_0_acc gf_0 gf_1;
  pacomult   := paco11_2_0_mult gf_0 gf_1;
  pacofold   := paco11_2_0_fold gf_0 gf_1;
  pacounfold := paco11_2_0_unfold gf_0 gf_1 }.

Global Instance paco11_2_1_inst  (gf_0 gf_1 : rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10->_) r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : paco_class (paco11_2_1 gf_0 gf_1 r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) :=
{ pacoacc    := paco11_2_1_acc gf_0 gf_1;
  pacomult   := paco11_2_1_mult gf_0 gf_1;
  pacofold   := paco11_2_1_fold gf_0 gf_1;
  pacounfold := paco11_2_1_unfold gf_0 gf_1 }.

(** 3 Mutual Coinduction *)

Section Arg11_3.

Definition monotone11_3 (gf: rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10) :=
  forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 r_0 r_1 r_2 r'_0 r'_1 r'_2 (IN: gf r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) (LE_0: r_0 <11= r'_0)(LE_1: r_1 <11= r'_1)(LE_2: r_2 <11= r'_2), gf r'_0 r'_1 r'_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10.

Definition _monotone11_3 (gf: rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10) :=
  forall r_0 r_1 r_2 r'_0 r'_1 r'_2(LE_0: r_0 <11= r'_0)(LE_1: r_1 <11= r'_1)(LE_2: r_2 <11= r'_2), gf r_0 r_1 r_2 <11== gf r'_0 r'_1 r'_2.

Lemma monotone11_3_eq (gf: rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10) :
  monotone11_3 gf <-> _monotone11_3 gf.
Proof. unfold monotone11_3, _monotone11_3, le11. split; intros; eapply H; eassumption. Qed.

Lemma monotone11_3_map (gf: rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10)
      (MON: _monotone11_3 gf) :
  _monotone_3 (fun R0 R1 R2 => uncurry11 (gf (curry11 R0) (curry11 R1) (curry11 R2))).
Proof.
  repeat_intros 9. apply uncurry_map11. apply MON; apply curry_map11; assumption.
Qed.

Variable gf_0 gf_1 gf_2 : rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.
Arguments gf_2 : clear implicits.

Theorem _paco11_3_0_mon: _monotone11_3 (paco11_3_0 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 9. eapply curry_map11, _paco_3_0_mon; apply uncurry_map11; assumption.
Qed.

Theorem _paco11_3_1_mon: _monotone11_3 (paco11_3_1 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 9. eapply curry_map11, _paco_3_1_mon; apply uncurry_map11; assumption.
Qed.

Theorem _paco11_3_2_mon: _monotone11_3 (paco11_3_2 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 9. eapply curry_map11, _paco_3_2_mon; apply uncurry_map11; assumption.
Qed.

Theorem _paco11_3_0_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_0 <11== rr) (CIH: l <11== rr), l <11== paco11_3_0 gf_0 gf_1 gf_2 rr r_1 r_2),
  l <11== paco11_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_11.
  eapply _paco_3_0_acc. intros.
  apply uncurry_adjoint1_11 in INC. apply uncurry_adjoint1_11 in CIH.
  apply uncurry_adjoint2_11.
  eapply le11_trans. eapply (OBG _ INC CIH).
  apply curry_map11.
  apply _paco_3_0_mon; try apply le1_refl; apply curry_bij1_11.
Qed.

Theorem _paco11_3_1_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_1 <11== rr) (CIH: l <11== rr), l <11== paco11_3_1 gf_0 gf_1 gf_2 r_0 rr r_2),
  l <11== paco11_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_11.
  eapply _paco_3_1_acc. intros.
  apply uncurry_adjoint1_11 in INC. apply uncurry_adjoint1_11 in CIH.
  apply uncurry_adjoint2_11.
  eapply le11_trans. eapply (OBG _ INC CIH).
  apply curry_map11.
  apply _paco_3_1_mon; try apply le1_refl; apply curry_bij1_11.
Qed.

Theorem _paco11_3_2_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_2 <11== rr) (CIH: l <11== rr), l <11== paco11_3_2 gf_0 gf_1 gf_2 r_0 r_1 rr),
  l <11== paco11_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_11.
  eapply _paco_3_2_acc. intros.
  apply uncurry_adjoint1_11 in INC. apply uncurry_adjoint1_11 in CIH.
  apply uncurry_adjoint2_11.
  eapply le11_trans. eapply (OBG _ INC CIH).
  apply curry_map11.
  apply _paco_3_2_mon; try apply le1_refl; apply curry_bij1_11.
Qed.

Theorem _paco11_3_0_mult_strong: forall r_0 r_1 r_2,
  paco11_3_0 gf_0 gf_1 gf_2 (upaco11_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco11_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco11_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <11== paco11_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply curry_map11.
  eapply le1_trans; [| eapply _paco_3_0_mult_strong].
  apply _paco_3_0_mon; intros []; intros H; apply H.
Qed.

Theorem _paco11_3_1_mult_strong: forall r_0 r_1 r_2,
  paco11_3_1 gf_0 gf_1 gf_2 (upaco11_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco11_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco11_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <11== paco11_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply curry_map11.
  eapply le1_trans; [| eapply _paco_3_1_mult_strong].
  apply _paco_3_1_mon; intros []; intros H; apply H.
Qed.

Theorem _paco11_3_2_mult_strong: forall r_0 r_1 r_2,
  paco11_3_2 gf_0 gf_1 gf_2 (upaco11_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco11_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco11_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <11== paco11_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply curry_map11.
  eapply le1_trans; [| eapply _paco_3_2_mult_strong].
  apply _paco_3_2_mon; intros []; intros H; apply H.
Qed.

Theorem _paco11_3_0_fold: forall r_0 r_1 r_2,
  gf_0 (upaco11_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco11_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco11_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <11== paco11_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_11.
  eapply le1_trans; [| apply _paco_3_0_fold]. apply le1_refl.
Qed.

Theorem _paco11_3_1_fold: forall r_0 r_1 r_2,
  gf_1 (upaco11_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco11_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco11_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <11== paco11_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_11.
  eapply le1_trans; [| apply _paco_3_1_fold]. apply le1_refl.
Qed.

Theorem _paco11_3_2_fold: forall r_0 r_1 r_2,
  gf_2 (upaco11_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco11_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco11_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <11== paco11_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_11.
  eapply le1_trans; [| apply _paco_3_2_fold]. apply le1_refl.
Qed.

Theorem _paco11_3_0_unfold: forall (MON: _monotone11_3 gf_0) (MON: _monotone11_3 gf_1) (MON: _monotone11_3 gf_2) r_0 r_1 r_2,
  paco11_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 <11== gf_0 (upaco11_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco11_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco11_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  intros. apply curry_adjoint2_11.
  eapply _paco_3_0_unfold; apply monotone11_3_map; assumption.
Qed.

Theorem _paco11_3_1_unfold: forall (MON: _monotone11_3 gf_0) (MON: _monotone11_3 gf_1) (MON: _monotone11_3 gf_2) r_0 r_1 r_2,
  paco11_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 <11== gf_1 (upaco11_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco11_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco11_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  intros. apply curry_adjoint2_11.
  eapply _paco_3_1_unfold; apply monotone11_3_map; assumption.
Qed.

Theorem _paco11_3_2_unfold: forall (MON: _monotone11_3 gf_0) (MON: _monotone11_3 gf_1) (MON: _monotone11_3 gf_2) r_0 r_1 r_2,
  paco11_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 <11== gf_2 (upaco11_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco11_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco11_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  intros. apply curry_adjoint2_11.
  eapply _paco_3_2_unfold; apply monotone11_3_map; assumption.
Qed.

Theorem paco11_3_0_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_0 <11= rr) (CIH: l <11= rr), l <11= paco11_3_0 gf_0 gf_1 gf_2 rr r_1 r_2),
  l <11= paco11_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco11_3_0_acc.
Qed.

Theorem paco11_3_1_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_1 <11= rr) (CIH: l <11= rr), l <11= paco11_3_1 gf_0 gf_1 gf_2 r_0 rr r_2),
  l <11= paco11_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco11_3_1_acc.
Qed.

Theorem paco11_3_2_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_2 <11= rr) (CIH: l <11= rr), l <11= paco11_3_2 gf_0 gf_1 gf_2 r_0 r_1 rr),
  l <11= paco11_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco11_3_2_acc.
Qed.

Theorem paco11_3_0_mon: monotone11_3 (paco11_3_0 gf_0 gf_1 gf_2).
Proof.
  apply monotone11_3_eq.
  apply _paco11_3_0_mon.
Qed.

Theorem paco11_3_1_mon: monotone11_3 (paco11_3_1 gf_0 gf_1 gf_2).
Proof.
  apply monotone11_3_eq.
  apply _paco11_3_1_mon.
Qed.

Theorem paco11_3_2_mon: monotone11_3 (paco11_3_2 gf_0 gf_1 gf_2).
Proof.
  apply monotone11_3_eq.
  apply _paco11_3_2_mon.
Qed.

Theorem upaco11_3_0_mon: monotone11_3 (upaco11_3_0 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 17. intros R  LE0 LE1 LE2.
  destruct R.
  - left. eapply paco11_3_0_mon. apply H. apply LE0. apply LE1. apply LE2.
  - right. apply LE0, H.
Qed.
Theorem upaco11_3_1_mon: monotone11_3 (upaco11_3_1 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 17. intros R  LE0 LE1 LE2.
  destruct R.
  - left. eapply paco11_3_1_mon. apply H. apply LE0. apply LE1. apply LE2.
  - right. apply LE1, H.
Qed.
Theorem upaco11_3_2_mon: monotone11_3 (upaco11_3_2 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 17. intros R  LE0 LE1 LE2.
  destruct R.
  - left. eapply paco11_3_2_mon. apply H. apply LE0. apply LE1. apply LE2.
  - right. apply LE2, H.
Qed.
Theorem paco11_3_0_mult_strong: forall r_0 r_1 r_2,
  paco11_3_0 gf_0 gf_1 gf_2 (upaco11_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco11_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco11_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <11= paco11_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco11_3_0_mult_strong.
Qed.

Theorem paco11_3_1_mult_strong: forall r_0 r_1 r_2,
  paco11_3_1 gf_0 gf_1 gf_2 (upaco11_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco11_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco11_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <11= paco11_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco11_3_1_mult_strong.
Qed.

Theorem paco11_3_2_mult_strong: forall r_0 r_1 r_2,
  paco11_3_2 gf_0 gf_1 gf_2 (upaco11_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco11_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco11_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <11= paco11_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco11_3_2_mult_strong.
Qed.

Corollary paco11_3_0_mult: forall r_0 r_1 r_2,
  paco11_3_0 gf_0 gf_1 gf_2 (paco11_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco11_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco11_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <11= paco11_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco11_3_0_mult_strong, paco11_3_0_mon; [apply PR|..]; intros; left; assumption. Qed.

Corollary paco11_3_1_mult: forall r_0 r_1 r_2,
  paco11_3_1 gf_0 gf_1 gf_2 (paco11_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco11_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco11_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <11= paco11_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco11_3_1_mult_strong, paco11_3_1_mon; [apply PR|..]; intros; left; assumption. Qed.

Corollary paco11_3_2_mult: forall r_0 r_1 r_2,
  paco11_3_2 gf_0 gf_1 gf_2 (paco11_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco11_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco11_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <11= paco11_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco11_3_2_mult_strong, paco11_3_2_mon; [apply PR|..]; intros; left; assumption. Qed.

Theorem paco11_3_0_fold: forall r_0 r_1 r_2,
  gf_0 (upaco11_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco11_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco11_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <11= paco11_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco11_3_0_fold.
Qed.

Theorem paco11_3_1_fold: forall r_0 r_1 r_2,
  gf_1 (upaco11_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco11_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco11_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <11= paco11_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco11_3_1_fold.
Qed.

Theorem paco11_3_2_fold: forall r_0 r_1 r_2,
  gf_2 (upaco11_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco11_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco11_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <11= paco11_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco11_3_2_fold.
Qed.

Theorem paco11_3_0_unfold: forall (MON: monotone11_3 gf_0) (MON: monotone11_3 gf_1) (MON: monotone11_3 gf_2) r_0 r_1 r_2,
  paco11_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 <11= gf_0 (upaco11_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco11_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco11_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  repeat_intros 3. eapply _paco11_3_0_unfold; apply monotone11_3_eq; assumption.
Qed.

Theorem paco11_3_1_unfold: forall (MON: monotone11_3 gf_0) (MON: monotone11_3 gf_1) (MON: monotone11_3 gf_2) r_0 r_1 r_2,
  paco11_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 <11= gf_1 (upaco11_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco11_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco11_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  repeat_intros 3. eapply _paco11_3_1_unfold; apply monotone11_3_eq; assumption.
Qed.

Theorem paco11_3_2_unfold: forall (MON: monotone11_3 gf_0) (MON: monotone11_3 gf_1) (MON: monotone11_3 gf_2) r_0 r_1 r_2,
  paco11_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 <11= gf_2 (upaco11_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco11_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco11_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  repeat_intros 3. eapply _paco11_3_2_unfold; apply monotone11_3_eq; assumption.
Qed.

End Arg11_3.

Arguments paco11_3_0_acc : clear implicits.
Arguments paco11_3_1_acc : clear implicits.
Arguments paco11_3_2_acc : clear implicits.
Arguments paco11_3_0_mon : clear implicits.
Arguments paco11_3_1_mon : clear implicits.
Arguments paco11_3_2_mon : clear implicits.
Arguments upaco11_3_0_mon : clear implicits.
Arguments upaco11_3_1_mon : clear implicits.
Arguments upaco11_3_2_mon : clear implicits.
Arguments paco11_3_0_mult_strong : clear implicits.
Arguments paco11_3_1_mult_strong : clear implicits.
Arguments paco11_3_2_mult_strong : clear implicits.
Arguments paco11_3_0_mult : clear implicits.
Arguments paco11_3_1_mult : clear implicits.
Arguments paco11_3_2_mult : clear implicits.
Arguments paco11_3_0_fold : clear implicits.
Arguments paco11_3_1_fold : clear implicits.
Arguments paco11_3_2_fold : clear implicits.
Arguments paco11_3_0_unfold : clear implicits.
Arguments paco11_3_1_unfold : clear implicits.
Arguments paco11_3_2_unfold : clear implicits.

Global Instance paco11_3_0_inst  (gf_0 gf_1 gf_2 : rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : paco_class (paco11_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) :=
{ pacoacc    := paco11_3_0_acc gf_0 gf_1 gf_2;
  pacomult   := paco11_3_0_mult gf_0 gf_1 gf_2;
  pacofold   := paco11_3_0_fold gf_0 gf_1 gf_2;
  pacounfold := paco11_3_0_unfold gf_0 gf_1 gf_2 }.

Global Instance paco11_3_1_inst  (gf_0 gf_1 gf_2 : rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : paco_class (paco11_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) :=
{ pacoacc    := paco11_3_1_acc gf_0 gf_1 gf_2;
  pacomult   := paco11_3_1_mult gf_0 gf_1 gf_2;
  pacofold   := paco11_3_1_fold gf_0 gf_1 gf_2;
  pacounfold := paco11_3_1_unfold gf_0 gf_1 gf_2 }.

Global Instance paco11_3_2_inst  (gf_0 gf_1 gf_2 : rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : paco_class (paco11_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) :=
{ pacoacc    := paco11_3_2_acc gf_0 gf_1 gf_2;
  pacomult   := paco11_3_2_mult gf_0 gf_1 gf_2;
  pacofold   := paco11_3_2_fold gf_0 gf_1 gf_2;
  pacounfold := paco11_3_2_unfold gf_0 gf_1 gf_2 }.

End PACO11.

Global Opaque paco11.

Hint Unfold upaco11.
Hint Resolve paco11_fold.
Hint Unfold monotone11.

Global Opaque paco11_2_0.
Global Opaque paco11_2_1.

Hint Unfold upaco11_2_0.
Hint Unfold upaco11_2_1.
Hint Resolve paco11_2_0_fold.
Hint Resolve paco11_2_1_fold.
Hint Unfold monotone11_2.

Global Opaque paco11_3_0.
Global Opaque paco11_3_1.
Global Opaque paco11_3_2.

Hint Unfold upaco11_3_0.
Hint Unfold upaco11_3_1.
Hint Unfold upaco11_3_2.
Hint Resolve paco11_3_0_fold.
Hint Resolve paco11_3_1_fold.
Hint Resolve paco11_3_2_fold.
Hint Unfold monotone11_3.

