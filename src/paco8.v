Require Export paconotation pacotacuser.
Require Import paconotation_internal pacotac pacon.
Set Implicit Arguments.

Section PACO8.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
Variable T7 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5), Type.

Record sig8T :=
  exist8T { 
      proj8T0: @T0;
      proj8T1: @T1 proj8T0;
      proj8T2: @T2 proj8T0 proj8T1;
      proj8T3: @T3 proj8T0 proj8T1 proj8T2;
      proj8T4: @T4 proj8T0 proj8T1 proj8T2 proj8T3;
      proj8T5: @T5 proj8T0 proj8T1 proj8T2 proj8T3 proj8T4;
      proj8T6: @T6 proj8T0 proj8T1 proj8T2 proj8T3 proj8T4 proj8T5;
      proj8T7: @T7 proj8T0 proj8T1 proj8T2 proj8T3 proj8T4 proj8T5 proj8T6;
    }.

Definition uncurry8 (R: rel8 T0 T1 T2 T3 T4 T5 T6 T7): rel1 sig8T := fun x => R (proj8T0 x) (proj8T1 x) (proj8T2 x) (proj8T3 x) (proj8T4 x) (proj8T5 x) (proj8T6 x) (proj8T7 x).

Definition curry8 (R: rel1 sig8T): rel8 T0 T1 T2 T3 T4 T5 T6 T7 :=
  fun x0 x1 x2 x3 x4 x5 x6 x7 => R (exist8T x7).

Lemma uncurry_map8 r0 r1 (LE : r0 <8== r1) : uncurry8 r0 <1== uncurry8 r1.
Proof. intros [] H. apply LE. apply H. Qed.

Lemma uncurry_map_rev8 r0 r1 (LE: uncurry8 r0 <1== uncurry8 r1) : r0 <8== r1.
Proof.
  repeat_intros 8. intros H. apply (LE (exist8T x7) H).
Qed.

Lemma curry_map8 r0 r1 (LE: r0 <1== r1) : curry8 r0 <8== curry8 r1.
Proof. 
  repeat_intros 8. intros H. apply (LE (exist8T x7) H).
Qed.

Lemma curry_map_rev8 r0 r1 (LE: curry8 r0 <8== curry8 r1) : r0 <1== r1.
Proof. 
  intros [] H. apply LE. apply H.
Qed.

Lemma uncurry_bij1_8 r : curry8 (uncurry8 r) <8== r.
Proof. unfold le8. repeat_intros 8. intros H. apply H. Qed.

Lemma uncurry_bij2_8 r : r <8== curry8 (uncurry8 r).
Proof. unfold le8. repeat_intros 8. intros H. apply H. Qed.

Lemma curry_bij1_8 r : uncurry8 (curry8 r) <1== r.
Proof. intros []. intro H. apply H. Qed.

Lemma curry_bij2_8 r : r <1== uncurry8 (curry8 r).
Proof. intros []. intro H. apply H. Qed.

Lemma uncurry_adjoint1_8 r0 r1 (LE: uncurry8 r0 <1== r1) : r0 <8== curry8 r1.
Proof.
  apply uncurry_map_rev8. eapply le1_trans; [apply LE|]. apply curry_bij2_8.
Qed.

Lemma uncurry_adjoint2_8 r0 r1 (LE: r0 <8== curry8 r1) : uncurry8 r0 <1== r1.
Proof.
  apply curry_map_rev8. eapply le8_trans; [|apply LE]. apply uncurry_bij2_8.
Qed.

Lemma curry_adjoint1_8 r0 r1 (LE: curry8 r0 <8== r1) : r0 <1== uncurry8 r1.
Proof.
  apply curry_map_rev8. eapply le8_trans; [apply LE|]. apply uncurry_bij2_8.
Qed.

Lemma curry_adjoint2_8 r0 r1 (LE: r0 <1== uncurry8 r1) : curry8 r0 <8== r1.
Proof.
  apply uncurry_map_rev8. eapply le1_trans; [|apply LE]. apply curry_bij1_8.
Qed.

(** ** Predicates of Arity 8
*)

Section Arg8_def.
Variable gf : rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7.
Arguments gf : clear implicits.

Definition paco8( r: rel8 T0 T1 T2 T3 T4 T5 T6 T7) : rel8 T0 T1 T2 T3 T4 T5 T6 T7 :=
  curry8 (paco (fun R0 => uncurry8 (gf (curry8 R0))) (uncurry8 r)).

Definition upaco8( r: rel8 T0 T1 T2 T3 T4 T5 T6 T7) := paco8 r \8/ r.
End Arg8_def.
Arguments paco8 : clear implicits.
Arguments upaco8 : clear implicits.
Hint Unfold upaco8.

Section Arg8_2_def.
Variable gf_0 gf_1 : rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.

Definition paco8_2_0( r_0 r_1: rel8 T0 T1 T2 T3 T4 T5 T6 T7) : rel8 T0 T1 T2 T3 T4 T5 T6 T7 :=
  curry8 (paco_2_0 (fun R0 R1 => uncurry8 (gf_0 (curry8 R0) (curry8 R1))) (fun R0 R1 => uncurry8 (gf_1 (curry8 R0) (curry8 R1))) (uncurry8 r_0) (uncurry8 r_1)).

Definition paco8_2_1( r_0 r_1: rel8 T0 T1 T2 T3 T4 T5 T6 T7) : rel8 T0 T1 T2 T3 T4 T5 T6 T7 :=
  curry8 (paco_2_1 (fun R0 R1 => uncurry8 (gf_0 (curry8 R0) (curry8 R1))) (fun R0 R1 => uncurry8 (gf_1 (curry8 R0) (curry8 R1))) (uncurry8 r_0) (uncurry8 r_1)).

Definition upaco8_2_0( r_0 r_1: rel8 T0 T1 T2 T3 T4 T5 T6 T7) := paco8_2_0 r_0 r_1 \8/ r_0.
Definition upaco8_2_1( r_0 r_1: rel8 T0 T1 T2 T3 T4 T5 T6 T7) := paco8_2_1 r_0 r_1 \8/ r_1.
End Arg8_2_def.
Arguments paco8_2_0 : clear implicits.
Arguments upaco8_2_0 : clear implicits.
Hint Unfold upaco8_2_0.
Arguments paco8_2_1 : clear implicits.
Arguments upaco8_2_1 : clear implicits.
Hint Unfold upaco8_2_1.

Section Arg8_3_def.
Variable gf_0 gf_1 gf_2 : rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.
Arguments gf_2 : clear implicits.

Definition paco8_3_0( r_0 r_1 r_2: rel8 T0 T1 T2 T3 T4 T5 T6 T7) : rel8 T0 T1 T2 T3 T4 T5 T6 T7 :=
  curry8 (paco_3_0 (fun R0 R1 R2 => uncurry8 (gf_0 (curry8 R0) (curry8 R1) (curry8 R2))) (fun R0 R1 R2 => uncurry8 (gf_1 (curry8 R0) (curry8 R1) (curry8 R2))) (fun R0 R1 R2 => uncurry8 (gf_2 (curry8 R0) (curry8 R1) (curry8 R2))) (uncurry8 r_0) (uncurry8 r_1) (uncurry8 r_2)).

Definition paco8_3_1( r_0 r_1 r_2: rel8 T0 T1 T2 T3 T4 T5 T6 T7) : rel8 T0 T1 T2 T3 T4 T5 T6 T7 :=
  curry8 (paco_3_1 (fun R0 R1 R2 => uncurry8 (gf_0 (curry8 R0) (curry8 R1) (curry8 R2))) (fun R0 R1 R2 => uncurry8 (gf_1 (curry8 R0) (curry8 R1) (curry8 R2))) (fun R0 R1 R2 => uncurry8 (gf_2 (curry8 R0) (curry8 R1) (curry8 R2))) (uncurry8 r_0) (uncurry8 r_1) (uncurry8 r_2)).

Definition paco8_3_2( r_0 r_1 r_2: rel8 T0 T1 T2 T3 T4 T5 T6 T7) : rel8 T0 T1 T2 T3 T4 T5 T6 T7 :=
  curry8 (paco_3_2 (fun R0 R1 R2 => uncurry8 (gf_0 (curry8 R0) (curry8 R1) (curry8 R2))) (fun R0 R1 R2 => uncurry8 (gf_1 (curry8 R0) (curry8 R1) (curry8 R2))) (fun R0 R1 R2 => uncurry8 (gf_2 (curry8 R0) (curry8 R1) (curry8 R2))) (uncurry8 r_0) (uncurry8 r_1) (uncurry8 r_2)).

Definition upaco8_3_0( r_0 r_1 r_2: rel8 T0 T1 T2 T3 T4 T5 T6 T7) := paco8_3_0 r_0 r_1 r_2 \8/ r_0.
Definition upaco8_3_1( r_0 r_1 r_2: rel8 T0 T1 T2 T3 T4 T5 T6 T7) := paco8_3_1 r_0 r_1 r_2 \8/ r_1.
Definition upaco8_3_2( r_0 r_1 r_2: rel8 T0 T1 T2 T3 T4 T5 T6 T7) := paco8_3_2 r_0 r_1 r_2 \8/ r_2.
End Arg8_3_def.
Arguments paco8_3_0 : clear implicits.
Arguments upaco8_3_0 : clear implicits.
Hint Unfold upaco8_3_0.
Arguments paco8_3_1 : clear implicits.
Arguments upaco8_3_1 : clear implicits.
Hint Unfold upaco8_3_1.
Arguments paco8_3_2 : clear implicits.
Arguments upaco8_3_2 : clear implicits.
Hint Unfold upaco8_3_2.

(** 1 Mutual Coinduction *)

Section Arg8_1.

Definition monotone8 (gf: rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7) :=
  forall x0 x1 x2 x3 x4 x5 x6 x7 r r' (IN: gf r x0 x1 x2 x3 x4 x5 x6 x7) (LE: r <8= r'), gf r' x0 x1 x2 x3 x4 x5 x6 x7.

Definition _monotone8 (gf: rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7) :=
  forall r r'(LE: r <8= r'), gf r <8== gf r'.

Lemma monotone8_eq (gf: rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7) :
  monotone8 gf <-> _monotone8 gf.
Proof. unfold monotone8, _monotone8, le8. split; intros; eapply H; eassumption. Qed.

Lemma monotone8_map (gf: rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7)
      (MON: _monotone8 gf) :
  _monotone (fun R0 => uncurry8 (gf (curry8 R0))).
Proof.
  repeat_intros 3. apply uncurry_map8. apply MON; apply curry_map8; assumption.
Qed.

Variable gf : rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7.
Arguments gf : clear implicits.

Theorem _paco8_mon: _monotone8 (paco8 gf).
Proof.
  repeat_intros 3. eapply curry_map8, _paco_mon; apply uncurry_map8; assumption.
Qed.

Theorem _paco8_acc: forall
  l r (OBG: forall rr (INC: r <8== rr) (CIH: l <8== rr), l <8== paco8 gf rr),
  l <8== paco8 gf r.
Proof.
  intros. apply uncurry_adjoint1_8.
  eapply _paco_acc. intros.
  apply uncurry_adjoint1_8 in INC. apply uncurry_adjoint1_8 in CIH.
  apply uncurry_adjoint2_8.
  eapply le8_trans. eapply (OBG _ INC CIH).
  apply curry_map8.
  apply _paco_mon; try apply le1_refl; apply curry_bij1_8.
Qed.

Theorem _paco8_mult_strong: forall r,
  paco8 gf (upaco8 gf r) <8== paco8 gf r.
Proof.
  intros. apply curry_map8.
  eapply le1_trans; [| eapply _paco_mult_strong].
  apply _paco_mon; intros []; intros H; apply H.
Qed.

Theorem _paco8_fold: forall r,
  gf (upaco8 gf r) <8== paco8 gf r.
Proof.
  intros. apply uncurry_adjoint1_8.
  eapply le1_trans; [| apply _paco_fold]. apply le1_refl.
Qed.

Theorem _paco8_unfold: forall (MON: _monotone8 gf) r,
  paco8 gf r <8== gf (upaco8 gf r).
Proof.
  intros. apply curry_adjoint2_8.
  eapply _paco_unfold; apply monotone8_map; assumption.
Qed.

Theorem paco8_acc: forall
  l r (OBG: forall rr (INC: r <8= rr) (CIH: l <8= rr), l <8= paco8 gf rr),
  l <8= paco8 gf r.
Proof.
  apply _paco8_acc.
Qed.

Theorem paco8_mon: monotone8 (paco8 gf).
Proof.
  apply monotone8_eq.
  apply _paco8_mon.
Qed.

Theorem upaco8_mon: monotone8 (upaco8 gf).
Proof.
  repeat_intros 10. intros R  LE0.
  destruct R.
  - left. eapply paco8_mon. apply H. apply LE0.
  - right. apply LE0, H.
Qed.
Theorem paco8_mult_strong: forall r,
  paco8 gf (upaco8 gf r) <8= paco8 gf r.
Proof.
  apply _paco8_mult_strong.
Qed.

Corollary paco8_mult: forall r,
  paco8 gf (paco8 gf r) <8= paco8 gf r.
Proof. intros; eapply paco8_mult_strong, paco8_mon; [apply PR|..]; intros; left; assumption. Qed.

Theorem paco8_fold: forall r,
  gf (upaco8 gf r) <8= paco8 gf r.
Proof.
  apply _paco8_fold.
Qed.

Theorem paco8_unfold: forall (MON: monotone8 gf) r,
  paco8 gf r <8= gf (upaco8 gf r).
Proof.
  repeat_intros 1. eapply _paco8_unfold; apply monotone8_eq; assumption.
Qed.

End Arg8_1.

Arguments paco8_acc : clear implicits.
Arguments paco8_mon : clear implicits.
Arguments upaco8_mon : clear implicits.
Arguments paco8_mult_strong : clear implicits.
Arguments paco8_mult : clear implicits.
Arguments paco8_fold : clear implicits.
Arguments paco8_unfold : clear implicits.

Global Instance paco8_inst  (gf : rel8 T0 T1 T2 T3 T4 T5 T6 T7->_) r x0 x1 x2 x3 x4 x5 x6 x7 : paco_class (paco8 gf r x0 x1 x2 x3 x4 x5 x6 x7) :=
{ pacoacc    := paco8_acc gf;
  pacomult   := paco8_mult gf;
  pacofold   := paco8_fold gf;
  pacounfold := paco8_unfold gf }.

(** 2 Mutual Coinduction *)

Section Arg8_2.

Definition monotone8_2 (gf: rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7) :=
  forall x0 x1 x2 x3 x4 x5 x6 x7 r_0 r_1 r'_0 r'_1 (IN: gf r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7) (LE_0: r_0 <8= r'_0)(LE_1: r_1 <8= r'_1), gf r'_0 r'_1 x0 x1 x2 x3 x4 x5 x6 x7.

Definition _monotone8_2 (gf: rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7) :=
  forall r_0 r_1 r'_0 r'_1(LE_0: r_0 <8= r'_0)(LE_1: r_1 <8= r'_1), gf r_0 r_1 <8== gf r'_0 r'_1.

Lemma monotone8_2_eq (gf: rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7) :
  monotone8_2 gf <-> _monotone8_2 gf.
Proof. unfold monotone8_2, _monotone8_2, le8. split; intros; eapply H; eassumption. Qed.

Lemma monotone8_2_map (gf: rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7)
      (MON: _monotone8_2 gf) :
  _monotone_2 (fun R0 R1 => uncurry8 (gf (curry8 R0) (curry8 R1))).
Proof.
  repeat_intros 6. apply uncurry_map8. apply MON; apply curry_map8; assumption.
Qed.

Variable gf_0 gf_1 : rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.

Theorem _paco8_2_0_mon: _monotone8_2 (paco8_2_0 gf_0 gf_1).
Proof.
  repeat_intros 6. eapply curry_map8, _paco_2_0_mon; apply uncurry_map8; assumption.
Qed.

Theorem _paco8_2_1_mon: _monotone8_2 (paco8_2_1 gf_0 gf_1).
Proof.
  repeat_intros 6. eapply curry_map8, _paco_2_1_mon; apply uncurry_map8; assumption.
Qed.

Theorem _paco8_2_0_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_0 <8== rr) (CIH: l <8== rr), l <8== paco8_2_0 gf_0 gf_1 rr r_1),
  l <8== paco8_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_8.
  eapply _paco_2_0_acc. intros.
  apply uncurry_adjoint1_8 in INC. apply uncurry_adjoint1_8 in CIH.
  apply uncurry_adjoint2_8.
  eapply le8_trans. eapply (OBG _ INC CIH).
  apply curry_map8.
  apply _paco_2_0_mon; try apply le1_refl; apply curry_bij1_8.
Qed.

Theorem _paco8_2_1_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_1 <8== rr) (CIH: l <8== rr), l <8== paco8_2_1 gf_0 gf_1 r_0 rr),
  l <8== paco8_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_8.
  eapply _paco_2_1_acc. intros.
  apply uncurry_adjoint1_8 in INC. apply uncurry_adjoint1_8 in CIH.
  apply uncurry_adjoint2_8.
  eapply le8_trans. eapply (OBG _ INC CIH).
  apply curry_map8.
  apply _paco_2_1_mon; try apply le1_refl; apply curry_bij1_8.
Qed.

Theorem _paco8_2_0_mult_strong: forall r_0 r_1,
  paco8_2_0 gf_0 gf_1 (upaco8_2_0 gf_0 gf_1 r_0 r_1) (upaco8_2_1 gf_0 gf_1 r_0 r_1) <8== paco8_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply curry_map8.
  eapply le1_trans; [| eapply _paco_2_0_mult_strong].
  apply _paco_2_0_mon; intros []; intros H; apply H.
Qed.

Theorem _paco8_2_1_mult_strong: forall r_0 r_1,
  paco8_2_1 gf_0 gf_1 (upaco8_2_0 gf_0 gf_1 r_0 r_1) (upaco8_2_1 gf_0 gf_1 r_0 r_1) <8== paco8_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply curry_map8.
  eapply le1_trans; [| eapply _paco_2_1_mult_strong].
  apply _paco_2_1_mon; intros []; intros H; apply H.
Qed.

Theorem _paco8_2_0_fold: forall r_0 r_1,
  gf_0 (upaco8_2_0 gf_0 gf_1 r_0 r_1) (upaco8_2_1 gf_0 gf_1 r_0 r_1) <8== paco8_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_8.
  eapply le1_trans; [| apply _paco_2_0_fold]. apply le1_refl.
Qed.

Theorem _paco8_2_1_fold: forall r_0 r_1,
  gf_1 (upaco8_2_0 gf_0 gf_1 r_0 r_1) (upaco8_2_1 gf_0 gf_1 r_0 r_1) <8== paco8_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_8.
  eapply le1_trans; [| apply _paco_2_1_fold]. apply le1_refl.
Qed.

Theorem _paco8_2_0_unfold: forall (MON: _monotone8_2 gf_0) (MON: _monotone8_2 gf_1) r_0 r_1,
  paco8_2_0 gf_0 gf_1 r_0 r_1 <8== gf_0 (upaco8_2_0 gf_0 gf_1 r_0 r_1) (upaco8_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  intros. apply curry_adjoint2_8.
  eapply _paco_2_0_unfold; apply monotone8_2_map; assumption.
Qed.

Theorem _paco8_2_1_unfold: forall (MON: _monotone8_2 gf_0) (MON: _monotone8_2 gf_1) r_0 r_1,
  paco8_2_1 gf_0 gf_1 r_0 r_1 <8== gf_1 (upaco8_2_0 gf_0 gf_1 r_0 r_1) (upaco8_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  intros. apply curry_adjoint2_8.
  eapply _paco_2_1_unfold; apply monotone8_2_map; assumption.
Qed.

Theorem paco8_2_0_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_0 <8= rr) (CIH: l <8= rr), l <8= paco8_2_0 gf_0 gf_1 rr r_1),
  l <8= paco8_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco8_2_0_acc.
Qed.

Theorem paco8_2_1_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_1 <8= rr) (CIH: l <8= rr), l <8= paco8_2_1 gf_0 gf_1 r_0 rr),
  l <8= paco8_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco8_2_1_acc.
Qed.

Theorem paco8_2_0_mon: monotone8_2 (paco8_2_0 gf_0 gf_1).
Proof.
  apply monotone8_2_eq.
  apply _paco8_2_0_mon.
Qed.

Theorem paco8_2_1_mon: monotone8_2 (paco8_2_1 gf_0 gf_1).
Proof.
  apply monotone8_2_eq.
  apply _paco8_2_1_mon.
Qed.

Theorem upaco8_2_0_mon: monotone8_2 (upaco8_2_0 gf_0 gf_1).
Proof.
  repeat_intros 12. intros R  LE0 LE1.
  destruct R.
  - left. eapply paco8_2_0_mon. apply H. apply LE0. apply LE1.
  - right. apply LE0, H.
Qed.
Theorem upaco8_2_1_mon: monotone8_2 (upaco8_2_1 gf_0 gf_1).
Proof.
  repeat_intros 12. intros R  LE0 LE1.
  destruct R.
  - left. eapply paco8_2_1_mon. apply H. apply LE0. apply LE1.
  - right. apply LE1, H.
Qed.
Theorem paco8_2_0_mult_strong: forall r_0 r_1,
  paco8_2_0 gf_0 gf_1 (upaco8_2_0 gf_0 gf_1 r_0 r_1) (upaco8_2_1 gf_0 gf_1 r_0 r_1) <8= paco8_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco8_2_0_mult_strong.
Qed.

Theorem paco8_2_1_mult_strong: forall r_0 r_1,
  paco8_2_1 gf_0 gf_1 (upaco8_2_0 gf_0 gf_1 r_0 r_1) (upaco8_2_1 gf_0 gf_1 r_0 r_1) <8= paco8_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco8_2_1_mult_strong.
Qed.

Corollary paco8_2_0_mult: forall r_0 r_1,
  paco8_2_0 gf_0 gf_1 (paco8_2_0 gf_0 gf_1 r_0 r_1) (paco8_2_1 gf_0 gf_1 r_0 r_1) <8= paco8_2_0 gf_0 gf_1 r_0 r_1.
Proof. intros; eapply paco8_2_0_mult_strong, paco8_2_0_mon; [apply PR|..]; intros; left; assumption. Qed.

Corollary paco8_2_1_mult: forall r_0 r_1,
  paco8_2_1 gf_0 gf_1 (paco8_2_0 gf_0 gf_1 r_0 r_1) (paco8_2_1 gf_0 gf_1 r_0 r_1) <8= paco8_2_1 gf_0 gf_1 r_0 r_1.
Proof. intros; eapply paco8_2_1_mult_strong, paco8_2_1_mon; [apply PR|..]; intros; left; assumption. Qed.

Theorem paco8_2_0_fold: forall r_0 r_1,
  gf_0 (upaco8_2_0 gf_0 gf_1 r_0 r_1) (upaco8_2_1 gf_0 gf_1 r_0 r_1) <8= paco8_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco8_2_0_fold.
Qed.

Theorem paco8_2_1_fold: forall r_0 r_1,
  gf_1 (upaco8_2_0 gf_0 gf_1 r_0 r_1) (upaco8_2_1 gf_0 gf_1 r_0 r_1) <8= paco8_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco8_2_1_fold.
Qed.

Theorem paco8_2_0_unfold: forall (MON: monotone8_2 gf_0) (MON: monotone8_2 gf_1) r_0 r_1,
  paco8_2_0 gf_0 gf_1 r_0 r_1 <8= gf_0 (upaco8_2_0 gf_0 gf_1 r_0 r_1) (upaco8_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  repeat_intros 2. eapply _paco8_2_0_unfold; apply monotone8_2_eq; assumption.
Qed.

Theorem paco8_2_1_unfold: forall (MON: monotone8_2 gf_0) (MON: monotone8_2 gf_1) r_0 r_1,
  paco8_2_1 gf_0 gf_1 r_0 r_1 <8= gf_1 (upaco8_2_0 gf_0 gf_1 r_0 r_1) (upaco8_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  repeat_intros 2. eapply _paco8_2_1_unfold; apply monotone8_2_eq; assumption.
Qed.

End Arg8_2.

Arguments paco8_2_0_acc : clear implicits.
Arguments paco8_2_1_acc : clear implicits.
Arguments paco8_2_0_mon : clear implicits.
Arguments paco8_2_1_mon : clear implicits.
Arguments upaco8_2_0_mon : clear implicits.
Arguments upaco8_2_1_mon : clear implicits.
Arguments paco8_2_0_mult_strong : clear implicits.
Arguments paco8_2_1_mult_strong : clear implicits.
Arguments paco8_2_0_mult : clear implicits.
Arguments paco8_2_1_mult : clear implicits.
Arguments paco8_2_0_fold : clear implicits.
Arguments paco8_2_1_fold : clear implicits.
Arguments paco8_2_0_unfold : clear implicits.
Arguments paco8_2_1_unfold : clear implicits.

Global Instance paco8_2_0_inst  (gf_0 gf_1 : rel8 T0 T1 T2 T3 T4 T5 T6 T7->_) r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 : paco_class (paco8_2_0 gf_0 gf_1 r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7) :=
{ pacoacc    := paco8_2_0_acc gf_0 gf_1;
  pacomult   := paco8_2_0_mult gf_0 gf_1;
  pacofold   := paco8_2_0_fold gf_0 gf_1;
  pacounfold := paco8_2_0_unfold gf_0 gf_1 }.

Global Instance paco8_2_1_inst  (gf_0 gf_1 : rel8 T0 T1 T2 T3 T4 T5 T6 T7->_) r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 : paco_class (paco8_2_1 gf_0 gf_1 r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7) :=
{ pacoacc    := paco8_2_1_acc gf_0 gf_1;
  pacomult   := paco8_2_1_mult gf_0 gf_1;
  pacofold   := paco8_2_1_fold gf_0 gf_1;
  pacounfold := paco8_2_1_unfold gf_0 gf_1 }.

(** 3 Mutual Coinduction *)

Section Arg8_3.

Definition monotone8_3 (gf: rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7) :=
  forall x0 x1 x2 x3 x4 x5 x6 x7 r_0 r_1 r_2 r'_0 r'_1 r'_2 (IN: gf r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7) (LE_0: r_0 <8= r'_0)(LE_1: r_1 <8= r'_1)(LE_2: r_2 <8= r'_2), gf r'_0 r'_1 r'_2 x0 x1 x2 x3 x4 x5 x6 x7.

Definition _monotone8_3 (gf: rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7) :=
  forall r_0 r_1 r_2 r'_0 r'_1 r'_2(LE_0: r_0 <8= r'_0)(LE_1: r_1 <8= r'_1)(LE_2: r_2 <8= r'_2), gf r_0 r_1 r_2 <8== gf r'_0 r'_1 r'_2.

Lemma monotone8_3_eq (gf: rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7) :
  monotone8_3 gf <-> _monotone8_3 gf.
Proof. unfold monotone8_3, _monotone8_3, le8. split; intros; eapply H; eassumption. Qed.

Lemma monotone8_3_map (gf: rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7)
      (MON: _monotone8_3 gf) :
  _monotone_3 (fun R0 R1 R2 => uncurry8 (gf (curry8 R0) (curry8 R1) (curry8 R2))).
Proof.
  repeat_intros 9. apply uncurry_map8. apply MON; apply curry_map8; assumption.
Qed.

Variable gf_0 gf_1 gf_2 : rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.
Arguments gf_2 : clear implicits.

Theorem _paco8_3_0_mon: _monotone8_3 (paco8_3_0 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 9. eapply curry_map8, _paco_3_0_mon; apply uncurry_map8; assumption.
Qed.

Theorem _paco8_3_1_mon: _monotone8_3 (paco8_3_1 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 9. eapply curry_map8, _paco_3_1_mon; apply uncurry_map8; assumption.
Qed.

Theorem _paco8_3_2_mon: _monotone8_3 (paco8_3_2 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 9. eapply curry_map8, _paco_3_2_mon; apply uncurry_map8; assumption.
Qed.

Theorem _paco8_3_0_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_0 <8== rr) (CIH: l <8== rr), l <8== paco8_3_0 gf_0 gf_1 gf_2 rr r_1 r_2),
  l <8== paco8_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_8.
  eapply _paco_3_0_acc. intros.
  apply uncurry_adjoint1_8 in INC. apply uncurry_adjoint1_8 in CIH.
  apply uncurry_adjoint2_8.
  eapply le8_trans. eapply (OBG _ INC CIH).
  apply curry_map8.
  apply _paco_3_0_mon; try apply le1_refl; apply curry_bij1_8.
Qed.

Theorem _paco8_3_1_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_1 <8== rr) (CIH: l <8== rr), l <8== paco8_3_1 gf_0 gf_1 gf_2 r_0 rr r_2),
  l <8== paco8_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_8.
  eapply _paco_3_1_acc. intros.
  apply uncurry_adjoint1_8 in INC. apply uncurry_adjoint1_8 in CIH.
  apply uncurry_adjoint2_8.
  eapply le8_trans. eapply (OBG _ INC CIH).
  apply curry_map8.
  apply _paco_3_1_mon; try apply le1_refl; apply curry_bij1_8.
Qed.

Theorem _paco8_3_2_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_2 <8== rr) (CIH: l <8== rr), l <8== paco8_3_2 gf_0 gf_1 gf_2 r_0 r_1 rr),
  l <8== paco8_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_8.
  eapply _paco_3_2_acc. intros.
  apply uncurry_adjoint1_8 in INC. apply uncurry_adjoint1_8 in CIH.
  apply uncurry_adjoint2_8.
  eapply le8_trans. eapply (OBG _ INC CIH).
  apply curry_map8.
  apply _paco_3_2_mon; try apply le1_refl; apply curry_bij1_8.
Qed.

Theorem _paco8_3_0_mult_strong: forall r_0 r_1 r_2,
  paco8_3_0 gf_0 gf_1 gf_2 (upaco8_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco8_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco8_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <8== paco8_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply curry_map8.
  eapply le1_trans; [| eapply _paco_3_0_mult_strong].
  apply _paco_3_0_mon; intros []; intros H; apply H.
Qed.

Theorem _paco8_3_1_mult_strong: forall r_0 r_1 r_2,
  paco8_3_1 gf_0 gf_1 gf_2 (upaco8_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco8_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco8_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <8== paco8_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply curry_map8.
  eapply le1_trans; [| eapply _paco_3_1_mult_strong].
  apply _paco_3_1_mon; intros []; intros H; apply H.
Qed.

Theorem _paco8_3_2_mult_strong: forall r_0 r_1 r_2,
  paco8_3_2 gf_0 gf_1 gf_2 (upaco8_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco8_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco8_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <8== paco8_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply curry_map8.
  eapply le1_trans; [| eapply _paco_3_2_mult_strong].
  apply _paco_3_2_mon; intros []; intros H; apply H.
Qed.

Theorem _paco8_3_0_fold: forall r_0 r_1 r_2,
  gf_0 (upaco8_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco8_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco8_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <8== paco8_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_8.
  eapply le1_trans; [| apply _paco_3_0_fold]. apply le1_refl.
Qed.

Theorem _paco8_3_1_fold: forall r_0 r_1 r_2,
  gf_1 (upaco8_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco8_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco8_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <8== paco8_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_8.
  eapply le1_trans; [| apply _paco_3_1_fold]. apply le1_refl.
Qed.

Theorem _paco8_3_2_fold: forall r_0 r_1 r_2,
  gf_2 (upaco8_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco8_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco8_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <8== paco8_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_8.
  eapply le1_trans; [| apply _paco_3_2_fold]. apply le1_refl.
Qed.

Theorem _paco8_3_0_unfold: forall (MON: _monotone8_3 gf_0) (MON: _monotone8_3 gf_1) (MON: _monotone8_3 gf_2) r_0 r_1 r_2,
  paco8_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 <8== gf_0 (upaco8_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco8_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco8_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  intros. apply curry_adjoint2_8.
  eapply _paco_3_0_unfold; apply monotone8_3_map; assumption.
Qed.

Theorem _paco8_3_1_unfold: forall (MON: _monotone8_3 gf_0) (MON: _monotone8_3 gf_1) (MON: _monotone8_3 gf_2) r_0 r_1 r_2,
  paco8_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 <8== gf_1 (upaco8_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco8_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco8_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  intros. apply curry_adjoint2_8.
  eapply _paco_3_1_unfold; apply monotone8_3_map; assumption.
Qed.

Theorem _paco8_3_2_unfold: forall (MON: _monotone8_3 gf_0) (MON: _monotone8_3 gf_1) (MON: _monotone8_3 gf_2) r_0 r_1 r_2,
  paco8_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 <8== gf_2 (upaco8_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco8_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco8_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  intros. apply curry_adjoint2_8.
  eapply _paco_3_2_unfold; apply monotone8_3_map; assumption.
Qed.

Theorem paco8_3_0_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_0 <8= rr) (CIH: l <8= rr), l <8= paco8_3_0 gf_0 gf_1 gf_2 rr r_1 r_2),
  l <8= paco8_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco8_3_0_acc.
Qed.

Theorem paco8_3_1_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_1 <8= rr) (CIH: l <8= rr), l <8= paco8_3_1 gf_0 gf_1 gf_2 r_0 rr r_2),
  l <8= paco8_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco8_3_1_acc.
Qed.

Theorem paco8_3_2_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_2 <8= rr) (CIH: l <8= rr), l <8= paco8_3_2 gf_0 gf_1 gf_2 r_0 r_1 rr),
  l <8= paco8_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco8_3_2_acc.
Qed.

Theorem paco8_3_0_mon: monotone8_3 (paco8_3_0 gf_0 gf_1 gf_2).
Proof.
  apply monotone8_3_eq.
  apply _paco8_3_0_mon.
Qed.

Theorem paco8_3_1_mon: monotone8_3 (paco8_3_1 gf_0 gf_1 gf_2).
Proof.
  apply monotone8_3_eq.
  apply _paco8_3_1_mon.
Qed.

Theorem paco8_3_2_mon: monotone8_3 (paco8_3_2 gf_0 gf_1 gf_2).
Proof.
  apply monotone8_3_eq.
  apply _paco8_3_2_mon.
Qed.

Theorem upaco8_3_0_mon: monotone8_3 (upaco8_3_0 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 14. intros R  LE0 LE1 LE2.
  destruct R.
  - left. eapply paco8_3_0_mon. apply H. apply LE0. apply LE1. apply LE2.
  - right. apply LE0, H.
Qed.
Theorem upaco8_3_1_mon: monotone8_3 (upaco8_3_1 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 14. intros R  LE0 LE1 LE2.
  destruct R.
  - left. eapply paco8_3_1_mon. apply H. apply LE0. apply LE1. apply LE2.
  - right. apply LE1, H.
Qed.
Theorem upaco8_3_2_mon: monotone8_3 (upaco8_3_2 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 14. intros R  LE0 LE1 LE2.
  destruct R.
  - left. eapply paco8_3_2_mon. apply H. apply LE0. apply LE1. apply LE2.
  - right. apply LE2, H.
Qed.
Theorem paco8_3_0_mult_strong: forall r_0 r_1 r_2,
  paco8_3_0 gf_0 gf_1 gf_2 (upaco8_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco8_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco8_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <8= paco8_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco8_3_0_mult_strong.
Qed.

Theorem paco8_3_1_mult_strong: forall r_0 r_1 r_2,
  paco8_3_1 gf_0 gf_1 gf_2 (upaco8_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco8_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco8_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <8= paco8_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco8_3_1_mult_strong.
Qed.

Theorem paco8_3_2_mult_strong: forall r_0 r_1 r_2,
  paco8_3_2 gf_0 gf_1 gf_2 (upaco8_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco8_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco8_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <8= paco8_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco8_3_2_mult_strong.
Qed.

Corollary paco8_3_0_mult: forall r_0 r_1 r_2,
  paco8_3_0 gf_0 gf_1 gf_2 (paco8_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco8_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco8_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <8= paco8_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco8_3_0_mult_strong, paco8_3_0_mon; [apply PR|..]; intros; left; assumption. Qed.

Corollary paco8_3_1_mult: forall r_0 r_1 r_2,
  paco8_3_1 gf_0 gf_1 gf_2 (paco8_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco8_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco8_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <8= paco8_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco8_3_1_mult_strong, paco8_3_1_mon; [apply PR|..]; intros; left; assumption. Qed.

Corollary paco8_3_2_mult: forall r_0 r_1 r_2,
  paco8_3_2 gf_0 gf_1 gf_2 (paco8_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco8_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco8_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <8= paco8_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco8_3_2_mult_strong, paco8_3_2_mon; [apply PR|..]; intros; left; assumption. Qed.

Theorem paco8_3_0_fold: forall r_0 r_1 r_2,
  gf_0 (upaco8_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco8_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco8_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <8= paco8_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco8_3_0_fold.
Qed.

Theorem paco8_3_1_fold: forall r_0 r_1 r_2,
  gf_1 (upaco8_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco8_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco8_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <8= paco8_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco8_3_1_fold.
Qed.

Theorem paco8_3_2_fold: forall r_0 r_1 r_2,
  gf_2 (upaco8_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco8_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco8_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <8= paco8_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco8_3_2_fold.
Qed.

Theorem paco8_3_0_unfold: forall (MON: monotone8_3 gf_0) (MON: monotone8_3 gf_1) (MON: monotone8_3 gf_2) r_0 r_1 r_2,
  paco8_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 <8= gf_0 (upaco8_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco8_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco8_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  repeat_intros 3. eapply _paco8_3_0_unfold; apply monotone8_3_eq; assumption.
Qed.

Theorem paco8_3_1_unfold: forall (MON: monotone8_3 gf_0) (MON: monotone8_3 gf_1) (MON: monotone8_3 gf_2) r_0 r_1 r_2,
  paco8_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 <8= gf_1 (upaco8_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco8_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco8_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  repeat_intros 3. eapply _paco8_3_1_unfold; apply monotone8_3_eq; assumption.
Qed.

Theorem paco8_3_2_unfold: forall (MON: monotone8_3 gf_0) (MON: monotone8_3 gf_1) (MON: monotone8_3 gf_2) r_0 r_1 r_2,
  paco8_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 <8= gf_2 (upaco8_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco8_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco8_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  repeat_intros 3. eapply _paco8_3_2_unfold; apply monotone8_3_eq; assumption.
Qed.

End Arg8_3.

Arguments paco8_3_0_acc : clear implicits.
Arguments paco8_3_1_acc : clear implicits.
Arguments paco8_3_2_acc : clear implicits.
Arguments paco8_3_0_mon : clear implicits.
Arguments paco8_3_1_mon : clear implicits.
Arguments paco8_3_2_mon : clear implicits.
Arguments upaco8_3_0_mon : clear implicits.
Arguments upaco8_3_1_mon : clear implicits.
Arguments upaco8_3_2_mon : clear implicits.
Arguments paco8_3_0_mult_strong : clear implicits.
Arguments paco8_3_1_mult_strong : clear implicits.
Arguments paco8_3_2_mult_strong : clear implicits.
Arguments paco8_3_0_mult : clear implicits.
Arguments paco8_3_1_mult : clear implicits.
Arguments paco8_3_2_mult : clear implicits.
Arguments paco8_3_0_fold : clear implicits.
Arguments paco8_3_1_fold : clear implicits.
Arguments paco8_3_2_fold : clear implicits.
Arguments paco8_3_0_unfold : clear implicits.
Arguments paco8_3_1_unfold : clear implicits.
Arguments paco8_3_2_unfold : clear implicits.

Global Instance paco8_3_0_inst  (gf_0 gf_1 gf_2 : rel8 T0 T1 T2 T3 T4 T5 T6 T7->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 : paco_class (paco8_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7) :=
{ pacoacc    := paco8_3_0_acc gf_0 gf_1 gf_2;
  pacomult   := paco8_3_0_mult gf_0 gf_1 gf_2;
  pacofold   := paco8_3_0_fold gf_0 gf_1 gf_2;
  pacounfold := paco8_3_0_unfold gf_0 gf_1 gf_2 }.

Global Instance paco8_3_1_inst  (gf_0 gf_1 gf_2 : rel8 T0 T1 T2 T3 T4 T5 T6 T7->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 : paco_class (paco8_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7) :=
{ pacoacc    := paco8_3_1_acc gf_0 gf_1 gf_2;
  pacomult   := paco8_3_1_mult gf_0 gf_1 gf_2;
  pacofold   := paco8_3_1_fold gf_0 gf_1 gf_2;
  pacounfold := paco8_3_1_unfold gf_0 gf_1 gf_2 }.

Global Instance paco8_3_2_inst  (gf_0 gf_1 gf_2 : rel8 T0 T1 T2 T3 T4 T5 T6 T7->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 : paco_class (paco8_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7) :=
{ pacoacc    := paco8_3_2_acc gf_0 gf_1 gf_2;
  pacomult   := paco8_3_2_mult gf_0 gf_1 gf_2;
  pacofold   := paco8_3_2_fold gf_0 gf_1 gf_2;
  pacounfold := paco8_3_2_unfold gf_0 gf_1 gf_2 }.

End PACO8.

Global Opaque paco8.

Hint Unfold upaco8.
Hint Resolve paco8_fold.
Hint Unfold monotone8.

Global Opaque paco8_2_0.
Global Opaque paco8_2_1.

Hint Unfold upaco8_2_0.
Hint Unfold upaco8_2_1.
Hint Resolve paco8_2_0_fold.
Hint Resolve paco8_2_1_fold.
Hint Unfold monotone8_2.

Global Opaque paco8_3_0.
Global Opaque paco8_3_1.
Global Opaque paco8_3_2.

Hint Unfold upaco8_3_0.
Hint Unfold upaco8_3_1.
Hint Unfold upaco8_3_2.
Hint Resolve paco8_3_0_fold.
Hint Resolve paco8_3_1_fold.
Hint Resolve paco8_3_2_fold.
Hint Unfold monotone8_3.

