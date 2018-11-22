Require Export paconotation pacotacuser.
Require Import paconotation_internal pacotac pacon.
Set Implicit Arguments.

Section PACO9.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
Variable T7 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5), Type.
Variable T8 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6), Type.

Record sig9T :=
  exist9T { 
      proj9T0: @T0;
      proj9T1: @T1 proj9T0;
      proj9T2: @T2 proj9T0 proj9T1;
      proj9T3: @T3 proj9T0 proj9T1 proj9T2;
      proj9T4: @T4 proj9T0 proj9T1 proj9T2 proj9T3;
      proj9T5: @T5 proj9T0 proj9T1 proj9T2 proj9T3 proj9T4;
      proj9T6: @T6 proj9T0 proj9T1 proj9T2 proj9T3 proj9T4 proj9T5;
      proj9T7: @T7 proj9T0 proj9T1 proj9T2 proj9T3 proj9T4 proj9T5 proj9T6;
      proj9T8: @T8 proj9T0 proj9T1 proj9T2 proj9T3 proj9T4 proj9T5 proj9T6 proj9T7;
    }.

Definition uncurry9 (R: rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8): rel1 sig9T := fun x => R (proj9T0 x) (proj9T1 x) (proj9T2 x) (proj9T3 x) (proj9T4 x) (proj9T5 x) (proj9T6 x) (proj9T7 x) (proj9T8 x).

Definition curry9 (R: rel1 sig9T): rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 :=
  fun x0 x1 x2 x3 x4 x5 x6 x7 x8 => R (exist9T x8).

Lemma uncurry_map9 r0 r1 (LE : r0 <9== r1) : uncurry9 r0 <1== uncurry9 r1.
Proof. intros [] H. apply LE. apply H. Qed.

Lemma uncurry_map_rev9 r0 r1 (LE: uncurry9 r0 <1== uncurry9 r1) : r0 <9== r1.
Proof.
  repeat_intros 9. intros H. apply (LE (exist9T x8) H).
Qed.

Lemma curry_map9 r0 r1 (LE: r0 <1== r1) : curry9 r0 <9== curry9 r1.
Proof. 
  repeat_intros 9. intros H. apply (LE (exist9T x8) H).
Qed.

Lemma curry_map_rev9 r0 r1 (LE: curry9 r0 <9== curry9 r1) : r0 <1== r1.
Proof. 
  intros [] H. apply LE. apply H.
Qed.

Lemma uncurry_bij1_9 r : curry9 (uncurry9 r) <9== r.
Proof. unfold le9. repeat_intros 9. intros H. apply H. Qed.

Lemma uncurry_bij2_9 r : r <9== curry9 (uncurry9 r).
Proof. unfold le9. repeat_intros 9. intros H. apply H. Qed.

Lemma curry_bij1_9 r : uncurry9 (curry9 r) <1== r.
Proof. intros []. intro H. apply H. Qed.

Lemma curry_bij2_9 r : r <1== uncurry9 (curry9 r).
Proof. intros []. intro H. apply H. Qed.

Lemma uncurry_adjoint1_9 r0 r1 (LE: uncurry9 r0 <1== r1) : r0 <9== curry9 r1.
Proof.
  apply uncurry_map_rev9. eapply le1_trans; [apply LE|]. apply curry_bij2_9.
Qed.

Lemma uncurry_adjoint2_9 r0 r1 (LE: r0 <9== curry9 r1) : uncurry9 r0 <1== r1.
Proof.
  apply curry_map_rev9. eapply le9_trans; [|apply LE]. apply uncurry_bij2_9.
Qed.

Lemma curry_adjoint1_9 r0 r1 (LE: curry9 r0 <9== r1) : r0 <1== uncurry9 r1.
Proof.
  apply curry_map_rev9. eapply le9_trans; [apply LE|]. apply uncurry_bij2_9.
Qed.

Lemma curry_adjoint2_9 r0 r1 (LE: r0 <1== uncurry9 r1) : curry9 r0 <9== r1.
Proof.
  apply uncurry_map_rev9. eapply le1_trans; [|apply LE]. apply curry_bij1_9.
Qed.

(** ** Predicates of Arity 9
*)

Section Arg9_def.
Variable gf : rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8.
Arguments gf : clear implicits.

Definition paco9( r: rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8) : rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 :=
  curry9 (paco (fun R0 => uncurry9 (gf (curry9 R0))) (uncurry9 r)).

Definition upaco9( r: rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8) := paco9 r \9/ r.
End Arg9_def.
Arguments paco9 : clear implicits.
Arguments upaco9 : clear implicits.
Hint Unfold upaco9.

Section Arg9_2_def.
Variable gf_0 gf_1 : rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.

Definition paco9_2_0( r_0 r_1: rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8) : rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 :=
  curry9 (paco_2_0 (fun R0 R1 => uncurry9 (gf_0 (curry9 R0) (curry9 R1))) (fun R0 R1 => uncurry9 (gf_1 (curry9 R0) (curry9 R1))) (uncurry9 r_0) (uncurry9 r_1)).

Definition paco9_2_1( r_0 r_1: rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8) : rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 :=
  curry9 (paco_2_1 (fun R0 R1 => uncurry9 (gf_0 (curry9 R0) (curry9 R1))) (fun R0 R1 => uncurry9 (gf_1 (curry9 R0) (curry9 R1))) (uncurry9 r_0) (uncurry9 r_1)).

Definition upaco9_2_0( r_0 r_1: rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8) := paco9_2_0 r_0 r_1 \9/ r_0.
Definition upaco9_2_1( r_0 r_1: rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8) := paco9_2_1 r_0 r_1 \9/ r_1.
End Arg9_2_def.
Arguments paco9_2_0 : clear implicits.
Arguments upaco9_2_0 : clear implicits.
Hint Unfold upaco9_2_0.
Arguments paco9_2_1 : clear implicits.
Arguments upaco9_2_1 : clear implicits.
Hint Unfold upaco9_2_1.

Section Arg9_3_def.
Variable gf_0 gf_1 gf_2 : rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.
Arguments gf_2 : clear implicits.

Definition paco9_3_0( r_0 r_1 r_2: rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8) : rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 :=
  curry9 (paco_3_0 (fun R0 R1 R2 => uncurry9 (gf_0 (curry9 R0) (curry9 R1) (curry9 R2))) (fun R0 R1 R2 => uncurry9 (gf_1 (curry9 R0) (curry9 R1) (curry9 R2))) (fun R0 R1 R2 => uncurry9 (gf_2 (curry9 R0) (curry9 R1) (curry9 R2))) (uncurry9 r_0) (uncurry9 r_1) (uncurry9 r_2)).

Definition paco9_3_1( r_0 r_1 r_2: rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8) : rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 :=
  curry9 (paco_3_1 (fun R0 R1 R2 => uncurry9 (gf_0 (curry9 R0) (curry9 R1) (curry9 R2))) (fun R0 R1 R2 => uncurry9 (gf_1 (curry9 R0) (curry9 R1) (curry9 R2))) (fun R0 R1 R2 => uncurry9 (gf_2 (curry9 R0) (curry9 R1) (curry9 R2))) (uncurry9 r_0) (uncurry9 r_1) (uncurry9 r_2)).

Definition paco9_3_2( r_0 r_1 r_2: rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8) : rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 :=
  curry9 (paco_3_2 (fun R0 R1 R2 => uncurry9 (gf_0 (curry9 R0) (curry9 R1) (curry9 R2))) (fun R0 R1 R2 => uncurry9 (gf_1 (curry9 R0) (curry9 R1) (curry9 R2))) (fun R0 R1 R2 => uncurry9 (gf_2 (curry9 R0) (curry9 R1) (curry9 R2))) (uncurry9 r_0) (uncurry9 r_1) (uncurry9 r_2)).

Definition upaco9_3_0( r_0 r_1 r_2: rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8) := paco9_3_0 r_0 r_1 r_2 \9/ r_0.
Definition upaco9_3_1( r_0 r_1 r_2: rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8) := paco9_3_1 r_0 r_1 r_2 \9/ r_1.
Definition upaco9_3_2( r_0 r_1 r_2: rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8) := paco9_3_2 r_0 r_1 r_2 \9/ r_2.
End Arg9_3_def.
Arguments paco9_3_0 : clear implicits.
Arguments upaco9_3_0 : clear implicits.
Hint Unfold upaco9_3_0.
Arguments paco9_3_1 : clear implicits.
Arguments upaco9_3_1 : clear implicits.
Hint Unfold upaco9_3_1.
Arguments paco9_3_2 : clear implicits.
Arguments upaco9_3_2 : clear implicits.
Hint Unfold upaco9_3_2.

(** 1 Mutual Coinduction *)

Section Arg9_1.

Definition monotone9 (gf: rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8) :=
  forall x0 x1 x2 x3 x4 x5 x6 x7 x8 r r' (IN: gf r x0 x1 x2 x3 x4 x5 x6 x7 x8) (LE: r <9= r'), gf r' x0 x1 x2 x3 x4 x5 x6 x7 x8.

Definition _monotone9 (gf: rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8) :=
  forall r r'(LE: r <9= r'), gf r <9== gf r'.

Lemma monotone9_eq (gf: rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8) :
  monotone9 gf <-> _monotone9 gf.
Proof. unfold monotone9, _monotone9, le9. split; intros; eapply H; eassumption. Qed.

Lemma monotone9_map (gf: rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8)
      (MON: _monotone9 gf) :
  _monotone (fun R0 => uncurry9 (gf (curry9 R0))).
Proof.
  repeat_intros 3. apply uncurry_map9. apply MON; apply curry_map9; assumption.
Qed.

Variable gf : rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8.
Arguments gf : clear implicits.

Theorem _paco9_mon: _monotone9 (paco9 gf).
Proof.
  repeat_intros 3. eapply curry_map9, _paco_mon; apply uncurry_map9; assumption.
Qed.

Theorem _paco9_acc: forall
  l r (OBG: forall rr (INC: r <9== rr) (CIH: l <9== rr), l <9== paco9 gf rr),
  l <9== paco9 gf r.
Proof.
  intros. apply uncurry_adjoint1_9.
  eapply _paco_acc. intros.
  apply uncurry_adjoint1_9 in INC. apply uncurry_adjoint1_9 in CIH.
  apply uncurry_adjoint2_9.
  eapply le9_trans. eapply (OBG _ INC CIH).
  apply curry_map9.
  apply _paco_mon; try apply le1_refl; apply curry_bij1_9.
Qed.

Theorem _paco9_mult_strong: forall r,
  paco9 gf (upaco9 gf r) <9== paco9 gf r.
Proof.
  intros. apply curry_map9.
  eapply le1_trans; [| eapply _paco_mult_strong].
  apply _paco_mon; intros []; intros H; apply H.
Qed.

Theorem _paco9_fold: forall r,
  gf (upaco9 gf r) <9== paco9 gf r.
Proof.
  intros. apply uncurry_adjoint1_9.
  eapply le1_trans; [| apply _paco_fold]. apply le1_refl.
Qed.

Theorem _paco9_unfold: forall (MON: _monotone9 gf) r,
  paco9 gf r <9== gf (upaco9 gf r).
Proof.
  intros. apply curry_adjoint2_9.
  eapply _paco_unfold; apply monotone9_map; assumption.
Qed.

Theorem paco9_acc: forall
  l r (OBG: forall rr (INC: r <9= rr) (CIH: l <9= rr), l <9= paco9 gf rr),
  l <9= paco9 gf r.
Proof.
  apply _paco9_acc.
Qed.

Theorem paco9_mon: monotone9 (paco9 gf).
Proof.
  apply monotone9_eq.
  apply _paco9_mon.
Qed.

Theorem paco9_mult_strong: forall r,
  paco9 gf (upaco9 gf r) <9= paco9 gf r.
Proof.
  apply _paco9_mult_strong.
Qed.

Corollary paco9_mult: forall r,
  paco9 gf (paco9 gf r) <9= paco9 gf r.
Proof. intros; eapply paco9_mult_strong, paco9_mon; [apply PR|..]; intros; left; assumption. Qed.

Theorem paco9_fold: forall r,
  gf (upaco9 gf r) <9= paco9 gf r.
Proof.
  apply _paco9_fold.
Qed.

Theorem paco9_unfold: forall (MON: monotone9 gf) r,
  paco9 gf r <9= gf (upaco9 gf r).
Proof.
  repeat_intros 1. eapply _paco9_unfold; apply monotone9_eq; assumption.
Qed.

End Arg9_1.

Arguments paco9_acc : clear implicits.
Arguments paco9_mon : clear implicits.
Arguments paco9_mult_strong : clear implicits.
Arguments paco9_mult : clear implicits.
Arguments paco9_fold : clear implicits.
Arguments paco9_unfold : clear implicits.

Global Instance paco9_inst  (gf : rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8->_) r x0 x1 x2 x3 x4 x5 x6 x7 x8 : paco_class (paco9 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8) :=
{ pacoacc    := paco9_acc gf;
  pacomult   := paco9_mult gf;
  pacofold   := paco9_fold gf;
  pacounfold := paco9_unfold gf }.

(** 2 Mutual Coinduction *)

Section Arg9_2.

Definition monotone9_2 (gf: rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8) :=
  forall x0 x1 x2 x3 x4 x5 x6 x7 x8 r_0 r_1 r'_0 r'_1 (IN: gf r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8) (LE_0: r_0 <9= r'_0)(LE_1: r_1 <9= r'_1), gf r'_0 r'_1 x0 x1 x2 x3 x4 x5 x6 x7 x8.

Definition _monotone9_2 (gf: rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8) :=
  forall r_0 r_1 r'_0 r'_1(LE_0: r_0 <9= r'_0)(LE_1: r_1 <9= r'_1), gf r_0 r_1 <9== gf r'_0 r'_1.

Lemma monotone9_2_eq (gf: rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8) :
  monotone9_2 gf <-> _monotone9_2 gf.
Proof. unfold monotone9_2, _monotone9_2, le9. split; intros; eapply H; eassumption. Qed.

Lemma monotone9_2_map (gf: rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8)
      (MON: _monotone9_2 gf) :
  _monotone_2 (fun R0 R1 => uncurry9 (gf (curry9 R0) (curry9 R1))).
Proof.
  repeat_intros 6. apply uncurry_map9. apply MON; apply curry_map9; assumption.
Qed.

Variable gf_0 gf_1 : rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.

Theorem _paco9_2_0_mon: _monotone9_2 (paco9_2_0 gf_0 gf_1).
Proof.
  repeat_intros 6. eapply curry_map9, _paco_2_0_mon; apply uncurry_map9; assumption.
Qed.

Theorem _paco9_2_1_mon: _monotone9_2 (paco9_2_1 gf_0 gf_1).
Proof.
  repeat_intros 6. eapply curry_map9, _paco_2_1_mon; apply uncurry_map9; assumption.
Qed.

Theorem _paco9_2_0_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_0 <9== rr) (CIH: l <9== rr), l <9== paco9_2_0 gf_0 gf_1 rr r_1),
  l <9== paco9_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_9.
  eapply _paco_2_0_acc. intros.
  apply uncurry_adjoint1_9 in INC. apply uncurry_adjoint1_9 in CIH.
  apply uncurry_adjoint2_9.
  eapply le9_trans. eapply (OBG _ INC CIH).
  apply curry_map9.
  apply _paco_2_0_mon; try apply le1_refl; apply curry_bij1_9.
Qed.

Theorem _paco9_2_1_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_1 <9== rr) (CIH: l <9== rr), l <9== paco9_2_1 gf_0 gf_1 r_0 rr),
  l <9== paco9_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_9.
  eapply _paco_2_1_acc. intros.
  apply uncurry_adjoint1_9 in INC. apply uncurry_adjoint1_9 in CIH.
  apply uncurry_adjoint2_9.
  eapply le9_trans. eapply (OBG _ INC CIH).
  apply curry_map9.
  apply _paco_2_1_mon; try apply le1_refl; apply curry_bij1_9.
Qed.

Theorem _paco9_2_0_mult_strong: forall r_0 r_1,
  paco9_2_0 gf_0 gf_1 (upaco9_2_0 gf_0 gf_1 r_0 r_1) (upaco9_2_1 gf_0 gf_1 r_0 r_1) <9== paco9_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply curry_map9.
  eapply le1_trans; [| eapply _paco_2_0_mult_strong].
  apply _paco_2_0_mon; intros []; intros H; apply H.
Qed.

Theorem _paco9_2_1_mult_strong: forall r_0 r_1,
  paco9_2_1 gf_0 gf_1 (upaco9_2_0 gf_0 gf_1 r_0 r_1) (upaco9_2_1 gf_0 gf_1 r_0 r_1) <9== paco9_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply curry_map9.
  eapply le1_trans; [| eapply _paco_2_1_mult_strong].
  apply _paco_2_1_mon; intros []; intros H; apply H.
Qed.

Theorem _paco9_2_0_fold: forall r_0 r_1,
  gf_0 (upaco9_2_0 gf_0 gf_1 r_0 r_1) (upaco9_2_1 gf_0 gf_1 r_0 r_1) <9== paco9_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_9.
  eapply le1_trans; [| apply _paco_2_0_fold]. apply le1_refl.
Qed.

Theorem _paco9_2_1_fold: forall r_0 r_1,
  gf_1 (upaco9_2_0 gf_0 gf_1 r_0 r_1) (upaco9_2_1 gf_0 gf_1 r_0 r_1) <9== paco9_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_9.
  eapply le1_trans; [| apply _paco_2_1_fold]. apply le1_refl.
Qed.

Theorem _paco9_2_0_unfold: forall (MON: _monotone9_2 gf_0) (MON: _monotone9_2 gf_1) r_0 r_1,
  paco9_2_0 gf_0 gf_1 r_0 r_1 <9== gf_0 (upaco9_2_0 gf_0 gf_1 r_0 r_1) (upaco9_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  intros. apply curry_adjoint2_9.
  eapply _paco_2_0_unfold; apply monotone9_2_map; assumption.
Qed.

Theorem _paco9_2_1_unfold: forall (MON: _monotone9_2 gf_0) (MON: _monotone9_2 gf_1) r_0 r_1,
  paco9_2_1 gf_0 gf_1 r_0 r_1 <9== gf_1 (upaco9_2_0 gf_0 gf_1 r_0 r_1) (upaco9_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  intros. apply curry_adjoint2_9.
  eapply _paco_2_1_unfold; apply monotone9_2_map; assumption.
Qed.

Theorem paco9_2_0_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_0 <9= rr) (CIH: l <9= rr), l <9= paco9_2_0 gf_0 gf_1 rr r_1),
  l <9= paco9_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco9_2_0_acc.
Qed.

Theorem paco9_2_1_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_1 <9= rr) (CIH: l <9= rr), l <9= paco9_2_1 gf_0 gf_1 r_0 rr),
  l <9= paco9_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco9_2_1_acc.
Qed.

Theorem paco9_2_0_mon: monotone9_2 (paco9_2_0 gf_0 gf_1).
Proof.
  apply monotone9_2_eq.
  apply _paco9_2_0_mon.
Qed.

Theorem paco9_2_1_mon: monotone9_2 (paco9_2_1 gf_0 gf_1).
Proof.
  apply monotone9_2_eq.
  apply _paco9_2_1_mon.
Qed.

Theorem paco9_2_0_mult_strong: forall r_0 r_1,
  paco9_2_0 gf_0 gf_1 (upaco9_2_0 gf_0 gf_1 r_0 r_1) (upaco9_2_1 gf_0 gf_1 r_0 r_1) <9= paco9_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco9_2_0_mult_strong.
Qed.

Theorem paco9_2_1_mult_strong: forall r_0 r_1,
  paco9_2_1 gf_0 gf_1 (upaco9_2_0 gf_0 gf_1 r_0 r_1) (upaco9_2_1 gf_0 gf_1 r_0 r_1) <9= paco9_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco9_2_1_mult_strong.
Qed.

Corollary paco9_2_0_mult: forall r_0 r_1,
  paco9_2_0 gf_0 gf_1 (paco9_2_0 gf_0 gf_1 r_0 r_1) (paco9_2_1 gf_0 gf_1 r_0 r_1) <9= paco9_2_0 gf_0 gf_1 r_0 r_1.
Proof. intros; eapply paco9_2_0_mult_strong, paco9_2_0_mon; [apply PR|..]; intros; left; assumption. Qed.

Corollary paco9_2_1_mult: forall r_0 r_1,
  paco9_2_1 gf_0 gf_1 (paco9_2_0 gf_0 gf_1 r_0 r_1) (paco9_2_1 gf_0 gf_1 r_0 r_1) <9= paco9_2_1 gf_0 gf_1 r_0 r_1.
Proof. intros; eapply paco9_2_1_mult_strong, paco9_2_1_mon; [apply PR|..]; intros; left; assumption. Qed.

Theorem paco9_2_0_fold: forall r_0 r_1,
  gf_0 (upaco9_2_0 gf_0 gf_1 r_0 r_1) (upaco9_2_1 gf_0 gf_1 r_0 r_1) <9= paco9_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco9_2_0_fold.
Qed.

Theorem paco9_2_1_fold: forall r_0 r_1,
  gf_1 (upaco9_2_0 gf_0 gf_1 r_0 r_1) (upaco9_2_1 gf_0 gf_1 r_0 r_1) <9= paco9_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco9_2_1_fold.
Qed.

Theorem paco9_2_0_unfold: forall (MON: monotone9_2 gf_0) (MON: monotone9_2 gf_1) r_0 r_1,
  paco9_2_0 gf_0 gf_1 r_0 r_1 <9= gf_0 (upaco9_2_0 gf_0 gf_1 r_0 r_1) (upaco9_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  repeat_intros 2. eapply _paco9_2_0_unfold; apply monotone9_2_eq; assumption.
Qed.

Theorem paco9_2_1_unfold: forall (MON: monotone9_2 gf_0) (MON: monotone9_2 gf_1) r_0 r_1,
  paco9_2_1 gf_0 gf_1 r_0 r_1 <9= gf_1 (upaco9_2_0 gf_0 gf_1 r_0 r_1) (upaco9_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  repeat_intros 2. eapply _paco9_2_1_unfold; apply monotone9_2_eq; assumption.
Qed.

End Arg9_2.

Arguments paco9_2_0_acc : clear implicits.
Arguments paco9_2_1_acc : clear implicits.
Arguments paco9_2_0_mon : clear implicits.
Arguments paco9_2_1_mon : clear implicits.
Arguments paco9_2_0_mult_strong : clear implicits.
Arguments paco9_2_1_mult_strong : clear implicits.
Arguments paco9_2_0_mult : clear implicits.
Arguments paco9_2_1_mult : clear implicits.
Arguments paco9_2_0_fold : clear implicits.
Arguments paco9_2_1_fold : clear implicits.
Arguments paco9_2_0_unfold : clear implicits.
Arguments paco9_2_1_unfold : clear implicits.

Global Instance paco9_2_0_inst  (gf_0 gf_1 : rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8->_) r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 : paco_class (paco9_2_0 gf_0 gf_1 r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8) :=
{ pacoacc    := paco9_2_0_acc gf_0 gf_1;
  pacomult   := paco9_2_0_mult gf_0 gf_1;
  pacofold   := paco9_2_0_fold gf_0 gf_1;
  pacounfold := paco9_2_0_unfold gf_0 gf_1 }.

Global Instance paco9_2_1_inst  (gf_0 gf_1 : rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8->_) r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 : paco_class (paco9_2_1 gf_0 gf_1 r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8) :=
{ pacoacc    := paco9_2_1_acc gf_0 gf_1;
  pacomult   := paco9_2_1_mult gf_0 gf_1;
  pacofold   := paco9_2_1_fold gf_0 gf_1;
  pacounfold := paco9_2_1_unfold gf_0 gf_1 }.

(** 3 Mutual Coinduction *)

Section Arg9_3.

Definition monotone9_3 (gf: rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8) :=
  forall x0 x1 x2 x3 x4 x5 x6 x7 x8 r_0 r_1 r_2 r'_0 r'_1 r'_2 (IN: gf r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8) (LE_0: r_0 <9= r'_0)(LE_1: r_1 <9= r'_1)(LE_2: r_2 <9= r'_2), gf r'_0 r'_1 r'_2 x0 x1 x2 x3 x4 x5 x6 x7 x8.

Definition _monotone9_3 (gf: rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8) :=
  forall r_0 r_1 r_2 r'_0 r'_1 r'_2(LE_0: r_0 <9= r'_0)(LE_1: r_1 <9= r'_1)(LE_2: r_2 <9= r'_2), gf r_0 r_1 r_2 <9== gf r'_0 r'_1 r'_2.

Lemma monotone9_3_eq (gf: rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8) :
  monotone9_3 gf <-> _monotone9_3 gf.
Proof. unfold monotone9_3, _monotone9_3, le9. split; intros; eapply H; eassumption. Qed.

Lemma monotone9_3_map (gf: rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8)
      (MON: _monotone9_3 gf) :
  _monotone_3 (fun R0 R1 R2 => uncurry9 (gf (curry9 R0) (curry9 R1) (curry9 R2))).
Proof.
  repeat_intros 9. apply uncurry_map9. apply MON; apply curry_map9; assumption.
Qed.

Variable gf_0 gf_1 gf_2 : rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.
Arguments gf_2 : clear implicits.

Theorem _paco9_3_0_mon: _monotone9_3 (paco9_3_0 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 9. eapply curry_map9, _paco_3_0_mon; apply uncurry_map9; assumption.
Qed.

Theorem _paco9_3_1_mon: _monotone9_3 (paco9_3_1 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 9. eapply curry_map9, _paco_3_1_mon; apply uncurry_map9; assumption.
Qed.

Theorem _paco9_3_2_mon: _monotone9_3 (paco9_3_2 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 9. eapply curry_map9, _paco_3_2_mon; apply uncurry_map9; assumption.
Qed.

Theorem _paco9_3_0_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_0 <9== rr) (CIH: l <9== rr), l <9== paco9_3_0 gf_0 gf_1 gf_2 rr r_1 r_2),
  l <9== paco9_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_9.
  eapply _paco_3_0_acc. intros.
  apply uncurry_adjoint1_9 in INC. apply uncurry_adjoint1_9 in CIH.
  apply uncurry_adjoint2_9.
  eapply le9_trans. eapply (OBG _ INC CIH).
  apply curry_map9.
  apply _paco_3_0_mon; try apply le1_refl; apply curry_bij1_9.
Qed.

Theorem _paco9_3_1_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_1 <9== rr) (CIH: l <9== rr), l <9== paco9_3_1 gf_0 gf_1 gf_2 r_0 rr r_2),
  l <9== paco9_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_9.
  eapply _paco_3_1_acc. intros.
  apply uncurry_adjoint1_9 in INC. apply uncurry_adjoint1_9 in CIH.
  apply uncurry_adjoint2_9.
  eapply le9_trans. eapply (OBG _ INC CIH).
  apply curry_map9.
  apply _paco_3_1_mon; try apply le1_refl; apply curry_bij1_9.
Qed.

Theorem _paco9_3_2_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_2 <9== rr) (CIH: l <9== rr), l <9== paco9_3_2 gf_0 gf_1 gf_2 r_0 r_1 rr),
  l <9== paco9_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_9.
  eapply _paco_3_2_acc. intros.
  apply uncurry_adjoint1_9 in INC. apply uncurry_adjoint1_9 in CIH.
  apply uncurry_adjoint2_9.
  eapply le9_trans. eapply (OBG _ INC CIH).
  apply curry_map9.
  apply _paco_3_2_mon; try apply le1_refl; apply curry_bij1_9.
Qed.

Theorem _paco9_3_0_mult_strong: forall r_0 r_1 r_2,
  paco9_3_0 gf_0 gf_1 gf_2 (upaco9_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco9_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco9_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <9== paco9_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply curry_map9.
  eapply le1_trans; [| eapply _paco_3_0_mult_strong].
  apply _paco_3_0_mon; intros []; intros H; apply H.
Qed.

Theorem _paco9_3_1_mult_strong: forall r_0 r_1 r_2,
  paco9_3_1 gf_0 gf_1 gf_2 (upaco9_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco9_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco9_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <9== paco9_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply curry_map9.
  eapply le1_trans; [| eapply _paco_3_1_mult_strong].
  apply _paco_3_1_mon; intros []; intros H; apply H.
Qed.

Theorem _paco9_3_2_mult_strong: forall r_0 r_1 r_2,
  paco9_3_2 gf_0 gf_1 gf_2 (upaco9_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco9_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco9_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <9== paco9_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply curry_map9.
  eapply le1_trans; [| eapply _paco_3_2_mult_strong].
  apply _paco_3_2_mon; intros []; intros H; apply H.
Qed.

Theorem _paco9_3_0_fold: forall r_0 r_1 r_2,
  gf_0 (upaco9_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco9_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco9_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <9== paco9_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_9.
  eapply le1_trans; [| apply _paco_3_0_fold]. apply le1_refl.
Qed.

Theorem _paco9_3_1_fold: forall r_0 r_1 r_2,
  gf_1 (upaco9_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco9_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco9_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <9== paco9_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_9.
  eapply le1_trans; [| apply _paco_3_1_fold]. apply le1_refl.
Qed.

Theorem _paco9_3_2_fold: forall r_0 r_1 r_2,
  gf_2 (upaco9_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco9_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco9_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <9== paco9_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_9.
  eapply le1_trans; [| apply _paco_3_2_fold]. apply le1_refl.
Qed.

Theorem _paco9_3_0_unfold: forall (MON: _monotone9_3 gf_0) (MON: _monotone9_3 gf_1) (MON: _monotone9_3 gf_2) r_0 r_1 r_2,
  paco9_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 <9== gf_0 (upaco9_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco9_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco9_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  intros. apply curry_adjoint2_9.
  eapply _paco_3_0_unfold; apply monotone9_3_map; assumption.
Qed.

Theorem _paco9_3_1_unfold: forall (MON: _monotone9_3 gf_0) (MON: _monotone9_3 gf_1) (MON: _monotone9_3 gf_2) r_0 r_1 r_2,
  paco9_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 <9== gf_1 (upaco9_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco9_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco9_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  intros. apply curry_adjoint2_9.
  eapply _paco_3_1_unfold; apply monotone9_3_map; assumption.
Qed.

Theorem _paco9_3_2_unfold: forall (MON: _monotone9_3 gf_0) (MON: _monotone9_3 gf_1) (MON: _monotone9_3 gf_2) r_0 r_1 r_2,
  paco9_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 <9== gf_2 (upaco9_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco9_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco9_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  intros. apply curry_adjoint2_9.
  eapply _paco_3_2_unfold; apply monotone9_3_map; assumption.
Qed.

Theorem paco9_3_0_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_0 <9= rr) (CIH: l <9= rr), l <9= paco9_3_0 gf_0 gf_1 gf_2 rr r_1 r_2),
  l <9= paco9_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco9_3_0_acc.
Qed.

Theorem paco9_3_1_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_1 <9= rr) (CIH: l <9= rr), l <9= paco9_3_1 gf_0 gf_1 gf_2 r_0 rr r_2),
  l <9= paco9_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco9_3_1_acc.
Qed.

Theorem paco9_3_2_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_2 <9= rr) (CIH: l <9= rr), l <9= paco9_3_2 gf_0 gf_1 gf_2 r_0 r_1 rr),
  l <9= paco9_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco9_3_2_acc.
Qed.

Theorem paco9_3_0_mon: monotone9_3 (paco9_3_0 gf_0 gf_1 gf_2).
Proof.
  apply monotone9_3_eq.
  apply _paco9_3_0_mon.
Qed.

Theorem paco9_3_1_mon: monotone9_3 (paco9_3_1 gf_0 gf_1 gf_2).
Proof.
  apply monotone9_3_eq.
  apply _paco9_3_1_mon.
Qed.

Theorem paco9_3_2_mon: monotone9_3 (paco9_3_2 gf_0 gf_1 gf_2).
Proof.
  apply monotone9_3_eq.
  apply _paco9_3_2_mon.
Qed.

Theorem paco9_3_0_mult_strong: forall r_0 r_1 r_2,
  paco9_3_0 gf_0 gf_1 gf_2 (upaco9_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco9_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco9_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <9= paco9_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco9_3_0_mult_strong.
Qed.

Theorem paco9_3_1_mult_strong: forall r_0 r_1 r_2,
  paco9_3_1 gf_0 gf_1 gf_2 (upaco9_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco9_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco9_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <9= paco9_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco9_3_1_mult_strong.
Qed.

Theorem paco9_3_2_mult_strong: forall r_0 r_1 r_2,
  paco9_3_2 gf_0 gf_1 gf_2 (upaco9_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco9_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco9_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <9= paco9_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco9_3_2_mult_strong.
Qed.

Corollary paco9_3_0_mult: forall r_0 r_1 r_2,
  paco9_3_0 gf_0 gf_1 gf_2 (paco9_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco9_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco9_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <9= paco9_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco9_3_0_mult_strong, paco9_3_0_mon; [apply PR|..]; intros; left; assumption. Qed.

Corollary paco9_3_1_mult: forall r_0 r_1 r_2,
  paco9_3_1 gf_0 gf_1 gf_2 (paco9_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco9_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco9_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <9= paco9_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco9_3_1_mult_strong, paco9_3_1_mon; [apply PR|..]; intros; left; assumption. Qed.

Corollary paco9_3_2_mult: forall r_0 r_1 r_2,
  paco9_3_2 gf_0 gf_1 gf_2 (paco9_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco9_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco9_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <9= paco9_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco9_3_2_mult_strong, paco9_3_2_mon; [apply PR|..]; intros; left; assumption. Qed.

Theorem paco9_3_0_fold: forall r_0 r_1 r_2,
  gf_0 (upaco9_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco9_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco9_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <9= paco9_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco9_3_0_fold.
Qed.

Theorem paco9_3_1_fold: forall r_0 r_1 r_2,
  gf_1 (upaco9_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco9_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco9_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <9= paco9_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco9_3_1_fold.
Qed.

Theorem paco9_3_2_fold: forall r_0 r_1 r_2,
  gf_2 (upaco9_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco9_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco9_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <9= paco9_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco9_3_2_fold.
Qed.

Theorem paco9_3_0_unfold: forall (MON: monotone9_3 gf_0) (MON: monotone9_3 gf_1) (MON: monotone9_3 gf_2) r_0 r_1 r_2,
  paco9_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 <9= gf_0 (upaco9_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco9_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco9_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  repeat_intros 3. eapply _paco9_3_0_unfold; apply monotone9_3_eq; assumption.
Qed.

Theorem paco9_3_1_unfold: forall (MON: monotone9_3 gf_0) (MON: monotone9_3 gf_1) (MON: monotone9_3 gf_2) r_0 r_1 r_2,
  paco9_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 <9= gf_1 (upaco9_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco9_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco9_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  repeat_intros 3. eapply _paco9_3_1_unfold; apply monotone9_3_eq; assumption.
Qed.

Theorem paco9_3_2_unfold: forall (MON: monotone9_3 gf_0) (MON: monotone9_3 gf_1) (MON: monotone9_3 gf_2) r_0 r_1 r_2,
  paco9_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 <9= gf_2 (upaco9_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco9_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco9_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  repeat_intros 3. eapply _paco9_3_2_unfold; apply monotone9_3_eq; assumption.
Qed.

End Arg9_3.

Arguments paco9_3_0_acc : clear implicits.
Arguments paco9_3_1_acc : clear implicits.
Arguments paco9_3_2_acc : clear implicits.
Arguments paco9_3_0_mon : clear implicits.
Arguments paco9_3_1_mon : clear implicits.
Arguments paco9_3_2_mon : clear implicits.
Arguments paco9_3_0_mult_strong : clear implicits.
Arguments paco9_3_1_mult_strong : clear implicits.
Arguments paco9_3_2_mult_strong : clear implicits.
Arguments paco9_3_0_mult : clear implicits.
Arguments paco9_3_1_mult : clear implicits.
Arguments paco9_3_2_mult : clear implicits.
Arguments paco9_3_0_fold : clear implicits.
Arguments paco9_3_1_fold : clear implicits.
Arguments paco9_3_2_fold : clear implicits.
Arguments paco9_3_0_unfold : clear implicits.
Arguments paco9_3_1_unfold : clear implicits.
Arguments paco9_3_2_unfold : clear implicits.

Global Instance paco9_3_0_inst  (gf_0 gf_1 gf_2 : rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 : paco_class (paco9_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8) :=
{ pacoacc    := paco9_3_0_acc gf_0 gf_1 gf_2;
  pacomult   := paco9_3_0_mult gf_0 gf_1 gf_2;
  pacofold   := paco9_3_0_fold gf_0 gf_1 gf_2;
  pacounfold := paco9_3_0_unfold gf_0 gf_1 gf_2 }.

Global Instance paco9_3_1_inst  (gf_0 gf_1 gf_2 : rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 : paco_class (paco9_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8) :=
{ pacoacc    := paco9_3_1_acc gf_0 gf_1 gf_2;
  pacomult   := paco9_3_1_mult gf_0 gf_1 gf_2;
  pacofold   := paco9_3_1_fold gf_0 gf_1 gf_2;
  pacounfold := paco9_3_1_unfold gf_0 gf_1 gf_2 }.

Global Instance paco9_3_2_inst  (gf_0 gf_1 gf_2 : rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 : paco_class (paco9_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8) :=
{ pacoacc    := paco9_3_2_acc gf_0 gf_1 gf_2;
  pacomult   := paco9_3_2_mult gf_0 gf_1 gf_2;
  pacofold   := paco9_3_2_fold gf_0 gf_1 gf_2;
  pacounfold := paco9_3_2_unfold gf_0 gf_1 gf_2 }.

End PACO9.

Global Opaque paco9.

Hint Unfold upaco9.
Hint Resolve paco9_fold.
Hint Unfold monotone9.

Global Opaque paco9_2_0.
Global Opaque paco9_2_1.

Hint Unfold upaco9_2_0.
Hint Unfold upaco9_2_1.
Hint Resolve paco9_2_0_fold.
Hint Resolve paco9_2_1_fold.
Hint Unfold monotone9_2.

Global Opaque paco9_3_0.
Global Opaque paco9_3_1.
Global Opaque paco9_3_2.

Hint Unfold upaco9_3_0.
Hint Unfold upaco9_3_1.
Hint Unfold upaco9_3_2.
Hint Resolve paco9_3_0_fold.
Hint Resolve paco9_3_1_fold.
Hint Resolve paco9_3_2_fold.
Hint Unfold monotone9_3.

