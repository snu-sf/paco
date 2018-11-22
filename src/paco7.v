Require Export paconotation pacotacuser.
Require Import paconotation_internal pacotac pacon.
Set Implicit Arguments.

Section PACO7.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.

Record sig7T :=
  exist7T { 
      proj7T0: @T0;
      proj7T1: @T1 proj7T0;
      proj7T2: @T2 proj7T0 proj7T1;
      proj7T3: @T3 proj7T0 proj7T1 proj7T2;
      proj7T4: @T4 proj7T0 proj7T1 proj7T2 proj7T3;
      proj7T5: @T5 proj7T0 proj7T1 proj7T2 proj7T3 proj7T4;
      proj7T6: @T6 proj7T0 proj7T1 proj7T2 proj7T3 proj7T4 proj7T5;
    }.

Definition uncurry7 (R: rel7 T0 T1 T2 T3 T4 T5 T6): rel1 sig7T := fun x => R (proj7T0 x) (proj7T1 x) (proj7T2 x) (proj7T3 x) (proj7T4 x) (proj7T5 x) (proj7T6 x).

Definition curry7 (R: rel1 sig7T): rel7 T0 T1 T2 T3 T4 T5 T6 :=
  fun x0 x1 x2 x3 x4 x5 x6 => R (exist7T x6).

Lemma uncurry_map7 r0 r1 (LE : r0 <7== r1) : uncurry7 r0 <1== uncurry7 r1.
Proof. intros [] H. apply LE. apply H. Qed.

Lemma uncurry_map_rev7 r0 r1 (LE: uncurry7 r0 <1== uncurry7 r1) : r0 <7== r1.
Proof.
  repeat_intros 7. intros H. apply (LE (exist7T x6) H).
Qed.

Lemma curry_map7 r0 r1 (LE: r0 <1== r1) : curry7 r0 <7== curry7 r1.
Proof. 
  repeat_intros 7. intros H. apply (LE (exist7T x6) H).
Qed.

Lemma curry_map_rev7 r0 r1 (LE: curry7 r0 <7== curry7 r1) : r0 <1== r1.
Proof. 
  intros [] H. apply LE. apply H.
Qed.

Lemma uncurry_bij1_7 r : curry7 (uncurry7 r) <7== r.
Proof. unfold le7. repeat_intros 7. intros H. apply H. Qed.

Lemma uncurry_bij2_7 r : r <7== curry7 (uncurry7 r).
Proof. unfold le7. repeat_intros 7. intros H. apply H. Qed.

Lemma curry_bij1_7 r : uncurry7 (curry7 r) <1== r.
Proof. intros []. intro H. apply H. Qed.

Lemma curry_bij2_7 r : r <1== uncurry7 (curry7 r).
Proof. intros []. intro H. apply H. Qed.

Lemma uncurry_adjoint1_7 r0 r1 (LE: uncurry7 r0 <1== r1) : r0 <7== curry7 r1.
Proof.
  apply uncurry_map_rev7. eapply le1_trans; [apply LE|]. apply curry_bij2_7.
Qed.

Lemma uncurry_adjoint2_7 r0 r1 (LE: r0 <7== curry7 r1) : uncurry7 r0 <1== r1.
Proof.
  apply curry_map_rev7. eapply le7_trans; [|apply LE]. apply uncurry_bij2_7.
Qed.

Lemma curry_adjoint1_7 r0 r1 (LE: curry7 r0 <7== r1) : r0 <1== uncurry7 r1.
Proof.
  apply curry_map_rev7. eapply le7_trans; [apply LE|]. apply uncurry_bij2_7.
Qed.

Lemma curry_adjoint2_7 r0 r1 (LE: r0 <1== uncurry7 r1) : curry7 r0 <7== r1.
Proof.
  apply uncurry_map_rev7. eapply le1_trans; [|apply LE]. apply curry_bij1_7.
Qed.

(** ** Predicates of Arity 7
*)

Section Arg7_def.
Variable gf : rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6.
Arguments gf : clear implicits.

Definition paco7( r: rel7 T0 T1 T2 T3 T4 T5 T6) : rel7 T0 T1 T2 T3 T4 T5 T6 :=
  curry7 (paco (fun R0 => uncurry7 (gf (curry7 R0))) (uncurry7 r)).

Definition upaco7( r: rel7 T0 T1 T2 T3 T4 T5 T6) := paco7 r \7/ r.
End Arg7_def.
Arguments paco7 : clear implicits.
Arguments upaco7 : clear implicits.
Hint Unfold upaco7.

Section Arg7_2_def.
Variable gf_0 gf_1 : rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.

Definition paco7_2_0( r_0 r_1: rel7 T0 T1 T2 T3 T4 T5 T6) : rel7 T0 T1 T2 T3 T4 T5 T6 :=
  curry7 (paco_2_0 (fun R0 R1 => uncurry7 (gf_0 (curry7 R0) (curry7 R1))) (fun R0 R1 => uncurry7 (gf_1 (curry7 R0) (curry7 R1))) (uncurry7 r_0) (uncurry7 r_1)).

Definition paco7_2_1( r_0 r_1: rel7 T0 T1 T2 T3 T4 T5 T6) : rel7 T0 T1 T2 T3 T4 T5 T6 :=
  curry7 (paco_2_1 (fun R0 R1 => uncurry7 (gf_0 (curry7 R0) (curry7 R1))) (fun R0 R1 => uncurry7 (gf_1 (curry7 R0) (curry7 R1))) (uncurry7 r_0) (uncurry7 r_1)).

Definition upaco7_2_0( r_0 r_1: rel7 T0 T1 T2 T3 T4 T5 T6) := paco7_2_0 r_0 r_1 \7/ r_0.
Definition upaco7_2_1( r_0 r_1: rel7 T0 T1 T2 T3 T4 T5 T6) := paco7_2_1 r_0 r_1 \7/ r_1.
End Arg7_2_def.
Arguments paco7_2_0 : clear implicits.
Arguments upaco7_2_0 : clear implicits.
Hint Unfold upaco7_2_0.
Arguments paco7_2_1 : clear implicits.
Arguments upaco7_2_1 : clear implicits.
Hint Unfold upaco7_2_1.

Section Arg7_3_def.
Variable gf_0 gf_1 gf_2 : rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.
Arguments gf_2 : clear implicits.

Definition paco7_3_0( r_0 r_1 r_2: rel7 T0 T1 T2 T3 T4 T5 T6) : rel7 T0 T1 T2 T3 T4 T5 T6 :=
  curry7 (paco_3_0 (fun R0 R1 R2 => uncurry7 (gf_0 (curry7 R0) (curry7 R1) (curry7 R2))) (fun R0 R1 R2 => uncurry7 (gf_1 (curry7 R0) (curry7 R1) (curry7 R2))) (fun R0 R1 R2 => uncurry7 (gf_2 (curry7 R0) (curry7 R1) (curry7 R2))) (uncurry7 r_0) (uncurry7 r_1) (uncurry7 r_2)).

Definition paco7_3_1( r_0 r_1 r_2: rel7 T0 T1 T2 T3 T4 T5 T6) : rel7 T0 T1 T2 T3 T4 T5 T6 :=
  curry7 (paco_3_1 (fun R0 R1 R2 => uncurry7 (gf_0 (curry7 R0) (curry7 R1) (curry7 R2))) (fun R0 R1 R2 => uncurry7 (gf_1 (curry7 R0) (curry7 R1) (curry7 R2))) (fun R0 R1 R2 => uncurry7 (gf_2 (curry7 R0) (curry7 R1) (curry7 R2))) (uncurry7 r_0) (uncurry7 r_1) (uncurry7 r_2)).

Definition paco7_3_2( r_0 r_1 r_2: rel7 T0 T1 T2 T3 T4 T5 T6) : rel7 T0 T1 T2 T3 T4 T5 T6 :=
  curry7 (paco_3_2 (fun R0 R1 R2 => uncurry7 (gf_0 (curry7 R0) (curry7 R1) (curry7 R2))) (fun R0 R1 R2 => uncurry7 (gf_1 (curry7 R0) (curry7 R1) (curry7 R2))) (fun R0 R1 R2 => uncurry7 (gf_2 (curry7 R0) (curry7 R1) (curry7 R2))) (uncurry7 r_0) (uncurry7 r_1) (uncurry7 r_2)).

Definition upaco7_3_0( r_0 r_1 r_2: rel7 T0 T1 T2 T3 T4 T5 T6) := paco7_3_0 r_0 r_1 r_2 \7/ r_0.
Definition upaco7_3_1( r_0 r_1 r_2: rel7 T0 T1 T2 T3 T4 T5 T6) := paco7_3_1 r_0 r_1 r_2 \7/ r_1.
Definition upaco7_3_2( r_0 r_1 r_2: rel7 T0 T1 T2 T3 T4 T5 T6) := paco7_3_2 r_0 r_1 r_2 \7/ r_2.
End Arg7_3_def.
Arguments paco7_3_0 : clear implicits.
Arguments upaco7_3_0 : clear implicits.
Hint Unfold upaco7_3_0.
Arguments paco7_3_1 : clear implicits.
Arguments upaco7_3_1 : clear implicits.
Hint Unfold upaco7_3_1.
Arguments paco7_3_2 : clear implicits.
Arguments upaco7_3_2 : clear implicits.
Hint Unfold upaco7_3_2.

(** 1 Mutual Coinduction *)

Section Arg7_1.

Definition monotone7 (gf: rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6) :=
  forall x0 x1 x2 x3 x4 x5 x6 r r' (IN: gf r x0 x1 x2 x3 x4 x5 x6) (LE: r <7= r'), gf r' x0 x1 x2 x3 x4 x5 x6.

Definition _monotone7 (gf: rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6) :=
  forall r r'(LE: r <7= r'), gf r <7== gf r'.

Lemma monotone7_eq (gf: rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6) :
  monotone7 gf <-> _monotone7 gf.
Proof. unfold monotone7, _monotone7, le7. split; intros; eapply H; eassumption. Qed.

Lemma monotone7_map (gf: rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6)
      (MON: _monotone7 gf) :
  _monotone (fun R0 => uncurry7 (gf (curry7 R0))).
Proof.
  repeat_intros 3. apply uncurry_map7. apply MON; apply curry_map7; assumption.
Qed.

Variable gf : rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6.
Arguments gf : clear implicits.

Theorem _paco7_mon: _monotone7 (paco7 gf).
Proof.
  repeat_intros 3. eapply curry_map7, _paco_mon; apply uncurry_map7; assumption.
Qed.

Theorem _paco7_acc: forall
  l r (OBG: forall rr (INC: r <7== rr) (CIH: l <7== rr), l <7== paco7 gf rr),
  l <7== paco7 gf r.
Proof.
  intros. apply uncurry_adjoint1_7.
  eapply _paco_acc. intros.
  apply uncurry_adjoint1_7 in INC. apply uncurry_adjoint1_7 in CIH.
  apply uncurry_adjoint2_7.
  eapply le7_trans. eapply (OBG _ INC CIH).
  apply curry_map7.
  apply _paco_mon; try apply le1_refl; apply curry_bij1_7.
Qed.

Theorem _paco7_mult_strong: forall r,
  paco7 gf (upaco7 gf r) <7== paco7 gf r.
Proof.
  intros. apply curry_map7.
  eapply le1_trans; [| eapply _paco_mult_strong].
  apply _paco_mon; intros []; intros H; apply H.
Qed.

Theorem _paco7_fold: forall r,
  gf (upaco7 gf r) <7== paco7 gf r.
Proof.
  intros. apply uncurry_adjoint1_7.
  eapply le1_trans; [| apply _paco_fold]. apply le1_refl.
Qed.

Theorem _paco7_unfold: forall (MON: _monotone7 gf) r,
  paco7 gf r <7== gf (upaco7 gf r).
Proof.
  intros. apply curry_adjoint2_7.
  eapply _paco_unfold; apply monotone7_map; assumption.
Qed.

Theorem paco7_acc: forall
  l r (OBG: forall rr (INC: r <7= rr) (CIH: l <7= rr), l <7= paco7 gf rr),
  l <7= paco7 gf r.
Proof.
  apply _paco7_acc.
Qed.

Theorem paco7_mon: monotone7 (paco7 gf).
Proof.
  apply monotone7_eq.
  apply _paco7_mon.
Qed.

Theorem paco7_mult_strong: forall r,
  paco7 gf (upaco7 gf r) <7= paco7 gf r.
Proof.
  apply _paco7_mult_strong.
Qed.

Corollary paco7_mult: forall r,
  paco7 gf (paco7 gf r) <7= paco7 gf r.
Proof. intros; eapply paco7_mult_strong, paco7_mon; [apply PR|..]; intros; left; assumption. Qed.

Theorem paco7_fold: forall r,
  gf (upaco7 gf r) <7= paco7 gf r.
Proof.
  apply _paco7_fold.
Qed.

Theorem paco7_unfold: forall (MON: monotone7 gf) r,
  paco7 gf r <7= gf (upaco7 gf r).
Proof.
  repeat_intros 1. eapply _paco7_unfold; apply monotone7_eq; assumption.
Qed.

End Arg7_1.

Arguments paco7_acc : clear implicits.
Arguments paco7_mon : clear implicits.
Arguments paco7_mult_strong : clear implicits.
Arguments paco7_mult : clear implicits.
Arguments paco7_fold : clear implicits.
Arguments paco7_unfold : clear implicits.

Global Instance paco7_inst  (gf : rel7 T0 T1 T2 T3 T4 T5 T6->_) r x0 x1 x2 x3 x4 x5 x6 : paco_class (paco7 gf r x0 x1 x2 x3 x4 x5 x6) :=
{ pacoacc    := paco7_acc gf;
  pacomult   := paco7_mult gf;
  pacofold   := paco7_fold gf;
  pacounfold := paco7_unfold gf }.

(** 2 Mutual Coinduction *)

Section Arg7_2.

Definition monotone7_2 (gf: rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6) :=
  forall x0 x1 x2 x3 x4 x5 x6 r_0 r_1 r'_0 r'_1 (IN: gf r_0 r_1 x0 x1 x2 x3 x4 x5 x6) (LE_0: r_0 <7= r'_0)(LE_1: r_1 <7= r'_1), gf r'_0 r'_1 x0 x1 x2 x3 x4 x5 x6.

Definition _monotone7_2 (gf: rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6) :=
  forall r_0 r_1 r'_0 r'_1(LE_0: r_0 <7= r'_0)(LE_1: r_1 <7= r'_1), gf r_0 r_1 <7== gf r'_0 r'_1.

Lemma monotone7_2_eq (gf: rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6) :
  monotone7_2 gf <-> _monotone7_2 gf.
Proof. unfold monotone7_2, _monotone7_2, le7. split; intros; eapply H; eassumption. Qed.

Lemma monotone7_2_map (gf: rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6)
      (MON: _monotone7_2 gf) :
  _monotone_2 (fun R0 R1 => uncurry7 (gf (curry7 R0) (curry7 R1))).
Proof.
  repeat_intros 6. apply uncurry_map7. apply MON; apply curry_map7; assumption.
Qed.

Variable gf_0 gf_1 : rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.

Theorem _paco7_2_0_mon: _monotone7_2 (paco7_2_0 gf_0 gf_1).
Proof.
  repeat_intros 6. eapply curry_map7, _paco_2_0_mon; apply uncurry_map7; assumption.
Qed.

Theorem _paco7_2_1_mon: _monotone7_2 (paco7_2_1 gf_0 gf_1).
Proof.
  repeat_intros 6. eapply curry_map7, _paco_2_1_mon; apply uncurry_map7; assumption.
Qed.

Theorem _paco7_2_0_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_0 <7== rr) (CIH: l <7== rr), l <7== paco7_2_0 gf_0 gf_1 rr r_1),
  l <7== paco7_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_7.
  eapply _paco_2_0_acc. intros.
  apply uncurry_adjoint1_7 in INC. apply uncurry_adjoint1_7 in CIH.
  apply uncurry_adjoint2_7.
  eapply le7_trans. eapply (OBG _ INC CIH).
  apply curry_map7.
  apply _paco_2_0_mon; try apply le1_refl; apply curry_bij1_7.
Qed.

Theorem _paco7_2_1_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_1 <7== rr) (CIH: l <7== rr), l <7== paco7_2_1 gf_0 gf_1 r_0 rr),
  l <7== paco7_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_7.
  eapply _paco_2_1_acc. intros.
  apply uncurry_adjoint1_7 in INC. apply uncurry_adjoint1_7 in CIH.
  apply uncurry_adjoint2_7.
  eapply le7_trans. eapply (OBG _ INC CIH).
  apply curry_map7.
  apply _paco_2_1_mon; try apply le1_refl; apply curry_bij1_7.
Qed.

Theorem _paco7_2_0_mult_strong: forall r_0 r_1,
  paco7_2_0 gf_0 gf_1 (upaco7_2_0 gf_0 gf_1 r_0 r_1) (upaco7_2_1 gf_0 gf_1 r_0 r_1) <7== paco7_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply curry_map7.
  eapply le1_trans; [| eapply _paco_2_0_mult_strong].
  apply _paco_2_0_mon; intros []; intros H; apply H.
Qed.

Theorem _paco7_2_1_mult_strong: forall r_0 r_1,
  paco7_2_1 gf_0 gf_1 (upaco7_2_0 gf_0 gf_1 r_0 r_1) (upaco7_2_1 gf_0 gf_1 r_0 r_1) <7== paco7_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply curry_map7.
  eapply le1_trans; [| eapply _paco_2_1_mult_strong].
  apply _paco_2_1_mon; intros []; intros H; apply H.
Qed.

Theorem _paco7_2_0_fold: forall r_0 r_1,
  gf_0 (upaco7_2_0 gf_0 gf_1 r_0 r_1) (upaco7_2_1 gf_0 gf_1 r_0 r_1) <7== paco7_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_7.
  eapply le1_trans; [| apply _paco_2_0_fold]. apply le1_refl.
Qed.

Theorem _paco7_2_1_fold: forall r_0 r_1,
  gf_1 (upaco7_2_0 gf_0 gf_1 r_0 r_1) (upaco7_2_1 gf_0 gf_1 r_0 r_1) <7== paco7_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_7.
  eapply le1_trans; [| apply _paco_2_1_fold]. apply le1_refl.
Qed.

Theorem _paco7_2_0_unfold: forall (MON: _monotone7_2 gf_0) (MON: _monotone7_2 gf_1) r_0 r_1,
  paco7_2_0 gf_0 gf_1 r_0 r_1 <7== gf_0 (upaco7_2_0 gf_0 gf_1 r_0 r_1) (upaco7_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  intros. apply curry_adjoint2_7.
  eapply _paco_2_0_unfold; apply monotone7_2_map; assumption.
Qed.

Theorem _paco7_2_1_unfold: forall (MON: _monotone7_2 gf_0) (MON: _monotone7_2 gf_1) r_0 r_1,
  paco7_2_1 gf_0 gf_1 r_0 r_1 <7== gf_1 (upaco7_2_0 gf_0 gf_1 r_0 r_1) (upaco7_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  intros. apply curry_adjoint2_7.
  eapply _paco_2_1_unfold; apply monotone7_2_map; assumption.
Qed.

Theorem paco7_2_0_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_0 <7= rr) (CIH: l <7= rr), l <7= paco7_2_0 gf_0 gf_1 rr r_1),
  l <7= paco7_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco7_2_0_acc.
Qed.

Theorem paco7_2_1_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_1 <7= rr) (CIH: l <7= rr), l <7= paco7_2_1 gf_0 gf_1 r_0 rr),
  l <7= paco7_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco7_2_1_acc.
Qed.

Theorem paco7_2_0_mon: monotone7_2 (paco7_2_0 gf_0 gf_1).
Proof.
  apply monotone7_2_eq.
  apply _paco7_2_0_mon.
Qed.

Theorem paco7_2_1_mon: monotone7_2 (paco7_2_1 gf_0 gf_1).
Proof.
  apply monotone7_2_eq.
  apply _paco7_2_1_mon.
Qed.

Theorem paco7_2_0_mult_strong: forall r_0 r_1,
  paco7_2_0 gf_0 gf_1 (upaco7_2_0 gf_0 gf_1 r_0 r_1) (upaco7_2_1 gf_0 gf_1 r_0 r_1) <7= paco7_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco7_2_0_mult_strong.
Qed.

Theorem paco7_2_1_mult_strong: forall r_0 r_1,
  paco7_2_1 gf_0 gf_1 (upaco7_2_0 gf_0 gf_1 r_0 r_1) (upaco7_2_1 gf_0 gf_1 r_0 r_1) <7= paco7_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco7_2_1_mult_strong.
Qed.

Corollary paco7_2_0_mult: forall r_0 r_1,
  paco7_2_0 gf_0 gf_1 (paco7_2_0 gf_0 gf_1 r_0 r_1) (paco7_2_1 gf_0 gf_1 r_0 r_1) <7= paco7_2_0 gf_0 gf_1 r_0 r_1.
Proof. intros; eapply paco7_2_0_mult_strong, paco7_2_0_mon; [apply PR|..]; intros; left; assumption. Qed.

Corollary paco7_2_1_mult: forall r_0 r_1,
  paco7_2_1 gf_0 gf_1 (paco7_2_0 gf_0 gf_1 r_0 r_1) (paco7_2_1 gf_0 gf_1 r_0 r_1) <7= paco7_2_1 gf_0 gf_1 r_0 r_1.
Proof. intros; eapply paco7_2_1_mult_strong, paco7_2_1_mon; [apply PR|..]; intros; left; assumption. Qed.

Theorem paco7_2_0_fold: forall r_0 r_1,
  gf_0 (upaco7_2_0 gf_0 gf_1 r_0 r_1) (upaco7_2_1 gf_0 gf_1 r_0 r_1) <7= paco7_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco7_2_0_fold.
Qed.

Theorem paco7_2_1_fold: forall r_0 r_1,
  gf_1 (upaco7_2_0 gf_0 gf_1 r_0 r_1) (upaco7_2_1 gf_0 gf_1 r_0 r_1) <7= paco7_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco7_2_1_fold.
Qed.

Theorem paco7_2_0_unfold: forall (MON: monotone7_2 gf_0) (MON: monotone7_2 gf_1) r_0 r_1,
  paco7_2_0 gf_0 gf_1 r_0 r_1 <7= gf_0 (upaco7_2_0 gf_0 gf_1 r_0 r_1) (upaco7_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  repeat_intros 2. eapply _paco7_2_0_unfold; apply monotone7_2_eq; assumption.
Qed.

Theorem paco7_2_1_unfold: forall (MON: monotone7_2 gf_0) (MON: monotone7_2 gf_1) r_0 r_1,
  paco7_2_1 gf_0 gf_1 r_0 r_1 <7= gf_1 (upaco7_2_0 gf_0 gf_1 r_0 r_1) (upaco7_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  repeat_intros 2. eapply _paco7_2_1_unfold; apply monotone7_2_eq; assumption.
Qed.

End Arg7_2.

Arguments paco7_2_0_acc : clear implicits.
Arguments paco7_2_1_acc : clear implicits.
Arguments paco7_2_0_mon : clear implicits.
Arguments paco7_2_1_mon : clear implicits.
Arguments paco7_2_0_mult_strong : clear implicits.
Arguments paco7_2_1_mult_strong : clear implicits.
Arguments paco7_2_0_mult : clear implicits.
Arguments paco7_2_1_mult : clear implicits.
Arguments paco7_2_0_fold : clear implicits.
Arguments paco7_2_1_fold : clear implicits.
Arguments paco7_2_0_unfold : clear implicits.
Arguments paco7_2_1_unfold : clear implicits.

Global Instance paco7_2_0_inst  (gf_0 gf_1 : rel7 T0 T1 T2 T3 T4 T5 T6->_) r_0 r_1 x0 x1 x2 x3 x4 x5 x6 : paco_class (paco7_2_0 gf_0 gf_1 r_0 r_1 x0 x1 x2 x3 x4 x5 x6) :=
{ pacoacc    := paco7_2_0_acc gf_0 gf_1;
  pacomult   := paco7_2_0_mult gf_0 gf_1;
  pacofold   := paco7_2_0_fold gf_0 gf_1;
  pacounfold := paco7_2_0_unfold gf_0 gf_1 }.

Global Instance paco7_2_1_inst  (gf_0 gf_1 : rel7 T0 T1 T2 T3 T4 T5 T6->_) r_0 r_1 x0 x1 x2 x3 x4 x5 x6 : paco_class (paco7_2_1 gf_0 gf_1 r_0 r_1 x0 x1 x2 x3 x4 x5 x6) :=
{ pacoacc    := paco7_2_1_acc gf_0 gf_1;
  pacomult   := paco7_2_1_mult gf_0 gf_1;
  pacofold   := paco7_2_1_fold gf_0 gf_1;
  pacounfold := paco7_2_1_unfold gf_0 gf_1 }.

(** 3 Mutual Coinduction *)

Section Arg7_3.

Definition monotone7_3 (gf: rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6) :=
  forall x0 x1 x2 x3 x4 x5 x6 r_0 r_1 r_2 r'_0 r'_1 r'_2 (IN: gf r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6) (LE_0: r_0 <7= r'_0)(LE_1: r_1 <7= r'_1)(LE_2: r_2 <7= r'_2), gf r'_0 r'_1 r'_2 x0 x1 x2 x3 x4 x5 x6.

Definition _monotone7_3 (gf: rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6) :=
  forall r_0 r_1 r_2 r'_0 r'_1 r'_2(LE_0: r_0 <7= r'_0)(LE_1: r_1 <7= r'_1)(LE_2: r_2 <7= r'_2), gf r_0 r_1 r_2 <7== gf r'_0 r'_1 r'_2.

Lemma monotone7_3_eq (gf: rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6) :
  monotone7_3 gf <-> _monotone7_3 gf.
Proof. unfold monotone7_3, _monotone7_3, le7. split; intros; eapply H; eassumption. Qed.

Lemma monotone7_3_map (gf: rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6)
      (MON: _monotone7_3 gf) :
  _monotone_3 (fun R0 R1 R2 => uncurry7 (gf (curry7 R0) (curry7 R1) (curry7 R2))).
Proof.
  repeat_intros 9. apply uncurry_map7. apply MON; apply curry_map7; assumption.
Qed.

Variable gf_0 gf_1 gf_2 : rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.
Arguments gf_2 : clear implicits.

Theorem _paco7_3_0_mon: _monotone7_3 (paco7_3_0 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 9. eapply curry_map7, _paco_3_0_mon; apply uncurry_map7; assumption.
Qed.

Theorem _paco7_3_1_mon: _monotone7_3 (paco7_3_1 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 9. eapply curry_map7, _paco_3_1_mon; apply uncurry_map7; assumption.
Qed.

Theorem _paco7_3_2_mon: _monotone7_3 (paco7_3_2 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 9. eapply curry_map7, _paco_3_2_mon; apply uncurry_map7; assumption.
Qed.

Theorem _paco7_3_0_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_0 <7== rr) (CIH: l <7== rr), l <7== paco7_3_0 gf_0 gf_1 gf_2 rr r_1 r_2),
  l <7== paco7_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_7.
  eapply _paco_3_0_acc. intros.
  apply uncurry_adjoint1_7 in INC. apply uncurry_adjoint1_7 in CIH.
  apply uncurry_adjoint2_7.
  eapply le7_trans. eapply (OBG _ INC CIH).
  apply curry_map7.
  apply _paco_3_0_mon; try apply le1_refl; apply curry_bij1_7.
Qed.

Theorem _paco7_3_1_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_1 <7== rr) (CIH: l <7== rr), l <7== paco7_3_1 gf_0 gf_1 gf_2 r_0 rr r_2),
  l <7== paco7_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_7.
  eapply _paco_3_1_acc. intros.
  apply uncurry_adjoint1_7 in INC. apply uncurry_adjoint1_7 in CIH.
  apply uncurry_adjoint2_7.
  eapply le7_trans. eapply (OBG _ INC CIH).
  apply curry_map7.
  apply _paco_3_1_mon; try apply le1_refl; apply curry_bij1_7.
Qed.

Theorem _paco7_3_2_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_2 <7== rr) (CIH: l <7== rr), l <7== paco7_3_2 gf_0 gf_1 gf_2 r_0 r_1 rr),
  l <7== paco7_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_7.
  eapply _paco_3_2_acc. intros.
  apply uncurry_adjoint1_7 in INC. apply uncurry_adjoint1_7 in CIH.
  apply uncurry_adjoint2_7.
  eapply le7_trans. eapply (OBG _ INC CIH).
  apply curry_map7.
  apply _paco_3_2_mon; try apply le1_refl; apply curry_bij1_7.
Qed.

Theorem _paco7_3_0_mult_strong: forall r_0 r_1 r_2,
  paco7_3_0 gf_0 gf_1 gf_2 (upaco7_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco7_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco7_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <7== paco7_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply curry_map7.
  eapply le1_trans; [| eapply _paco_3_0_mult_strong].
  apply _paco_3_0_mon; intros []; intros H; apply H.
Qed.

Theorem _paco7_3_1_mult_strong: forall r_0 r_1 r_2,
  paco7_3_1 gf_0 gf_1 gf_2 (upaco7_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco7_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco7_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <7== paco7_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply curry_map7.
  eapply le1_trans; [| eapply _paco_3_1_mult_strong].
  apply _paco_3_1_mon; intros []; intros H; apply H.
Qed.

Theorem _paco7_3_2_mult_strong: forall r_0 r_1 r_2,
  paco7_3_2 gf_0 gf_1 gf_2 (upaco7_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco7_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco7_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <7== paco7_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply curry_map7.
  eapply le1_trans; [| eapply _paco_3_2_mult_strong].
  apply _paco_3_2_mon; intros []; intros H; apply H.
Qed.

Theorem _paco7_3_0_fold: forall r_0 r_1 r_2,
  gf_0 (upaco7_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco7_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco7_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <7== paco7_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_7.
  eapply le1_trans; [| apply _paco_3_0_fold]. apply le1_refl.
Qed.

Theorem _paco7_3_1_fold: forall r_0 r_1 r_2,
  gf_1 (upaco7_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco7_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco7_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <7== paco7_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_7.
  eapply le1_trans; [| apply _paco_3_1_fold]. apply le1_refl.
Qed.

Theorem _paco7_3_2_fold: forall r_0 r_1 r_2,
  gf_2 (upaco7_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco7_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco7_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <7== paco7_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_7.
  eapply le1_trans; [| apply _paco_3_2_fold]. apply le1_refl.
Qed.

Theorem _paco7_3_0_unfold: forall (MON: _monotone7_3 gf_0) (MON: _monotone7_3 gf_1) (MON: _monotone7_3 gf_2) r_0 r_1 r_2,
  paco7_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 <7== gf_0 (upaco7_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco7_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco7_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  intros. apply curry_adjoint2_7.
  eapply _paco_3_0_unfold; apply monotone7_3_map; assumption.
Qed.

Theorem _paco7_3_1_unfold: forall (MON: _monotone7_3 gf_0) (MON: _monotone7_3 gf_1) (MON: _monotone7_3 gf_2) r_0 r_1 r_2,
  paco7_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 <7== gf_1 (upaco7_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco7_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco7_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  intros. apply curry_adjoint2_7.
  eapply _paco_3_1_unfold; apply monotone7_3_map; assumption.
Qed.

Theorem _paco7_3_2_unfold: forall (MON: _monotone7_3 gf_0) (MON: _monotone7_3 gf_1) (MON: _monotone7_3 gf_2) r_0 r_1 r_2,
  paco7_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 <7== gf_2 (upaco7_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco7_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco7_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  intros. apply curry_adjoint2_7.
  eapply _paco_3_2_unfold; apply monotone7_3_map; assumption.
Qed.

Theorem paco7_3_0_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_0 <7= rr) (CIH: l <7= rr), l <7= paco7_3_0 gf_0 gf_1 gf_2 rr r_1 r_2),
  l <7= paco7_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco7_3_0_acc.
Qed.

Theorem paco7_3_1_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_1 <7= rr) (CIH: l <7= rr), l <7= paco7_3_1 gf_0 gf_1 gf_2 r_0 rr r_2),
  l <7= paco7_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco7_3_1_acc.
Qed.

Theorem paco7_3_2_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_2 <7= rr) (CIH: l <7= rr), l <7= paco7_3_2 gf_0 gf_1 gf_2 r_0 r_1 rr),
  l <7= paco7_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco7_3_2_acc.
Qed.

Theorem paco7_3_0_mon: monotone7_3 (paco7_3_0 gf_0 gf_1 gf_2).
Proof.
  apply monotone7_3_eq.
  apply _paco7_3_0_mon.
Qed.

Theorem paco7_3_1_mon: monotone7_3 (paco7_3_1 gf_0 gf_1 gf_2).
Proof.
  apply monotone7_3_eq.
  apply _paco7_3_1_mon.
Qed.

Theorem paco7_3_2_mon: monotone7_3 (paco7_3_2 gf_0 gf_1 gf_2).
Proof.
  apply monotone7_3_eq.
  apply _paco7_3_2_mon.
Qed.

Theorem paco7_3_0_mult_strong: forall r_0 r_1 r_2,
  paco7_3_0 gf_0 gf_1 gf_2 (upaco7_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco7_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco7_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <7= paco7_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco7_3_0_mult_strong.
Qed.

Theorem paco7_3_1_mult_strong: forall r_0 r_1 r_2,
  paco7_3_1 gf_0 gf_1 gf_2 (upaco7_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco7_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco7_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <7= paco7_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco7_3_1_mult_strong.
Qed.

Theorem paco7_3_2_mult_strong: forall r_0 r_1 r_2,
  paco7_3_2 gf_0 gf_1 gf_2 (upaco7_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco7_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco7_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <7= paco7_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco7_3_2_mult_strong.
Qed.

Corollary paco7_3_0_mult: forall r_0 r_1 r_2,
  paco7_3_0 gf_0 gf_1 gf_2 (paco7_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco7_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco7_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <7= paco7_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco7_3_0_mult_strong, paco7_3_0_mon; [apply PR|..]; intros; left; assumption. Qed.

Corollary paco7_3_1_mult: forall r_0 r_1 r_2,
  paco7_3_1 gf_0 gf_1 gf_2 (paco7_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco7_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco7_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <7= paco7_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco7_3_1_mult_strong, paco7_3_1_mon; [apply PR|..]; intros; left; assumption. Qed.

Corollary paco7_3_2_mult: forall r_0 r_1 r_2,
  paco7_3_2 gf_0 gf_1 gf_2 (paco7_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco7_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco7_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <7= paco7_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco7_3_2_mult_strong, paco7_3_2_mon; [apply PR|..]; intros; left; assumption. Qed.

Theorem paco7_3_0_fold: forall r_0 r_1 r_2,
  gf_0 (upaco7_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco7_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco7_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <7= paco7_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco7_3_0_fold.
Qed.

Theorem paco7_3_1_fold: forall r_0 r_1 r_2,
  gf_1 (upaco7_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco7_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco7_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <7= paco7_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco7_3_1_fold.
Qed.

Theorem paco7_3_2_fold: forall r_0 r_1 r_2,
  gf_2 (upaco7_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco7_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco7_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <7= paco7_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco7_3_2_fold.
Qed.

Theorem paco7_3_0_unfold: forall (MON: monotone7_3 gf_0) (MON: monotone7_3 gf_1) (MON: monotone7_3 gf_2) r_0 r_1 r_2,
  paco7_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 <7= gf_0 (upaco7_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco7_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco7_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  repeat_intros 3. eapply _paco7_3_0_unfold; apply monotone7_3_eq; assumption.
Qed.

Theorem paco7_3_1_unfold: forall (MON: monotone7_3 gf_0) (MON: monotone7_3 gf_1) (MON: monotone7_3 gf_2) r_0 r_1 r_2,
  paco7_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 <7= gf_1 (upaco7_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco7_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco7_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  repeat_intros 3. eapply _paco7_3_1_unfold; apply monotone7_3_eq; assumption.
Qed.

Theorem paco7_3_2_unfold: forall (MON: monotone7_3 gf_0) (MON: monotone7_3 gf_1) (MON: monotone7_3 gf_2) r_0 r_1 r_2,
  paco7_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 <7= gf_2 (upaco7_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco7_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco7_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  repeat_intros 3. eapply _paco7_3_2_unfold; apply monotone7_3_eq; assumption.
Qed.

End Arg7_3.

Arguments paco7_3_0_acc : clear implicits.
Arguments paco7_3_1_acc : clear implicits.
Arguments paco7_3_2_acc : clear implicits.
Arguments paco7_3_0_mon : clear implicits.
Arguments paco7_3_1_mon : clear implicits.
Arguments paco7_3_2_mon : clear implicits.
Arguments paco7_3_0_mult_strong : clear implicits.
Arguments paco7_3_1_mult_strong : clear implicits.
Arguments paco7_3_2_mult_strong : clear implicits.
Arguments paco7_3_0_mult : clear implicits.
Arguments paco7_3_1_mult : clear implicits.
Arguments paco7_3_2_mult : clear implicits.
Arguments paco7_3_0_fold : clear implicits.
Arguments paco7_3_1_fold : clear implicits.
Arguments paco7_3_2_fold : clear implicits.
Arguments paco7_3_0_unfold : clear implicits.
Arguments paco7_3_1_unfold : clear implicits.
Arguments paco7_3_2_unfold : clear implicits.

Global Instance paco7_3_0_inst  (gf_0 gf_1 gf_2 : rel7 T0 T1 T2 T3 T4 T5 T6->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 : paco_class (paco7_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6) :=
{ pacoacc    := paco7_3_0_acc gf_0 gf_1 gf_2;
  pacomult   := paco7_3_0_mult gf_0 gf_1 gf_2;
  pacofold   := paco7_3_0_fold gf_0 gf_1 gf_2;
  pacounfold := paco7_3_0_unfold gf_0 gf_1 gf_2 }.

Global Instance paco7_3_1_inst  (gf_0 gf_1 gf_2 : rel7 T0 T1 T2 T3 T4 T5 T6->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 : paco_class (paco7_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6) :=
{ pacoacc    := paco7_3_1_acc gf_0 gf_1 gf_2;
  pacomult   := paco7_3_1_mult gf_0 gf_1 gf_2;
  pacofold   := paco7_3_1_fold gf_0 gf_1 gf_2;
  pacounfold := paco7_3_1_unfold gf_0 gf_1 gf_2 }.

Global Instance paco7_3_2_inst  (gf_0 gf_1 gf_2 : rel7 T0 T1 T2 T3 T4 T5 T6->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 : paco_class (paco7_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6) :=
{ pacoacc    := paco7_3_2_acc gf_0 gf_1 gf_2;
  pacomult   := paco7_3_2_mult gf_0 gf_1 gf_2;
  pacofold   := paco7_3_2_fold gf_0 gf_1 gf_2;
  pacounfold := paco7_3_2_unfold gf_0 gf_1 gf_2 }.

End PACO7.

Global Opaque paco7.

Hint Unfold upaco7.
Hint Resolve paco7_fold.
Hint Unfold monotone7.

Global Opaque paco7_2_0.
Global Opaque paco7_2_1.

Hint Unfold upaco7_2_0.
Hint Unfold upaco7_2_1.
Hint Resolve paco7_2_0_fold.
Hint Resolve paco7_2_1_fold.
Hint Unfold monotone7_2.

Global Opaque paco7_3_0.
Global Opaque paco7_3_1.
Global Opaque paco7_3_2.

Hint Unfold upaco7_3_0.
Hint Unfold upaco7_3_1.
Hint Unfold upaco7_3_2.
Hint Resolve paco7_3_0_fold.
Hint Resolve paco7_3_1_fold.
Hint Resolve paco7_3_2_fold.
Hint Unfold monotone7_3.

