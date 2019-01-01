Require Export paconotation pacotacuser.
Require Import paconotation_internal pacotac pacon.
Set Implicit Arguments.

Section PACO5.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.

Record sig5T :=
  exist5T { 
      proj5T0: @T0;
      proj5T1: @T1 proj5T0;
      proj5T2: @T2 proj5T0 proj5T1;
      proj5T3: @T3 proj5T0 proj5T1 proj5T2;
      proj5T4: @T4 proj5T0 proj5T1 proj5T2 proj5T3;
    }.

Definition uncurry5 (R: rel5 T0 T1 T2 T3 T4): rel1 sig5T := fun x => R (proj5T0 x) (proj5T1 x) (proj5T2 x) (proj5T3 x) (proj5T4 x).

Definition curry5 (R: rel1 sig5T): rel5 T0 T1 T2 T3 T4 :=
  fun x0 x1 x2 x3 x4 => R (exist5T x4).

Lemma uncurry_map5 r0 r1 (LE : r0 <5== r1) : uncurry5 r0 <1== uncurry5 r1.
Proof. intros [] H. apply LE. apply H. Qed.

Lemma uncurry_map_rev5 r0 r1 (LE: uncurry5 r0 <1== uncurry5 r1) : r0 <5== r1.
Proof.
  repeat_intros 5. intros H. apply (LE (exist5T x4) H).
Qed.

Lemma curry_map5 r0 r1 (LE: r0 <1== r1) : curry5 r0 <5== curry5 r1.
Proof. 
  repeat_intros 5. intros H. apply (LE (exist5T x4) H).
Qed.

Lemma curry_map_rev5 r0 r1 (LE: curry5 r0 <5== curry5 r1) : r0 <1== r1.
Proof. 
  intros [] H. apply LE. apply H.
Qed.

Lemma uncurry_bij1_5 r : curry5 (uncurry5 r) <5== r.
Proof. unfold le5. repeat_intros 5. intros H. apply H. Qed.

Lemma uncurry_bij2_5 r : r <5== curry5 (uncurry5 r).
Proof. unfold le5. repeat_intros 5. intros H. apply H. Qed.

Lemma curry_bij1_5 r : uncurry5 (curry5 r) <1== r.
Proof. intros []. intro H. apply H. Qed.

Lemma curry_bij2_5 r : r <1== uncurry5 (curry5 r).
Proof. intros []. intro H. apply H. Qed.

Lemma uncurry_adjoint1_5 r0 r1 (LE: uncurry5 r0 <1== r1) : r0 <5== curry5 r1.
Proof.
  apply uncurry_map_rev5. eapply le1_trans; [apply LE|]. apply curry_bij2_5.
Qed.

Lemma uncurry_adjoint2_5 r0 r1 (LE: r0 <5== curry5 r1) : uncurry5 r0 <1== r1.
Proof.
  apply curry_map_rev5. eapply le5_trans; [|apply LE]. apply uncurry_bij2_5.
Qed.

Lemma curry_adjoint1_5 r0 r1 (LE: curry5 r0 <5== r1) : r0 <1== uncurry5 r1.
Proof.
  apply curry_map_rev5. eapply le5_trans; [apply LE|]. apply uncurry_bij2_5.
Qed.

Lemma curry_adjoint2_5 r0 r1 (LE: r0 <1== uncurry5 r1) : curry5 r0 <5== r1.
Proof.
  apply uncurry_map_rev5. eapply le1_trans; [|apply LE]. apply curry_bij1_5.
Qed.

(** ** Predicates of Arity 5
*)

Section Arg5_def.
Variable gf : rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4.
Arguments gf : clear implicits.

Definition paco5( r: rel5 T0 T1 T2 T3 T4) : rel5 T0 T1 T2 T3 T4 :=
  curry5 (paco (fun R0 => uncurry5 (gf (curry5 R0))) (uncurry5 r)).

Definition upaco5( r: rel5 T0 T1 T2 T3 T4) := paco5 r \5/ r.
End Arg5_def.
Arguments paco5 : clear implicits.
Arguments upaco5 : clear implicits.
Hint Unfold upaco5.

Section Arg5_2_def.
Variable gf_0 gf_1 : rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.

Definition paco5_2_0( r_0 r_1: rel5 T0 T1 T2 T3 T4) : rel5 T0 T1 T2 T3 T4 :=
  curry5 (paco_2_0 (fun R0 R1 => uncurry5 (gf_0 (curry5 R0) (curry5 R1))) (fun R0 R1 => uncurry5 (gf_1 (curry5 R0) (curry5 R1))) (uncurry5 r_0) (uncurry5 r_1)).

Definition paco5_2_1( r_0 r_1: rel5 T0 T1 T2 T3 T4) : rel5 T0 T1 T2 T3 T4 :=
  curry5 (paco_2_1 (fun R0 R1 => uncurry5 (gf_0 (curry5 R0) (curry5 R1))) (fun R0 R1 => uncurry5 (gf_1 (curry5 R0) (curry5 R1))) (uncurry5 r_0) (uncurry5 r_1)).

Definition upaco5_2_0( r_0 r_1: rel5 T0 T1 T2 T3 T4) := paco5_2_0 r_0 r_1 \5/ r_0.
Definition upaco5_2_1( r_0 r_1: rel5 T0 T1 T2 T3 T4) := paco5_2_1 r_0 r_1 \5/ r_1.
End Arg5_2_def.
Arguments paco5_2_0 : clear implicits.
Arguments upaco5_2_0 : clear implicits.
Hint Unfold upaco5_2_0.
Arguments paco5_2_1 : clear implicits.
Arguments upaco5_2_1 : clear implicits.
Hint Unfold upaco5_2_1.

Section Arg5_3_def.
Variable gf_0 gf_1 gf_2 : rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.
Arguments gf_2 : clear implicits.

Definition paco5_3_0( r_0 r_1 r_2: rel5 T0 T1 T2 T3 T4) : rel5 T0 T1 T2 T3 T4 :=
  curry5 (paco_3_0 (fun R0 R1 R2 => uncurry5 (gf_0 (curry5 R0) (curry5 R1) (curry5 R2))) (fun R0 R1 R2 => uncurry5 (gf_1 (curry5 R0) (curry5 R1) (curry5 R2))) (fun R0 R1 R2 => uncurry5 (gf_2 (curry5 R0) (curry5 R1) (curry5 R2))) (uncurry5 r_0) (uncurry5 r_1) (uncurry5 r_2)).

Definition paco5_3_1( r_0 r_1 r_2: rel5 T0 T1 T2 T3 T4) : rel5 T0 T1 T2 T3 T4 :=
  curry5 (paco_3_1 (fun R0 R1 R2 => uncurry5 (gf_0 (curry5 R0) (curry5 R1) (curry5 R2))) (fun R0 R1 R2 => uncurry5 (gf_1 (curry5 R0) (curry5 R1) (curry5 R2))) (fun R0 R1 R2 => uncurry5 (gf_2 (curry5 R0) (curry5 R1) (curry5 R2))) (uncurry5 r_0) (uncurry5 r_1) (uncurry5 r_2)).

Definition paco5_3_2( r_0 r_1 r_2: rel5 T0 T1 T2 T3 T4) : rel5 T0 T1 T2 T3 T4 :=
  curry5 (paco_3_2 (fun R0 R1 R2 => uncurry5 (gf_0 (curry5 R0) (curry5 R1) (curry5 R2))) (fun R0 R1 R2 => uncurry5 (gf_1 (curry5 R0) (curry5 R1) (curry5 R2))) (fun R0 R1 R2 => uncurry5 (gf_2 (curry5 R0) (curry5 R1) (curry5 R2))) (uncurry5 r_0) (uncurry5 r_1) (uncurry5 r_2)).

Definition upaco5_3_0( r_0 r_1 r_2: rel5 T0 T1 T2 T3 T4) := paco5_3_0 r_0 r_1 r_2 \5/ r_0.
Definition upaco5_3_1( r_0 r_1 r_2: rel5 T0 T1 T2 T3 T4) := paco5_3_1 r_0 r_1 r_2 \5/ r_1.
Definition upaco5_3_2( r_0 r_1 r_2: rel5 T0 T1 T2 T3 T4) := paco5_3_2 r_0 r_1 r_2 \5/ r_2.
End Arg5_3_def.
Arguments paco5_3_0 : clear implicits.
Arguments upaco5_3_0 : clear implicits.
Hint Unfold upaco5_3_0.
Arguments paco5_3_1 : clear implicits.
Arguments upaco5_3_1 : clear implicits.
Hint Unfold upaco5_3_1.
Arguments paco5_3_2 : clear implicits.
Arguments upaco5_3_2 : clear implicits.
Hint Unfold upaco5_3_2.

(** 1 Mutual Coinduction *)

Section Arg5_1.

Definition monotone5 (gf: rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4) :=
  forall x0 x1 x2 x3 x4 r r' (IN: gf r x0 x1 x2 x3 x4) (LE: r <5= r'), gf r' x0 x1 x2 x3 x4.

Definition _monotone5 (gf: rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4) :=
  forall r r'(LE: r <5= r'), gf r <5== gf r'.

Lemma monotone5_eq (gf: rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4) :
  monotone5 gf <-> _monotone5 gf.
Proof. unfold monotone5, _monotone5, le5. split; intros; eapply H; eassumption. Qed.

Lemma monotone5_map (gf: rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4)
      (MON: _monotone5 gf) :
  _monotone (fun R0 => uncurry5 (gf (curry5 R0))).
Proof.
  repeat_intros 3. apply uncurry_map5. apply MON; apply curry_map5; assumption.
Qed.

Variable gf : rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4.
Arguments gf : clear implicits.

Theorem _paco5_mon: _monotone5 (paco5 gf).
Proof.
  repeat_intros 3. eapply curry_map5, _paco_mon; apply uncurry_map5; assumption.
Qed.

Theorem _paco5_acc: forall
  l r (OBG: forall rr (INC: r <5== rr) (CIH: l <5== rr), l <5== paco5 gf rr),
  l <5== paco5 gf r.
Proof.
  intros. apply uncurry_adjoint1_5.
  eapply _paco_acc. intros.
  apply uncurry_adjoint1_5 in INC. apply uncurry_adjoint1_5 in CIH.
  apply uncurry_adjoint2_5.
  eapply le5_trans. eapply (OBG _ INC CIH).
  apply curry_map5.
  apply _paco_mon; try apply le1_refl; apply curry_bij1_5.
Qed.

Theorem _paco5_mult_strong: forall r,
  paco5 gf (upaco5 gf r) <5== paco5 gf r.
Proof.
  intros. apply curry_map5.
  eapply le1_trans; [| eapply _paco_mult_strong].
  apply _paco_mon; intros []; intros H; apply H.
Qed.

Theorem _paco5_fold: forall r,
  gf (upaco5 gf r) <5== paco5 gf r.
Proof.
  intros. apply uncurry_adjoint1_5.
  eapply le1_trans; [| apply _paco_fold]. apply le1_refl.
Qed.

Theorem _paco5_unfold: forall (MON: _monotone5 gf) r,
  paco5 gf r <5== gf (upaco5 gf r).
Proof.
  intros. apply curry_adjoint2_5.
  eapply _paco_unfold; apply monotone5_map; assumption.
Qed.

Theorem paco5_acc: forall
  l r (OBG: forall rr (INC: r <5= rr) (CIH: l <5= rr), l <5= paco5 gf rr),
  l <5= paco5 gf r.
Proof.
  apply _paco5_acc.
Qed.

Theorem paco5_mon: monotone5 (paco5 gf).
Proof.
  apply monotone5_eq.
  apply _paco5_mon.
Qed.

Theorem upaco5_mon: monotone5 (upaco5 gf).
Proof.
  repeat_intros 7. intros R  LE0.
  destruct R.
  - left. eapply paco5_mon. apply H. apply LE0.
  - right. apply LE0, H.
Qed.
Theorem paco5_mult_strong: forall r,
  paco5 gf (upaco5 gf r) <5= paco5 gf r.
Proof.
  apply _paco5_mult_strong.
Qed.

Corollary paco5_mult: forall r,
  paco5 gf (paco5 gf r) <5= paco5 gf r.
Proof. intros; eapply paco5_mult_strong, paco5_mon; [apply PR|..]; intros; left; assumption. Qed.

Theorem paco5_fold: forall r,
  gf (upaco5 gf r) <5= paco5 gf r.
Proof.
  apply _paco5_fold.
Qed.

Theorem paco5_unfold: forall (MON: monotone5 gf) r,
  paco5 gf r <5= gf (upaco5 gf r).
Proof.
  repeat_intros 1. eapply _paco5_unfold; apply monotone5_eq; assumption.
Qed.

End Arg5_1.

Arguments paco5_acc : clear implicits.
Arguments paco5_mon : clear implicits.
Arguments upaco5_mon : clear implicits.
Arguments paco5_mult_strong : clear implicits.
Arguments paco5_mult : clear implicits.
Arguments paco5_fold : clear implicits.
Arguments paco5_unfold : clear implicits.

Global Instance paco5_inst  (gf : rel5 T0 T1 T2 T3 T4->_) r x0 x1 x2 x3 x4 : paco_class (paco5 gf r x0 x1 x2 x3 x4) :=
{ pacoacc    := paco5_acc gf;
  pacomult   := paco5_mult gf;
  pacofold   := paco5_fold gf;
  pacounfold := paco5_unfold gf }.

(** 2 Mutual Coinduction *)

Section Arg5_2.

Definition monotone5_2 (gf: rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4) :=
  forall x0 x1 x2 x3 x4 r_0 r_1 r'_0 r'_1 (IN: gf r_0 r_1 x0 x1 x2 x3 x4) (LE_0: r_0 <5= r'_0)(LE_1: r_1 <5= r'_1), gf r'_0 r'_1 x0 x1 x2 x3 x4.

Definition _monotone5_2 (gf: rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4) :=
  forall r_0 r_1 r'_0 r'_1(LE_0: r_0 <5= r'_0)(LE_1: r_1 <5= r'_1), gf r_0 r_1 <5== gf r'_0 r'_1.

Lemma monotone5_2_eq (gf: rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4) :
  monotone5_2 gf <-> _monotone5_2 gf.
Proof. unfold monotone5_2, _monotone5_2, le5. split; intros; eapply H; eassumption. Qed.

Lemma monotone5_2_map (gf: rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4)
      (MON: _monotone5_2 gf) :
  _monotone_2 (fun R0 R1 => uncurry5 (gf (curry5 R0) (curry5 R1))).
Proof.
  repeat_intros 6. apply uncurry_map5. apply MON; apply curry_map5; assumption.
Qed.

Variable gf_0 gf_1 : rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.

Theorem _paco5_2_0_mon: _monotone5_2 (paco5_2_0 gf_0 gf_1).
Proof.
  repeat_intros 6. eapply curry_map5, _paco_2_0_mon; apply uncurry_map5; assumption.
Qed.

Theorem _paco5_2_1_mon: _monotone5_2 (paco5_2_1 gf_0 gf_1).
Proof.
  repeat_intros 6. eapply curry_map5, _paco_2_1_mon; apply uncurry_map5; assumption.
Qed.

Theorem _paco5_2_0_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_0 <5== rr) (CIH: l <5== rr), l <5== paco5_2_0 gf_0 gf_1 rr r_1),
  l <5== paco5_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_5.
  eapply _paco_2_0_acc. intros.
  apply uncurry_adjoint1_5 in INC. apply uncurry_adjoint1_5 in CIH.
  apply uncurry_adjoint2_5.
  eapply le5_trans. eapply (OBG _ INC CIH).
  apply curry_map5.
  apply _paco_2_0_mon; try apply le1_refl; apply curry_bij1_5.
Qed.

Theorem _paco5_2_1_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_1 <5== rr) (CIH: l <5== rr), l <5== paco5_2_1 gf_0 gf_1 r_0 rr),
  l <5== paco5_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_5.
  eapply _paco_2_1_acc. intros.
  apply uncurry_adjoint1_5 in INC. apply uncurry_adjoint1_5 in CIH.
  apply uncurry_adjoint2_5.
  eapply le5_trans. eapply (OBG _ INC CIH).
  apply curry_map5.
  apply _paco_2_1_mon; try apply le1_refl; apply curry_bij1_5.
Qed.

Theorem _paco5_2_0_mult_strong: forall r_0 r_1,
  paco5_2_0 gf_0 gf_1 (upaco5_2_0 gf_0 gf_1 r_0 r_1) (upaco5_2_1 gf_0 gf_1 r_0 r_1) <5== paco5_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply curry_map5.
  eapply le1_trans; [| eapply _paco_2_0_mult_strong].
  apply _paco_2_0_mon; intros []; intros H; apply H.
Qed.

Theorem _paco5_2_1_mult_strong: forall r_0 r_1,
  paco5_2_1 gf_0 gf_1 (upaco5_2_0 gf_0 gf_1 r_0 r_1) (upaco5_2_1 gf_0 gf_1 r_0 r_1) <5== paco5_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply curry_map5.
  eapply le1_trans; [| eapply _paco_2_1_mult_strong].
  apply _paco_2_1_mon; intros []; intros H; apply H.
Qed.

Theorem _paco5_2_0_fold: forall r_0 r_1,
  gf_0 (upaco5_2_0 gf_0 gf_1 r_0 r_1) (upaco5_2_1 gf_0 gf_1 r_0 r_1) <5== paco5_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_5.
  eapply le1_trans; [| apply _paco_2_0_fold]. apply le1_refl.
Qed.

Theorem _paco5_2_1_fold: forall r_0 r_1,
  gf_1 (upaco5_2_0 gf_0 gf_1 r_0 r_1) (upaco5_2_1 gf_0 gf_1 r_0 r_1) <5== paco5_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_5.
  eapply le1_trans; [| apply _paco_2_1_fold]. apply le1_refl.
Qed.

Theorem _paco5_2_0_unfold: forall (MON: _monotone5_2 gf_0) (MON: _monotone5_2 gf_1) r_0 r_1,
  paco5_2_0 gf_0 gf_1 r_0 r_1 <5== gf_0 (upaco5_2_0 gf_0 gf_1 r_0 r_1) (upaco5_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  intros. apply curry_adjoint2_5.
  eapply _paco_2_0_unfold; apply monotone5_2_map; assumption.
Qed.

Theorem _paco5_2_1_unfold: forall (MON: _monotone5_2 gf_0) (MON: _monotone5_2 gf_1) r_0 r_1,
  paco5_2_1 gf_0 gf_1 r_0 r_1 <5== gf_1 (upaco5_2_0 gf_0 gf_1 r_0 r_1) (upaco5_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  intros. apply curry_adjoint2_5.
  eapply _paco_2_1_unfold; apply monotone5_2_map; assumption.
Qed.

Theorem paco5_2_0_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_0 <5= rr) (CIH: l <5= rr), l <5= paco5_2_0 gf_0 gf_1 rr r_1),
  l <5= paco5_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco5_2_0_acc.
Qed.

Theorem paco5_2_1_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_1 <5= rr) (CIH: l <5= rr), l <5= paco5_2_1 gf_0 gf_1 r_0 rr),
  l <5= paco5_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco5_2_1_acc.
Qed.

Theorem paco5_2_0_mon: monotone5_2 (paco5_2_0 gf_0 gf_1).
Proof.
  apply monotone5_2_eq.
  apply _paco5_2_0_mon.
Qed.

Theorem paco5_2_1_mon: monotone5_2 (paco5_2_1 gf_0 gf_1).
Proof.
  apply monotone5_2_eq.
  apply _paco5_2_1_mon.
Qed.

Theorem upaco5_2_0_mon: monotone5_2 (upaco5_2_0 gf_0 gf_1).
Proof.
  repeat_intros 9. intros R  LE0 LE1.
  destruct R.
  - left. eapply paco5_2_0_mon. apply H. apply LE0. apply LE1.
  - right. apply LE0, H.
Qed.
Theorem upaco5_2_1_mon: monotone5_2 (upaco5_2_1 gf_0 gf_1).
Proof.
  repeat_intros 9. intros R  LE0 LE1.
  destruct R.
  - left. eapply paco5_2_1_mon. apply H. apply LE0. apply LE1.
  - right. apply LE1, H.
Qed.
Theorem paco5_2_0_mult_strong: forall r_0 r_1,
  paco5_2_0 gf_0 gf_1 (upaco5_2_0 gf_0 gf_1 r_0 r_1) (upaco5_2_1 gf_0 gf_1 r_0 r_1) <5= paco5_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco5_2_0_mult_strong.
Qed.

Theorem paco5_2_1_mult_strong: forall r_0 r_1,
  paco5_2_1 gf_0 gf_1 (upaco5_2_0 gf_0 gf_1 r_0 r_1) (upaco5_2_1 gf_0 gf_1 r_0 r_1) <5= paco5_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco5_2_1_mult_strong.
Qed.

Corollary paco5_2_0_mult: forall r_0 r_1,
  paco5_2_0 gf_0 gf_1 (paco5_2_0 gf_0 gf_1 r_0 r_1) (paco5_2_1 gf_0 gf_1 r_0 r_1) <5= paco5_2_0 gf_0 gf_1 r_0 r_1.
Proof. intros; eapply paco5_2_0_mult_strong, paco5_2_0_mon; [apply PR|..]; intros; left; assumption. Qed.

Corollary paco5_2_1_mult: forall r_0 r_1,
  paco5_2_1 gf_0 gf_1 (paco5_2_0 gf_0 gf_1 r_0 r_1) (paco5_2_1 gf_0 gf_1 r_0 r_1) <5= paco5_2_1 gf_0 gf_1 r_0 r_1.
Proof. intros; eapply paco5_2_1_mult_strong, paco5_2_1_mon; [apply PR|..]; intros; left; assumption. Qed.

Theorem paco5_2_0_fold: forall r_0 r_1,
  gf_0 (upaco5_2_0 gf_0 gf_1 r_0 r_1) (upaco5_2_1 gf_0 gf_1 r_0 r_1) <5= paco5_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco5_2_0_fold.
Qed.

Theorem paco5_2_1_fold: forall r_0 r_1,
  gf_1 (upaco5_2_0 gf_0 gf_1 r_0 r_1) (upaco5_2_1 gf_0 gf_1 r_0 r_1) <5= paco5_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco5_2_1_fold.
Qed.

Theorem paco5_2_0_unfold: forall (MON: monotone5_2 gf_0) (MON: monotone5_2 gf_1) r_0 r_1,
  paco5_2_0 gf_0 gf_1 r_0 r_1 <5= gf_0 (upaco5_2_0 gf_0 gf_1 r_0 r_1) (upaco5_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  repeat_intros 2. eapply _paco5_2_0_unfold; apply monotone5_2_eq; assumption.
Qed.

Theorem paco5_2_1_unfold: forall (MON: monotone5_2 gf_0) (MON: monotone5_2 gf_1) r_0 r_1,
  paco5_2_1 gf_0 gf_1 r_0 r_1 <5= gf_1 (upaco5_2_0 gf_0 gf_1 r_0 r_1) (upaco5_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  repeat_intros 2. eapply _paco5_2_1_unfold; apply monotone5_2_eq; assumption.
Qed.

End Arg5_2.

Arguments paco5_2_0_acc : clear implicits.
Arguments paco5_2_1_acc : clear implicits.
Arguments paco5_2_0_mon : clear implicits.
Arguments paco5_2_1_mon : clear implicits.
Arguments upaco5_2_0_mon : clear implicits.
Arguments upaco5_2_1_mon : clear implicits.
Arguments paco5_2_0_mult_strong : clear implicits.
Arguments paco5_2_1_mult_strong : clear implicits.
Arguments paco5_2_0_mult : clear implicits.
Arguments paco5_2_1_mult : clear implicits.
Arguments paco5_2_0_fold : clear implicits.
Arguments paco5_2_1_fold : clear implicits.
Arguments paco5_2_0_unfold : clear implicits.
Arguments paco5_2_1_unfold : clear implicits.

Global Instance paco5_2_0_inst  (gf_0 gf_1 : rel5 T0 T1 T2 T3 T4->_) r_0 r_1 x0 x1 x2 x3 x4 : paco_class (paco5_2_0 gf_0 gf_1 r_0 r_1 x0 x1 x2 x3 x4) :=
{ pacoacc    := paco5_2_0_acc gf_0 gf_1;
  pacomult   := paco5_2_0_mult gf_0 gf_1;
  pacofold   := paco5_2_0_fold gf_0 gf_1;
  pacounfold := paco5_2_0_unfold gf_0 gf_1 }.

Global Instance paco5_2_1_inst  (gf_0 gf_1 : rel5 T0 T1 T2 T3 T4->_) r_0 r_1 x0 x1 x2 x3 x4 : paco_class (paco5_2_1 gf_0 gf_1 r_0 r_1 x0 x1 x2 x3 x4) :=
{ pacoacc    := paco5_2_1_acc gf_0 gf_1;
  pacomult   := paco5_2_1_mult gf_0 gf_1;
  pacofold   := paco5_2_1_fold gf_0 gf_1;
  pacounfold := paco5_2_1_unfold gf_0 gf_1 }.

(** 3 Mutual Coinduction *)

Section Arg5_3.

Definition monotone5_3 (gf: rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4) :=
  forall x0 x1 x2 x3 x4 r_0 r_1 r_2 r'_0 r'_1 r'_2 (IN: gf r_0 r_1 r_2 x0 x1 x2 x3 x4) (LE_0: r_0 <5= r'_0)(LE_1: r_1 <5= r'_1)(LE_2: r_2 <5= r'_2), gf r'_0 r'_1 r'_2 x0 x1 x2 x3 x4.

Definition _monotone5_3 (gf: rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4) :=
  forall r_0 r_1 r_2 r'_0 r'_1 r'_2(LE_0: r_0 <5= r'_0)(LE_1: r_1 <5= r'_1)(LE_2: r_2 <5= r'_2), gf r_0 r_1 r_2 <5== gf r'_0 r'_1 r'_2.

Lemma monotone5_3_eq (gf: rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4) :
  monotone5_3 gf <-> _monotone5_3 gf.
Proof. unfold monotone5_3, _monotone5_3, le5. split; intros; eapply H; eassumption. Qed.

Lemma monotone5_3_map (gf: rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4)
      (MON: _monotone5_3 gf) :
  _monotone_3 (fun R0 R1 R2 => uncurry5 (gf (curry5 R0) (curry5 R1) (curry5 R2))).
Proof.
  repeat_intros 9. apply uncurry_map5. apply MON; apply curry_map5; assumption.
Qed.

Variable gf_0 gf_1 gf_2 : rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.
Arguments gf_2 : clear implicits.

Theorem _paco5_3_0_mon: _monotone5_3 (paco5_3_0 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 9. eapply curry_map5, _paco_3_0_mon; apply uncurry_map5; assumption.
Qed.

Theorem _paco5_3_1_mon: _monotone5_3 (paco5_3_1 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 9. eapply curry_map5, _paco_3_1_mon; apply uncurry_map5; assumption.
Qed.

Theorem _paco5_3_2_mon: _monotone5_3 (paco5_3_2 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 9. eapply curry_map5, _paco_3_2_mon; apply uncurry_map5; assumption.
Qed.

Theorem _paco5_3_0_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_0 <5== rr) (CIH: l <5== rr), l <5== paco5_3_0 gf_0 gf_1 gf_2 rr r_1 r_2),
  l <5== paco5_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_5.
  eapply _paco_3_0_acc. intros.
  apply uncurry_adjoint1_5 in INC. apply uncurry_adjoint1_5 in CIH.
  apply uncurry_adjoint2_5.
  eapply le5_trans. eapply (OBG _ INC CIH).
  apply curry_map5.
  apply _paco_3_0_mon; try apply le1_refl; apply curry_bij1_5.
Qed.

Theorem _paco5_3_1_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_1 <5== rr) (CIH: l <5== rr), l <5== paco5_3_1 gf_0 gf_1 gf_2 r_0 rr r_2),
  l <5== paco5_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_5.
  eapply _paco_3_1_acc. intros.
  apply uncurry_adjoint1_5 in INC. apply uncurry_adjoint1_5 in CIH.
  apply uncurry_adjoint2_5.
  eapply le5_trans. eapply (OBG _ INC CIH).
  apply curry_map5.
  apply _paco_3_1_mon; try apply le1_refl; apply curry_bij1_5.
Qed.

Theorem _paco5_3_2_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_2 <5== rr) (CIH: l <5== rr), l <5== paco5_3_2 gf_0 gf_1 gf_2 r_0 r_1 rr),
  l <5== paco5_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_5.
  eapply _paco_3_2_acc. intros.
  apply uncurry_adjoint1_5 in INC. apply uncurry_adjoint1_5 in CIH.
  apply uncurry_adjoint2_5.
  eapply le5_trans. eapply (OBG _ INC CIH).
  apply curry_map5.
  apply _paco_3_2_mon; try apply le1_refl; apply curry_bij1_5.
Qed.

Theorem _paco5_3_0_mult_strong: forall r_0 r_1 r_2,
  paco5_3_0 gf_0 gf_1 gf_2 (upaco5_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco5_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco5_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <5== paco5_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply curry_map5.
  eapply le1_trans; [| eapply _paco_3_0_mult_strong].
  apply _paco_3_0_mon; intros []; intros H; apply H.
Qed.

Theorem _paco5_3_1_mult_strong: forall r_0 r_1 r_2,
  paco5_3_1 gf_0 gf_1 gf_2 (upaco5_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco5_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco5_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <5== paco5_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply curry_map5.
  eapply le1_trans; [| eapply _paco_3_1_mult_strong].
  apply _paco_3_1_mon; intros []; intros H; apply H.
Qed.

Theorem _paco5_3_2_mult_strong: forall r_0 r_1 r_2,
  paco5_3_2 gf_0 gf_1 gf_2 (upaco5_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco5_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco5_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <5== paco5_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply curry_map5.
  eapply le1_trans; [| eapply _paco_3_2_mult_strong].
  apply _paco_3_2_mon; intros []; intros H; apply H.
Qed.

Theorem _paco5_3_0_fold: forall r_0 r_1 r_2,
  gf_0 (upaco5_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco5_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco5_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <5== paco5_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_5.
  eapply le1_trans; [| apply _paco_3_0_fold]. apply le1_refl.
Qed.

Theorem _paco5_3_1_fold: forall r_0 r_1 r_2,
  gf_1 (upaco5_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco5_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco5_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <5== paco5_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_5.
  eapply le1_trans; [| apply _paco_3_1_fold]. apply le1_refl.
Qed.

Theorem _paco5_3_2_fold: forall r_0 r_1 r_2,
  gf_2 (upaco5_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco5_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco5_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <5== paco5_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_5.
  eapply le1_trans; [| apply _paco_3_2_fold]. apply le1_refl.
Qed.

Theorem _paco5_3_0_unfold: forall (MON: _monotone5_3 gf_0) (MON: _monotone5_3 gf_1) (MON: _monotone5_3 gf_2) r_0 r_1 r_2,
  paco5_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 <5== gf_0 (upaco5_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco5_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco5_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  intros. apply curry_adjoint2_5.
  eapply _paco_3_0_unfold; apply monotone5_3_map; assumption.
Qed.

Theorem _paco5_3_1_unfold: forall (MON: _monotone5_3 gf_0) (MON: _monotone5_3 gf_1) (MON: _monotone5_3 gf_2) r_0 r_1 r_2,
  paco5_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 <5== gf_1 (upaco5_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco5_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco5_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  intros. apply curry_adjoint2_5.
  eapply _paco_3_1_unfold; apply monotone5_3_map; assumption.
Qed.

Theorem _paco5_3_2_unfold: forall (MON: _monotone5_3 gf_0) (MON: _monotone5_3 gf_1) (MON: _monotone5_3 gf_2) r_0 r_1 r_2,
  paco5_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 <5== gf_2 (upaco5_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco5_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco5_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  intros. apply curry_adjoint2_5.
  eapply _paco_3_2_unfold; apply monotone5_3_map; assumption.
Qed.

Theorem paco5_3_0_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_0 <5= rr) (CIH: l <5= rr), l <5= paco5_3_0 gf_0 gf_1 gf_2 rr r_1 r_2),
  l <5= paco5_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco5_3_0_acc.
Qed.

Theorem paco5_3_1_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_1 <5= rr) (CIH: l <5= rr), l <5= paco5_3_1 gf_0 gf_1 gf_2 r_0 rr r_2),
  l <5= paco5_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco5_3_1_acc.
Qed.

Theorem paco5_3_2_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_2 <5= rr) (CIH: l <5= rr), l <5= paco5_3_2 gf_0 gf_1 gf_2 r_0 r_1 rr),
  l <5= paco5_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco5_3_2_acc.
Qed.

Theorem paco5_3_0_mon: monotone5_3 (paco5_3_0 gf_0 gf_1 gf_2).
Proof.
  apply monotone5_3_eq.
  apply _paco5_3_0_mon.
Qed.

Theorem paco5_3_1_mon: monotone5_3 (paco5_3_1 gf_0 gf_1 gf_2).
Proof.
  apply monotone5_3_eq.
  apply _paco5_3_1_mon.
Qed.

Theorem paco5_3_2_mon: monotone5_3 (paco5_3_2 gf_0 gf_1 gf_2).
Proof.
  apply monotone5_3_eq.
  apply _paco5_3_2_mon.
Qed.

Theorem upaco5_3_0_mon: monotone5_3 (upaco5_3_0 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 11. intros R  LE0 LE1 LE2.
  destruct R.
  - left. eapply paco5_3_0_mon. apply H. apply LE0. apply LE1. apply LE2.
  - right. apply LE0, H.
Qed.
Theorem upaco5_3_1_mon: monotone5_3 (upaco5_3_1 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 11. intros R  LE0 LE1 LE2.
  destruct R.
  - left. eapply paco5_3_1_mon. apply H. apply LE0. apply LE1. apply LE2.
  - right. apply LE1, H.
Qed.
Theorem upaco5_3_2_mon: monotone5_3 (upaco5_3_2 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 11. intros R  LE0 LE1 LE2.
  destruct R.
  - left. eapply paco5_3_2_mon. apply H. apply LE0. apply LE1. apply LE2.
  - right. apply LE2, H.
Qed.
Theorem paco5_3_0_mult_strong: forall r_0 r_1 r_2,
  paco5_3_0 gf_0 gf_1 gf_2 (upaco5_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco5_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco5_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <5= paco5_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco5_3_0_mult_strong.
Qed.

Theorem paco5_3_1_mult_strong: forall r_0 r_1 r_2,
  paco5_3_1 gf_0 gf_1 gf_2 (upaco5_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco5_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco5_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <5= paco5_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco5_3_1_mult_strong.
Qed.

Theorem paco5_3_2_mult_strong: forall r_0 r_1 r_2,
  paco5_3_2 gf_0 gf_1 gf_2 (upaco5_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco5_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco5_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <5= paco5_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco5_3_2_mult_strong.
Qed.

Corollary paco5_3_0_mult: forall r_0 r_1 r_2,
  paco5_3_0 gf_0 gf_1 gf_2 (paco5_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco5_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco5_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <5= paco5_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco5_3_0_mult_strong, paco5_3_0_mon; [apply PR|..]; intros; left; assumption. Qed.

Corollary paco5_3_1_mult: forall r_0 r_1 r_2,
  paco5_3_1 gf_0 gf_1 gf_2 (paco5_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco5_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco5_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <5= paco5_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco5_3_1_mult_strong, paco5_3_1_mon; [apply PR|..]; intros; left; assumption. Qed.

Corollary paco5_3_2_mult: forall r_0 r_1 r_2,
  paco5_3_2 gf_0 gf_1 gf_2 (paco5_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco5_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco5_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <5= paco5_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco5_3_2_mult_strong, paco5_3_2_mon; [apply PR|..]; intros; left; assumption. Qed.

Theorem paco5_3_0_fold: forall r_0 r_1 r_2,
  gf_0 (upaco5_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco5_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco5_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <5= paco5_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco5_3_0_fold.
Qed.

Theorem paco5_3_1_fold: forall r_0 r_1 r_2,
  gf_1 (upaco5_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco5_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco5_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <5= paco5_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco5_3_1_fold.
Qed.

Theorem paco5_3_2_fold: forall r_0 r_1 r_2,
  gf_2 (upaco5_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco5_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco5_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <5= paco5_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco5_3_2_fold.
Qed.

Theorem paco5_3_0_unfold: forall (MON: monotone5_3 gf_0) (MON: monotone5_3 gf_1) (MON: monotone5_3 gf_2) r_0 r_1 r_2,
  paco5_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 <5= gf_0 (upaco5_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco5_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco5_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  repeat_intros 3. eapply _paco5_3_0_unfold; apply monotone5_3_eq; assumption.
Qed.

Theorem paco5_3_1_unfold: forall (MON: monotone5_3 gf_0) (MON: monotone5_3 gf_1) (MON: monotone5_3 gf_2) r_0 r_1 r_2,
  paco5_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 <5= gf_1 (upaco5_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco5_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco5_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  repeat_intros 3. eapply _paco5_3_1_unfold; apply monotone5_3_eq; assumption.
Qed.

Theorem paco5_3_2_unfold: forall (MON: monotone5_3 gf_0) (MON: monotone5_3 gf_1) (MON: monotone5_3 gf_2) r_0 r_1 r_2,
  paco5_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 <5= gf_2 (upaco5_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco5_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco5_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  repeat_intros 3. eapply _paco5_3_2_unfold; apply monotone5_3_eq; assumption.
Qed.

End Arg5_3.

Arguments paco5_3_0_acc : clear implicits.
Arguments paco5_3_1_acc : clear implicits.
Arguments paco5_3_2_acc : clear implicits.
Arguments paco5_3_0_mon : clear implicits.
Arguments paco5_3_1_mon : clear implicits.
Arguments paco5_3_2_mon : clear implicits.
Arguments upaco5_3_0_mon : clear implicits.
Arguments upaco5_3_1_mon : clear implicits.
Arguments upaco5_3_2_mon : clear implicits.
Arguments paco5_3_0_mult_strong : clear implicits.
Arguments paco5_3_1_mult_strong : clear implicits.
Arguments paco5_3_2_mult_strong : clear implicits.
Arguments paco5_3_0_mult : clear implicits.
Arguments paco5_3_1_mult : clear implicits.
Arguments paco5_3_2_mult : clear implicits.
Arguments paco5_3_0_fold : clear implicits.
Arguments paco5_3_1_fold : clear implicits.
Arguments paco5_3_2_fold : clear implicits.
Arguments paco5_3_0_unfold : clear implicits.
Arguments paco5_3_1_unfold : clear implicits.
Arguments paco5_3_2_unfold : clear implicits.

Global Instance paco5_3_0_inst  (gf_0 gf_1 gf_2 : rel5 T0 T1 T2 T3 T4->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 : paco_class (paco5_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4) :=
{ pacoacc    := paco5_3_0_acc gf_0 gf_1 gf_2;
  pacomult   := paco5_3_0_mult gf_0 gf_1 gf_2;
  pacofold   := paco5_3_0_fold gf_0 gf_1 gf_2;
  pacounfold := paco5_3_0_unfold gf_0 gf_1 gf_2 }.

Global Instance paco5_3_1_inst  (gf_0 gf_1 gf_2 : rel5 T0 T1 T2 T3 T4->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 : paco_class (paco5_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4) :=
{ pacoacc    := paco5_3_1_acc gf_0 gf_1 gf_2;
  pacomult   := paco5_3_1_mult gf_0 gf_1 gf_2;
  pacofold   := paco5_3_1_fold gf_0 gf_1 gf_2;
  pacounfold := paco5_3_1_unfold gf_0 gf_1 gf_2 }.

Global Instance paco5_3_2_inst  (gf_0 gf_1 gf_2 : rel5 T0 T1 T2 T3 T4->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 : paco_class (paco5_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4) :=
{ pacoacc    := paco5_3_2_acc gf_0 gf_1 gf_2;
  pacomult   := paco5_3_2_mult gf_0 gf_1 gf_2;
  pacofold   := paco5_3_2_fold gf_0 gf_1 gf_2;
  pacounfold := paco5_3_2_unfold gf_0 gf_1 gf_2 }.

End PACO5.

Global Opaque paco5.

Hint Unfold upaco5.
Hint Resolve paco5_fold.
Hint Unfold monotone5.

Global Opaque paco5_2_0.
Global Opaque paco5_2_1.

Hint Unfold upaco5_2_0.
Hint Unfold upaco5_2_1.
Hint Resolve paco5_2_0_fold.
Hint Resolve paco5_2_1_fold.
Hint Unfold monotone5_2.

Global Opaque paco5_3_0.
Global Opaque paco5_3_1.
Global Opaque paco5_3_2.

Hint Unfold upaco5_3_0.
Hint Unfold upaco5_3_1.
Hint Unfold upaco5_3_2.
Hint Resolve paco5_3_0_fold.
Hint Resolve paco5_3_1_fold.
Hint Resolve paco5_3_2_fold.
Hint Unfold monotone5_3.

