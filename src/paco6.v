Require Export paconotation pacotacuser.
Require Import paconotation_internal pacotac pacon.
Set Implicit Arguments.

Section PACO6.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.

Record sig6T :=
  exist6T { 
      proj6T0: @T0;
      proj6T1: @T1 proj6T0;
      proj6T2: @T2 proj6T0 proj6T1;
      proj6T3: @T3 proj6T0 proj6T1 proj6T2;
      proj6T4: @T4 proj6T0 proj6T1 proj6T2 proj6T3;
      proj6T5: @T5 proj6T0 proj6T1 proj6T2 proj6T3 proj6T4;
    }.

Definition uncurry6 (R: rel6 T0 T1 T2 T3 T4 T5): rel1 sig6T := fun x => R (proj6T0 x) (proj6T1 x) (proj6T2 x) (proj6T3 x) (proj6T4 x) (proj6T5 x).

Definition curry6 (R: rel1 sig6T): rel6 T0 T1 T2 T3 T4 T5 :=
  fun x0 x1 x2 x3 x4 x5 => R (exist6T x5).

Lemma uncurry_map6 r0 r1 (LE : r0 <6== r1) : uncurry6 r0 <1== uncurry6 r1.
Proof. intros [] H. apply LE. auto. Qed.

Lemma uncurry_map_rev6 r0 r1 (LE: uncurry6 r0 <1== uncurry6 r1) : r0 <6== r1.
Proof.
  repeat_intros 6. intros H. apply (LE (exist6T x5) H).
Qed.

Lemma curry_map6 r0 r1 (LE: r0 <1== r1) : curry6 r0 <6== curry6 r1.
Proof. 
  repeat_intros 6. intros H. apply (LE (exist6T x5) H).
Qed.

Lemma curry_map_rev6 r0 r1 (LE: curry6 r0 <6== curry6 r1) : r0 <1== r1.
Proof. 
  intros [] H. apply LE. apply H.
Qed.

Lemma uncurry_bij1_6 r : curry6 (uncurry6 r) <6== r.
Proof. unfold le6. repeat_intros 6; auto. Qed.

Lemma uncurry_bij2_6 r : r <6== curry6 (uncurry6 r).
Proof. unfold le6. repeat_intros 6; auto. Qed.

Lemma curry_bij1_6 r : uncurry6 (curry6 r) <1== r.
Proof. intros []; auto. Qed.

Lemma curry_bij2_6 r : r <1== uncurry6 (curry6 r).
Proof. intros []; auto. Qed.

Lemma uncurry_adjoint1_6 r0 r1 (LE: uncurry6 r0 <1== r1) : r0 <6== curry6 r1.
Proof.
  apply uncurry_map_rev6. eapply le1_trans; [eauto|]. apply curry_bij2_6.
Qed.

Lemma uncurry_adjoint2_6 r0 r1 (LE: r0 <6== curry6 r1) : uncurry6 r0 <1== r1.
Proof.
  apply curry_map_rev6. eapply le6_trans; [|eauto]. apply uncurry_bij2_6.
Qed.

Lemma curry_adjoint1_6 r0 r1 (LE: curry6 r0 <6== r1) : r0 <1== uncurry6 r1.
Proof.
  apply curry_map_rev6. eapply le6_trans; [eauto|]. apply uncurry_bij2_6.
Qed.

Lemma curry_adjoint2_6 r0 r1 (LE: r0 <1== uncurry6 r1) : curry6 r0 <6== r1.
Proof.
  apply uncurry_map_rev6. eapply le1_trans; [|eauto]. apply curry_bij1_6.
Qed.

(** ** Predicates of Arity 6
*)

Section Arg6_def.
Variable gf : rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5.
Arguments gf : clear implicits.

Definition paco6( r: rel6 T0 T1 T2 T3 T4 T5) : rel6 T0 T1 T2 T3 T4 T5 :=
  curry6 (paco (fun R0 => uncurry6 (gf (curry6 R0))) (uncurry6 r)).

Definition upaco6( r: rel6 T0 T1 T2 T3 T4 T5) := paco6 r \6/ r.
End Arg6_def.
Arguments paco6 : clear implicits.
Arguments upaco6 : clear implicits.
Hint Unfold upaco6.

Section Arg6_2_def.
Variable gf_0 gf_1 : rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.

Definition paco6_2_0( r_0 r_1: rel6 T0 T1 T2 T3 T4 T5) : rel6 T0 T1 T2 T3 T4 T5 :=
  curry6 (paco_2_0 (fun R0 R1 => uncurry6 (gf_0 (curry6 R0) (curry6 R1))) (fun R0 R1 => uncurry6 (gf_1 (curry6 R0) (curry6 R1))) (uncurry6 r_0) (uncurry6 r_1)).

Definition paco6_2_1( r_0 r_1: rel6 T0 T1 T2 T3 T4 T5) : rel6 T0 T1 T2 T3 T4 T5 :=
  curry6 (paco_2_1 (fun R0 R1 => uncurry6 (gf_0 (curry6 R0) (curry6 R1))) (fun R0 R1 => uncurry6 (gf_1 (curry6 R0) (curry6 R1))) (uncurry6 r_0) (uncurry6 r_1)).

Definition upaco6_2_0( r_0 r_1: rel6 T0 T1 T2 T3 T4 T5) := paco6_2_0 r_0 r_1 \6/ r_0.
Definition upaco6_2_1( r_0 r_1: rel6 T0 T1 T2 T3 T4 T5) := paco6_2_1 r_0 r_1 \6/ r_1.
End Arg6_2_def.
Arguments paco6_2_0 : clear implicits.
Arguments upaco6_2_0 : clear implicits.
Hint Unfold upaco6_2_0.
Arguments paco6_2_1 : clear implicits.
Arguments upaco6_2_1 : clear implicits.
Hint Unfold upaco6_2_1.

Section Arg6_3_def.
Variable gf_0 gf_1 gf_2 : rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.
Arguments gf_2 : clear implicits.

Definition paco6_3_0( r_0 r_1 r_2: rel6 T0 T1 T2 T3 T4 T5) : rel6 T0 T1 T2 T3 T4 T5 :=
  curry6 (paco_3_0 (fun R0 R1 R2 => uncurry6 (gf_0 (curry6 R0) (curry6 R1) (curry6 R2))) (fun R0 R1 R2 => uncurry6 (gf_1 (curry6 R0) (curry6 R1) (curry6 R2))) (fun R0 R1 R2 => uncurry6 (gf_2 (curry6 R0) (curry6 R1) (curry6 R2))) (uncurry6 r_0) (uncurry6 r_1) (uncurry6 r_2)).

Definition paco6_3_1( r_0 r_1 r_2: rel6 T0 T1 T2 T3 T4 T5) : rel6 T0 T1 T2 T3 T4 T5 :=
  curry6 (paco_3_1 (fun R0 R1 R2 => uncurry6 (gf_0 (curry6 R0) (curry6 R1) (curry6 R2))) (fun R0 R1 R2 => uncurry6 (gf_1 (curry6 R0) (curry6 R1) (curry6 R2))) (fun R0 R1 R2 => uncurry6 (gf_2 (curry6 R0) (curry6 R1) (curry6 R2))) (uncurry6 r_0) (uncurry6 r_1) (uncurry6 r_2)).

Definition paco6_3_2( r_0 r_1 r_2: rel6 T0 T1 T2 T3 T4 T5) : rel6 T0 T1 T2 T3 T4 T5 :=
  curry6 (paco_3_2 (fun R0 R1 R2 => uncurry6 (gf_0 (curry6 R0) (curry6 R1) (curry6 R2))) (fun R0 R1 R2 => uncurry6 (gf_1 (curry6 R0) (curry6 R1) (curry6 R2))) (fun R0 R1 R2 => uncurry6 (gf_2 (curry6 R0) (curry6 R1) (curry6 R2))) (uncurry6 r_0) (uncurry6 r_1) (uncurry6 r_2)).

Definition upaco6_3_0( r_0 r_1 r_2: rel6 T0 T1 T2 T3 T4 T5) := paco6_3_0 r_0 r_1 r_2 \6/ r_0.
Definition upaco6_3_1( r_0 r_1 r_2: rel6 T0 T1 T2 T3 T4 T5) := paco6_3_1 r_0 r_1 r_2 \6/ r_1.
Definition upaco6_3_2( r_0 r_1 r_2: rel6 T0 T1 T2 T3 T4 T5) := paco6_3_2 r_0 r_1 r_2 \6/ r_2.
End Arg6_3_def.
Arguments paco6_3_0 : clear implicits.
Arguments upaco6_3_0 : clear implicits.
Hint Unfold upaco6_3_0.
Arguments paco6_3_1 : clear implicits.
Arguments upaco6_3_1 : clear implicits.
Hint Unfold upaco6_3_1.
Arguments paco6_3_2 : clear implicits.
Arguments upaco6_3_2 : clear implicits.
Hint Unfold upaco6_3_2.

(** 1 Mutual Coinduction *)

Section Arg6_1.

Definition monotone6 (gf: rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5) :=
  forall x0 x1 x2 x3 x4 x5 r r' (IN: gf r x0 x1 x2 x3 x4 x5) (LE: r <6= r'), gf r' x0 x1 x2 x3 x4 x5.

Definition _monotone6 (gf: rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5) :=
  forall r r'(LE: r <6= r'), gf r <6== gf r'.

Lemma monotone6_eq (gf: rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5) :
  monotone6 gf <-> _monotone6 gf.
Proof. unfold monotone6, _monotone6, le6. split; eauto. Qed.

Lemma monotone6_map (gf: rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5)
      (MON: _monotone6 gf) :
  _monotone (fun R0 => uncurry6 (gf (curry6 R0))).
Proof.
  repeat_intros 3. apply uncurry_map6. apply MON; apply curry_map6; auto.
Qed.

Variable gf : rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5.
Arguments gf : clear implicits.

Theorem _paco6_mon: _monotone6 (paco6 gf).
Proof.
  repeat_intros 3. eapply curry_map6, _paco_mon; apply uncurry_map6; auto.
Qed.

Theorem _paco6_acc: forall
  l r (OBG: forall rr (INC: r <6== rr) (CIH: l <6== rr), l <6== paco6 gf rr),
  l <6== paco6 gf r.
Proof.
  intros. apply uncurry_adjoint1_6.
  eapply _paco_acc. intros.
  apply uncurry_adjoint1_6 in INC. apply uncurry_adjoint1_6 in CIH.
  apply uncurry_adjoint2_6.
  eapply le6_trans. eapply (OBG _ INC CIH).
  apply curry_map6.
  apply _paco_mon; try apply le1_refl; apply curry_bij1_6.
Qed.

Theorem _paco6_mult_strong: forall r,
  paco6 gf (upaco6 gf r) <6== paco6 gf r.
Proof.
  intros. apply curry_map6.
  eapply le1_trans; [| eapply _paco_mult_strong].
  apply _paco_mon; intros []; eauto.
Qed.

Theorem _paco6_fold: forall r,
  gf (upaco6 gf r) <6== paco6 gf r.
Proof.
  intros. apply uncurry_adjoint1_6.
  eapply le1_trans; [| apply _paco_fold]. apply le1_refl.
Qed.

Theorem _paco6_unfold: forall (MON: _monotone6 gf) r,
  paco6 gf r <6== gf (upaco6 gf r).
Proof.
  intros. apply curry_adjoint2_6.
  eapply _paco_unfold; apply monotone6_map; auto.
Qed.

Theorem paco6_acc: forall
  l r (OBG: forall rr (INC: r <6= rr) (CIH: l <6= rr), l <6= paco6 gf rr),
  l <6= paco6 gf r.
Proof.
  apply _paco6_acc.
Qed.

Theorem paco6_mon: monotone6 (paco6 gf).
Proof.
  apply monotone6_eq.
  apply _paco6_mon.
Qed.

Theorem paco6_mult_strong: forall r,
  paco6 gf (upaco6 gf r) <6= paco6 gf r.
Proof.
  apply _paco6_mult_strong.
Qed.

Corollary paco6_mult: forall r,
  paco6 gf (paco6 gf r) <6= paco6 gf r.
Proof. intros; eapply paco6_mult_strong, paco6_mon; eauto. Qed.

Theorem paco6_fold: forall r,
  gf (upaco6 gf r) <6= paco6 gf r.
Proof.
  apply _paco6_fold.
Qed.

Theorem paco6_unfold: forall (MON: monotone6 gf) r,
  paco6 gf r <6= gf (upaco6 gf r).
Proof.
  repeat_intros 1. eapply _paco6_unfold; apply monotone6_eq; auto.
Qed.

End Arg6_1.

Arguments paco6_acc : clear implicits.
Arguments paco6_mon : clear implicits.
Arguments paco6_mult_strong : clear implicits.
Arguments paco6_mult : clear implicits.
Arguments paco6_fold : clear implicits.
Arguments paco6_unfold : clear implicits.

Global Instance paco6_inst  (gf : rel6 T0 T1 T2 T3 T4 T5->_) r x0 x1 x2 x3 x4 x5 : paco_class (paco6 gf r x0 x1 x2 x3 x4 x5) :=
{ pacoacc    := paco6_acc gf;
  pacomult   := paco6_mult gf;
  pacofold   := paco6_fold gf;
  pacounfold := paco6_unfold gf }.

(** 2 Mutual Coinduction *)

Section Arg6_2.

Definition monotone6_2 (gf: rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5) :=
  forall x0 x1 x2 x3 x4 x5 r_0 r_1 r'_0 r'_1 (IN: gf r_0 r_1 x0 x1 x2 x3 x4 x5) (LE_0: r_0 <6= r'_0)(LE_1: r_1 <6= r'_1), gf r'_0 r'_1 x0 x1 x2 x3 x4 x5.

Definition _monotone6_2 (gf: rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5) :=
  forall r_0 r_1 r'_0 r'_1(LE_0: r_0 <6= r'_0)(LE_1: r_1 <6= r'_1), gf r_0 r_1 <6== gf r'_0 r'_1.

Lemma monotone6_2_eq (gf: rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5) :
  monotone6_2 gf <-> _monotone6_2 gf.
Proof. unfold monotone6_2, _monotone6_2, le6. split; eauto. Qed.

Lemma monotone6_2_map (gf: rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5)
      (MON: _monotone6_2 gf) :
  _monotone_2 (fun R0 R1 => uncurry6 (gf (curry6 R0) (curry6 R1))).
Proof.
  repeat_intros 6. apply uncurry_map6. apply MON; apply curry_map6; auto.
Qed.

Variable gf_0 gf_1 : rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.

Theorem _paco6_2_0_mon: _monotone6_2 (paco6_2_0 gf_0 gf_1).
Proof.
  repeat_intros 6. eapply curry_map6, _paco_2_0_mon; apply uncurry_map6; auto.
Qed.

Theorem _paco6_2_1_mon: _monotone6_2 (paco6_2_1 gf_0 gf_1).
Proof.
  repeat_intros 6. eapply curry_map6, _paco_2_1_mon; apply uncurry_map6; auto.
Qed.

Theorem _paco6_2_0_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_0 <6== rr) (CIH: l <6== rr), l <6== paco6_2_0 gf_0 gf_1 rr r_1),
  l <6== paco6_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_6.
  eapply _paco_2_0_acc. intros.
  apply uncurry_adjoint1_6 in INC. apply uncurry_adjoint1_6 in CIH.
  apply uncurry_adjoint2_6.
  eapply le6_trans. eapply (OBG _ INC CIH).
  apply curry_map6.
  apply _paco_2_0_mon; try apply le1_refl; apply curry_bij1_6.
Qed.

Theorem _paco6_2_1_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_1 <6== rr) (CIH: l <6== rr), l <6== paco6_2_1 gf_0 gf_1 r_0 rr),
  l <6== paco6_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_6.
  eapply _paco_2_1_acc. intros.
  apply uncurry_adjoint1_6 in INC. apply uncurry_adjoint1_6 in CIH.
  apply uncurry_adjoint2_6.
  eapply le6_trans. eapply (OBG _ INC CIH).
  apply curry_map6.
  apply _paco_2_1_mon; try apply le1_refl; apply curry_bij1_6.
Qed.

Theorem _paco6_2_0_mult_strong: forall r_0 r_1,
  paco6_2_0 gf_0 gf_1 (upaco6_2_0 gf_0 gf_1 r_0 r_1) (upaco6_2_1 gf_0 gf_1 r_0 r_1) <6== paco6_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply curry_map6.
  eapply le1_trans; [| eapply _paco_2_0_mult_strong].
  apply _paco_2_0_mon; intros []; eauto.
Qed.

Theorem _paco6_2_1_mult_strong: forall r_0 r_1,
  paco6_2_1 gf_0 gf_1 (upaco6_2_0 gf_0 gf_1 r_0 r_1) (upaco6_2_1 gf_0 gf_1 r_0 r_1) <6== paco6_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply curry_map6.
  eapply le1_trans; [| eapply _paco_2_1_mult_strong].
  apply _paco_2_1_mon; intros []; eauto.
Qed.

Theorem _paco6_2_0_fold: forall r_0 r_1,
  gf_0 (upaco6_2_0 gf_0 gf_1 r_0 r_1) (upaco6_2_1 gf_0 gf_1 r_0 r_1) <6== paco6_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_6.
  eapply le1_trans; [| apply _paco_2_0_fold]. apply le1_refl.
Qed.

Theorem _paco6_2_1_fold: forall r_0 r_1,
  gf_1 (upaco6_2_0 gf_0 gf_1 r_0 r_1) (upaco6_2_1 gf_0 gf_1 r_0 r_1) <6== paco6_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_6.
  eapply le1_trans; [| apply _paco_2_1_fold]. apply le1_refl.
Qed.

Theorem _paco6_2_0_unfold: forall (MON: _monotone6_2 gf_0) (MON: _monotone6_2 gf_1) r_0 r_1,
  paco6_2_0 gf_0 gf_1 r_0 r_1 <6== gf_0 (upaco6_2_0 gf_0 gf_1 r_0 r_1) (upaco6_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  intros. apply curry_adjoint2_6.
  eapply _paco_2_0_unfold; apply monotone6_2_map; auto.
Qed.

Theorem _paco6_2_1_unfold: forall (MON: _monotone6_2 gf_0) (MON: _monotone6_2 gf_1) r_0 r_1,
  paco6_2_1 gf_0 gf_1 r_0 r_1 <6== gf_1 (upaco6_2_0 gf_0 gf_1 r_0 r_1) (upaco6_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  intros. apply curry_adjoint2_6.
  eapply _paco_2_1_unfold; apply monotone6_2_map; auto.
Qed.

Theorem paco6_2_0_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_0 <6= rr) (CIH: l <6= rr), l <6= paco6_2_0 gf_0 gf_1 rr r_1),
  l <6= paco6_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco6_2_0_acc.
Qed.

Theorem paco6_2_1_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_1 <6= rr) (CIH: l <6= rr), l <6= paco6_2_1 gf_0 gf_1 r_0 rr),
  l <6= paco6_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco6_2_1_acc.
Qed.

Theorem paco6_2_0_mon: monotone6_2 (paco6_2_0 gf_0 gf_1).
Proof.
  apply monotone6_2_eq.
  apply _paco6_2_0_mon.
Qed.

Theorem paco6_2_1_mon: monotone6_2 (paco6_2_1 gf_0 gf_1).
Proof.
  apply monotone6_2_eq.
  apply _paco6_2_1_mon.
Qed.

Theorem paco6_2_0_mult_strong: forall r_0 r_1,
  paco6_2_0 gf_0 gf_1 (upaco6_2_0 gf_0 gf_1 r_0 r_1) (upaco6_2_1 gf_0 gf_1 r_0 r_1) <6= paco6_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco6_2_0_mult_strong.
Qed.

Theorem paco6_2_1_mult_strong: forall r_0 r_1,
  paco6_2_1 gf_0 gf_1 (upaco6_2_0 gf_0 gf_1 r_0 r_1) (upaco6_2_1 gf_0 gf_1 r_0 r_1) <6= paco6_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco6_2_1_mult_strong.
Qed.

Corollary paco6_2_0_mult: forall r_0 r_1,
  paco6_2_0 gf_0 gf_1 (paco6_2_0 gf_0 gf_1 r_0 r_1) (paco6_2_1 gf_0 gf_1 r_0 r_1) <6= paco6_2_0 gf_0 gf_1 r_0 r_1.
Proof. intros; eapply paco6_2_0_mult_strong, paco6_2_0_mon; eauto. Qed.

Corollary paco6_2_1_mult: forall r_0 r_1,
  paco6_2_1 gf_0 gf_1 (paco6_2_0 gf_0 gf_1 r_0 r_1) (paco6_2_1 gf_0 gf_1 r_0 r_1) <6= paco6_2_1 gf_0 gf_1 r_0 r_1.
Proof. intros; eapply paco6_2_1_mult_strong, paco6_2_1_mon; eauto. Qed.

Theorem paco6_2_0_fold: forall r_0 r_1,
  gf_0 (upaco6_2_0 gf_0 gf_1 r_0 r_1) (upaco6_2_1 gf_0 gf_1 r_0 r_1) <6= paco6_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco6_2_0_fold.
Qed.

Theorem paco6_2_1_fold: forall r_0 r_1,
  gf_1 (upaco6_2_0 gf_0 gf_1 r_0 r_1) (upaco6_2_1 gf_0 gf_1 r_0 r_1) <6= paco6_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco6_2_1_fold.
Qed.

Theorem paco6_2_0_unfold: forall (MON: monotone6_2 gf_0) (MON: monotone6_2 gf_1) r_0 r_1,
  paco6_2_0 gf_0 gf_1 r_0 r_1 <6= gf_0 (upaco6_2_0 gf_0 gf_1 r_0 r_1) (upaco6_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  repeat_intros 2. eapply _paco6_2_0_unfold; apply monotone6_2_eq; auto.
Qed.

Theorem paco6_2_1_unfold: forall (MON: monotone6_2 gf_0) (MON: monotone6_2 gf_1) r_0 r_1,
  paco6_2_1 gf_0 gf_1 r_0 r_1 <6= gf_1 (upaco6_2_0 gf_0 gf_1 r_0 r_1) (upaco6_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  repeat_intros 2. eapply _paco6_2_1_unfold; apply monotone6_2_eq; auto.
Qed.

End Arg6_2.

Arguments paco6_2_0_acc : clear implicits.
Arguments paco6_2_1_acc : clear implicits.
Arguments paco6_2_0_mon : clear implicits.
Arguments paco6_2_1_mon : clear implicits.
Arguments paco6_2_0_mult_strong : clear implicits.
Arguments paco6_2_1_mult_strong : clear implicits.
Arguments paco6_2_0_mult : clear implicits.
Arguments paco6_2_1_mult : clear implicits.
Arguments paco6_2_0_fold : clear implicits.
Arguments paco6_2_1_fold : clear implicits.
Arguments paco6_2_0_unfold : clear implicits.
Arguments paco6_2_1_unfold : clear implicits.

Global Instance paco6_2_0_inst  (gf_0 gf_1 : rel6 T0 T1 T2 T3 T4 T5->_) r_0 r_1 x0 x1 x2 x3 x4 x5 : paco_class (paco6_2_0 gf_0 gf_1 r_0 r_1 x0 x1 x2 x3 x4 x5) :=
{ pacoacc    := paco6_2_0_acc gf_0 gf_1;
  pacomult   := paco6_2_0_mult gf_0 gf_1;
  pacofold   := paco6_2_0_fold gf_0 gf_1;
  pacounfold := paco6_2_0_unfold gf_0 gf_1 }.

Global Instance paco6_2_1_inst  (gf_0 gf_1 : rel6 T0 T1 T2 T3 T4 T5->_) r_0 r_1 x0 x1 x2 x3 x4 x5 : paco_class (paco6_2_1 gf_0 gf_1 r_0 r_1 x0 x1 x2 x3 x4 x5) :=
{ pacoacc    := paco6_2_1_acc gf_0 gf_1;
  pacomult   := paco6_2_1_mult gf_0 gf_1;
  pacofold   := paco6_2_1_fold gf_0 gf_1;
  pacounfold := paco6_2_1_unfold gf_0 gf_1 }.

(** 3 Mutual Coinduction *)

Section Arg6_3.

Definition monotone6_3 (gf: rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5) :=
  forall x0 x1 x2 x3 x4 x5 r_0 r_1 r_2 r'_0 r'_1 r'_2 (IN: gf r_0 r_1 r_2 x0 x1 x2 x3 x4 x5) (LE_0: r_0 <6= r'_0)(LE_1: r_1 <6= r'_1)(LE_2: r_2 <6= r'_2), gf r'_0 r'_1 r'_2 x0 x1 x2 x3 x4 x5.

Definition _monotone6_3 (gf: rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5) :=
  forall r_0 r_1 r_2 r'_0 r'_1 r'_2(LE_0: r_0 <6= r'_0)(LE_1: r_1 <6= r'_1)(LE_2: r_2 <6= r'_2), gf r_0 r_1 r_2 <6== gf r'_0 r'_1 r'_2.

Lemma monotone6_3_eq (gf: rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5) :
  monotone6_3 gf <-> _monotone6_3 gf.
Proof. unfold monotone6_3, _monotone6_3, le6. split; eauto. Qed.

Lemma monotone6_3_map (gf: rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5)
      (MON: _monotone6_3 gf) :
  _monotone_3 (fun R0 R1 R2 => uncurry6 (gf (curry6 R0) (curry6 R1) (curry6 R2))).
Proof.
  repeat_intros 9. apply uncurry_map6. apply MON; apply curry_map6; auto.
Qed.

Variable gf_0 gf_1 gf_2 : rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.
Arguments gf_2 : clear implicits.

Theorem _paco6_3_0_mon: _monotone6_3 (paco6_3_0 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 9. eapply curry_map6, _paco_3_0_mon; apply uncurry_map6; auto.
Qed.

Theorem _paco6_3_1_mon: _monotone6_3 (paco6_3_1 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 9. eapply curry_map6, _paco_3_1_mon; apply uncurry_map6; auto.
Qed.

Theorem _paco6_3_2_mon: _monotone6_3 (paco6_3_2 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 9. eapply curry_map6, _paco_3_2_mon; apply uncurry_map6; auto.
Qed.

Theorem _paco6_3_0_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_0 <6== rr) (CIH: l <6== rr), l <6== paco6_3_0 gf_0 gf_1 gf_2 rr r_1 r_2),
  l <6== paco6_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_6.
  eapply _paco_3_0_acc. intros.
  apply uncurry_adjoint1_6 in INC. apply uncurry_adjoint1_6 in CIH.
  apply uncurry_adjoint2_6.
  eapply le6_trans. eapply (OBG _ INC CIH).
  apply curry_map6.
  apply _paco_3_0_mon; try apply le1_refl; apply curry_bij1_6.
Qed.

Theorem _paco6_3_1_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_1 <6== rr) (CIH: l <6== rr), l <6== paco6_3_1 gf_0 gf_1 gf_2 r_0 rr r_2),
  l <6== paco6_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_6.
  eapply _paco_3_1_acc. intros.
  apply uncurry_adjoint1_6 in INC. apply uncurry_adjoint1_6 in CIH.
  apply uncurry_adjoint2_6.
  eapply le6_trans. eapply (OBG _ INC CIH).
  apply curry_map6.
  apply _paco_3_1_mon; try apply le1_refl; apply curry_bij1_6.
Qed.

Theorem _paco6_3_2_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_2 <6== rr) (CIH: l <6== rr), l <6== paco6_3_2 gf_0 gf_1 gf_2 r_0 r_1 rr),
  l <6== paco6_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_6.
  eapply _paco_3_2_acc. intros.
  apply uncurry_adjoint1_6 in INC. apply uncurry_adjoint1_6 in CIH.
  apply uncurry_adjoint2_6.
  eapply le6_trans. eapply (OBG _ INC CIH).
  apply curry_map6.
  apply _paco_3_2_mon; try apply le1_refl; apply curry_bij1_6.
Qed.

Theorem _paco6_3_0_mult_strong: forall r_0 r_1 r_2,
  paco6_3_0 gf_0 gf_1 gf_2 (upaco6_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco6_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco6_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <6== paco6_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply curry_map6.
  eapply le1_trans; [| eapply _paco_3_0_mult_strong].
  apply _paco_3_0_mon; intros []; eauto.
Qed.

Theorem _paco6_3_1_mult_strong: forall r_0 r_1 r_2,
  paco6_3_1 gf_0 gf_1 gf_2 (upaco6_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco6_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco6_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <6== paco6_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply curry_map6.
  eapply le1_trans; [| eapply _paco_3_1_mult_strong].
  apply _paco_3_1_mon; intros []; eauto.
Qed.

Theorem _paco6_3_2_mult_strong: forall r_0 r_1 r_2,
  paco6_3_2 gf_0 gf_1 gf_2 (upaco6_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco6_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco6_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <6== paco6_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply curry_map6.
  eapply le1_trans; [| eapply _paco_3_2_mult_strong].
  apply _paco_3_2_mon; intros []; eauto.
Qed.

Theorem _paco6_3_0_fold: forall r_0 r_1 r_2,
  gf_0 (upaco6_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco6_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco6_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <6== paco6_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_6.
  eapply le1_trans; [| apply _paco_3_0_fold]. apply le1_refl.
Qed.

Theorem _paco6_3_1_fold: forall r_0 r_1 r_2,
  gf_1 (upaco6_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco6_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco6_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <6== paco6_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_6.
  eapply le1_trans; [| apply _paco_3_1_fold]. apply le1_refl.
Qed.

Theorem _paco6_3_2_fold: forall r_0 r_1 r_2,
  gf_2 (upaco6_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco6_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco6_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <6== paco6_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_6.
  eapply le1_trans; [| apply _paco_3_2_fold]. apply le1_refl.
Qed.

Theorem _paco6_3_0_unfold: forall (MON: _monotone6_3 gf_0) (MON: _monotone6_3 gf_1) (MON: _monotone6_3 gf_2) r_0 r_1 r_2,
  paco6_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 <6== gf_0 (upaco6_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco6_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco6_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  intros. apply curry_adjoint2_6.
  eapply _paco_3_0_unfold; apply monotone6_3_map; auto.
Qed.

Theorem _paco6_3_1_unfold: forall (MON: _monotone6_3 gf_0) (MON: _monotone6_3 gf_1) (MON: _monotone6_3 gf_2) r_0 r_1 r_2,
  paco6_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 <6== gf_1 (upaco6_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco6_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco6_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  intros. apply curry_adjoint2_6.
  eapply _paco_3_1_unfold; apply monotone6_3_map; auto.
Qed.

Theorem _paco6_3_2_unfold: forall (MON: _monotone6_3 gf_0) (MON: _monotone6_3 gf_1) (MON: _monotone6_3 gf_2) r_0 r_1 r_2,
  paco6_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 <6== gf_2 (upaco6_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco6_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco6_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  intros. apply curry_adjoint2_6.
  eapply _paco_3_2_unfold; apply monotone6_3_map; auto.
Qed.

Theorem paco6_3_0_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_0 <6= rr) (CIH: l <6= rr), l <6= paco6_3_0 gf_0 gf_1 gf_2 rr r_1 r_2),
  l <6= paco6_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco6_3_0_acc.
Qed.

Theorem paco6_3_1_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_1 <6= rr) (CIH: l <6= rr), l <6= paco6_3_1 gf_0 gf_1 gf_2 r_0 rr r_2),
  l <6= paco6_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco6_3_1_acc.
Qed.

Theorem paco6_3_2_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_2 <6= rr) (CIH: l <6= rr), l <6= paco6_3_2 gf_0 gf_1 gf_2 r_0 r_1 rr),
  l <6= paco6_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco6_3_2_acc.
Qed.

Theorem paco6_3_0_mon: monotone6_3 (paco6_3_0 gf_0 gf_1 gf_2).
Proof.
  apply monotone6_3_eq.
  apply _paco6_3_0_mon.
Qed.

Theorem paco6_3_1_mon: monotone6_3 (paco6_3_1 gf_0 gf_1 gf_2).
Proof.
  apply monotone6_3_eq.
  apply _paco6_3_1_mon.
Qed.

Theorem paco6_3_2_mon: monotone6_3 (paco6_3_2 gf_0 gf_1 gf_2).
Proof.
  apply monotone6_3_eq.
  apply _paco6_3_2_mon.
Qed.

Theorem paco6_3_0_mult_strong: forall r_0 r_1 r_2,
  paco6_3_0 gf_0 gf_1 gf_2 (upaco6_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco6_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco6_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <6= paco6_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco6_3_0_mult_strong.
Qed.

Theorem paco6_3_1_mult_strong: forall r_0 r_1 r_2,
  paco6_3_1 gf_0 gf_1 gf_2 (upaco6_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco6_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco6_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <6= paco6_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco6_3_1_mult_strong.
Qed.

Theorem paco6_3_2_mult_strong: forall r_0 r_1 r_2,
  paco6_3_2 gf_0 gf_1 gf_2 (upaco6_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco6_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco6_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <6= paco6_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco6_3_2_mult_strong.
Qed.

Corollary paco6_3_0_mult: forall r_0 r_1 r_2,
  paco6_3_0 gf_0 gf_1 gf_2 (paco6_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco6_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco6_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <6= paco6_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco6_3_0_mult_strong, paco6_3_0_mon; eauto. Qed.

Corollary paco6_3_1_mult: forall r_0 r_1 r_2,
  paco6_3_1 gf_0 gf_1 gf_2 (paco6_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco6_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco6_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <6= paco6_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco6_3_1_mult_strong, paco6_3_1_mon; eauto. Qed.

Corollary paco6_3_2_mult: forall r_0 r_1 r_2,
  paco6_3_2 gf_0 gf_1 gf_2 (paco6_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco6_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco6_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <6= paco6_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco6_3_2_mult_strong, paco6_3_2_mon; eauto. Qed.

Theorem paco6_3_0_fold: forall r_0 r_1 r_2,
  gf_0 (upaco6_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco6_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco6_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <6= paco6_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco6_3_0_fold.
Qed.

Theorem paco6_3_1_fold: forall r_0 r_1 r_2,
  gf_1 (upaco6_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco6_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco6_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <6= paco6_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco6_3_1_fold.
Qed.

Theorem paco6_3_2_fold: forall r_0 r_1 r_2,
  gf_2 (upaco6_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco6_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco6_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <6= paco6_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco6_3_2_fold.
Qed.

Theorem paco6_3_0_unfold: forall (MON: monotone6_3 gf_0) (MON: monotone6_3 gf_1) (MON: monotone6_3 gf_2) r_0 r_1 r_2,
  paco6_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 <6= gf_0 (upaco6_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco6_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco6_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  repeat_intros 3. eapply _paco6_3_0_unfold; apply monotone6_3_eq; auto.
Qed.

Theorem paco6_3_1_unfold: forall (MON: monotone6_3 gf_0) (MON: monotone6_3 gf_1) (MON: monotone6_3 gf_2) r_0 r_1 r_2,
  paco6_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 <6= gf_1 (upaco6_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco6_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco6_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  repeat_intros 3. eapply _paco6_3_1_unfold; apply monotone6_3_eq; auto.
Qed.

Theorem paco6_3_2_unfold: forall (MON: monotone6_3 gf_0) (MON: monotone6_3 gf_1) (MON: monotone6_3 gf_2) r_0 r_1 r_2,
  paco6_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 <6= gf_2 (upaco6_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco6_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco6_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  repeat_intros 3. eapply _paco6_3_2_unfold; apply monotone6_3_eq; auto.
Qed.

End Arg6_3.

Arguments paco6_3_0_acc : clear implicits.
Arguments paco6_3_1_acc : clear implicits.
Arguments paco6_3_2_acc : clear implicits.
Arguments paco6_3_0_mon : clear implicits.
Arguments paco6_3_1_mon : clear implicits.
Arguments paco6_3_2_mon : clear implicits.
Arguments paco6_3_0_mult_strong : clear implicits.
Arguments paco6_3_1_mult_strong : clear implicits.
Arguments paco6_3_2_mult_strong : clear implicits.
Arguments paco6_3_0_mult : clear implicits.
Arguments paco6_3_1_mult : clear implicits.
Arguments paco6_3_2_mult : clear implicits.
Arguments paco6_3_0_fold : clear implicits.
Arguments paco6_3_1_fold : clear implicits.
Arguments paco6_3_2_fold : clear implicits.
Arguments paco6_3_0_unfold : clear implicits.
Arguments paco6_3_1_unfold : clear implicits.
Arguments paco6_3_2_unfold : clear implicits.

Global Instance paco6_3_0_inst  (gf_0 gf_1 gf_2 : rel6 T0 T1 T2 T3 T4 T5->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 : paco_class (paco6_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4 x5) :=
{ pacoacc    := paco6_3_0_acc gf_0 gf_1 gf_2;
  pacomult   := paco6_3_0_mult gf_0 gf_1 gf_2;
  pacofold   := paco6_3_0_fold gf_0 gf_1 gf_2;
  pacounfold := paco6_3_0_unfold gf_0 gf_1 gf_2 }.

Global Instance paco6_3_1_inst  (gf_0 gf_1 gf_2 : rel6 T0 T1 T2 T3 T4 T5->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 : paco_class (paco6_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4 x5) :=
{ pacoacc    := paco6_3_1_acc gf_0 gf_1 gf_2;
  pacomult   := paco6_3_1_mult gf_0 gf_1 gf_2;
  pacofold   := paco6_3_1_fold gf_0 gf_1 gf_2;
  pacounfold := paco6_3_1_unfold gf_0 gf_1 gf_2 }.

Global Instance paco6_3_2_inst  (gf_0 gf_1 gf_2 : rel6 T0 T1 T2 T3 T4 T5->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 : paco_class (paco6_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4 x5) :=
{ pacoacc    := paco6_3_2_acc gf_0 gf_1 gf_2;
  pacomult   := paco6_3_2_mult gf_0 gf_1 gf_2;
  pacofold   := paco6_3_2_fold gf_0 gf_1 gf_2;
  pacounfold := paco6_3_2_unfold gf_0 gf_1 gf_2 }.

End PACO6.

Global Opaque paco6.

Hint Unfold upaco6.
Hint Resolve paco6_fold.
Hint Unfold monotone6.

Global Opaque paco6_2_0.
Global Opaque paco6_2_1.

Hint Unfold upaco6_2_0.
Hint Unfold upaco6_2_1.
Hint Resolve paco6_2_0_fold.
Hint Resolve paco6_2_1_fold.
Hint Unfold monotone6_2.

Global Opaque paco6_3_0.
Global Opaque paco6_3_1.
Global Opaque paco6_3_2.

Hint Unfold upaco6_3_0.
Hint Unfold upaco6_3_1.
Hint Unfold upaco6_3_2.
Hint Resolve paco6_3_0_fold.
Hint Resolve paco6_3_1_fold.
Hint Resolve paco6_3_2_fold.
Hint Unfold monotone6_3.

