Require Export paconotation pacotacuser.
Require Import paconotation_internal pacotac pacon.
Set Implicit Arguments.

Section PACO12.

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

Record sig12T :=
  exist12T { 
      proj12T0: @T0;
      proj12T1: @T1 proj12T0;
      proj12T2: @T2 proj12T0 proj12T1;
      proj12T3: @T3 proj12T0 proj12T1 proj12T2;
      proj12T4: @T4 proj12T0 proj12T1 proj12T2 proj12T3;
      proj12T5: @T5 proj12T0 proj12T1 proj12T2 proj12T3 proj12T4;
      proj12T6: @T6 proj12T0 proj12T1 proj12T2 proj12T3 proj12T4 proj12T5;
      proj12T7: @T7 proj12T0 proj12T1 proj12T2 proj12T3 proj12T4 proj12T5 proj12T6;
      proj12T8: @T8 proj12T0 proj12T1 proj12T2 proj12T3 proj12T4 proj12T5 proj12T6 proj12T7;
      proj12T9: @T9 proj12T0 proj12T1 proj12T2 proj12T3 proj12T4 proj12T5 proj12T6 proj12T7 proj12T8;
      proj12T10: @T10 proj12T0 proj12T1 proj12T2 proj12T3 proj12T4 proj12T5 proj12T6 proj12T7 proj12T8 proj12T9;
      proj12T11: @T11 proj12T0 proj12T1 proj12T2 proj12T3 proj12T4 proj12T5 proj12T6 proj12T7 proj12T8 proj12T9 proj12T10;
    }.

Definition uncurry12 (R: rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11): rel1 sig12T := fun x => R (proj12T0 x) (proj12T1 x) (proj12T2 x) (proj12T3 x) (proj12T4 x) (proj12T5 x) (proj12T6 x) (proj12T7 x) (proj12T8 x) (proj12T9 x) (proj12T10 x) (proj12T11 x).

Definition curry12 (R: rel1 sig12T): rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 :=
  fun x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 => R (exist12T x11).

Lemma uncurry_map12 r0 r1 (LE : r0 <12== r1) : uncurry12 r0 <1== uncurry12 r1.
Proof. intros [] H. apply LE. auto. Qed.

Lemma uncurry_map_rev12 r0 r1 (LE: uncurry12 r0 <1== uncurry12 r1) : r0 <12== r1.
Proof.
  repeat_intros 12. intros H. apply (LE (exist12T x11) H).
Qed.

Lemma curry_map12 r0 r1 (LE: r0 <1== r1) : curry12 r0 <12== curry12 r1.
Proof. 
  repeat_intros 12. intros H. apply (LE (exist12T x11) H).
Qed.

Lemma curry_map_rev12 r0 r1 (LE: curry12 r0 <12== curry12 r1) : r0 <1== r1.
Proof. 
  intros [] H. apply LE. apply H.
Qed.

Lemma uncurry_bij1_12 r : curry12 (uncurry12 r) <12== r.
Proof. unfold le12. repeat_intros 12; auto. Qed.

Lemma uncurry_bij2_12 r : r <12== curry12 (uncurry12 r).
Proof. unfold le12. repeat_intros 12; auto. Qed.

Lemma curry_bij1_12 r : uncurry12 (curry12 r) <1== r.
Proof. intros []; auto. Qed.

Lemma curry_bij2_12 r : r <1== uncurry12 (curry12 r).
Proof. intros []; auto. Qed.

Lemma uncurry_adjoint1_12 r0 r1 (LE: uncurry12 r0 <1== r1) : r0 <12== curry12 r1.
Proof.
  apply uncurry_map_rev12. eapply le1_trans; [eauto|]. apply curry_bij2_12.
Qed.

Lemma uncurry_adjoint2_12 r0 r1 (LE: r0 <12== curry12 r1) : uncurry12 r0 <1== r1.
Proof.
  apply curry_map_rev12. eapply le12_trans; [|eauto]. apply uncurry_bij2_12.
Qed.

Lemma curry_adjoint1_12 r0 r1 (LE: curry12 r0 <12== r1) : r0 <1== uncurry12 r1.
Proof.
  apply curry_map_rev12. eapply le12_trans; [eauto|]. apply uncurry_bij2_12.
Qed.

Lemma curry_adjoint2_12 r0 r1 (LE: r0 <1== uncurry12 r1) : curry12 r0 <12== r1.
Proof.
  apply uncurry_map_rev12. eapply le1_trans; [|eauto]. apply curry_bij1_12.
Qed.

(** ** Predicates of Arity 12
*)

Section Arg12_def.
Variable gf : rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11.
Arguments gf : clear implicits.

Definition paco12( r: rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11) : rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 :=
  curry12 (paco (fun R0 => uncurry12 (gf (curry12 R0))) (uncurry12 r)).

Definition upaco12( r: rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11) := paco12 r \12/ r.
End Arg12_def.
Arguments paco12 : clear implicits.
Arguments upaco12 : clear implicits.
Hint Unfold upaco12.

Section Arg12_2_def.
Variable gf_0 gf_1 : rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.

Definition paco12_2_0( r_0 r_1: rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11) : rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 :=
  curry12 (paco_2_0 (fun R0 R1 => uncurry12 (gf_0 (curry12 R0) (curry12 R1))) (fun R0 R1 => uncurry12 (gf_1 (curry12 R0) (curry12 R1))) (uncurry12 r_0) (uncurry12 r_1)).

Definition paco12_2_1( r_0 r_1: rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11) : rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 :=
  curry12 (paco_2_1 (fun R0 R1 => uncurry12 (gf_0 (curry12 R0) (curry12 R1))) (fun R0 R1 => uncurry12 (gf_1 (curry12 R0) (curry12 R1))) (uncurry12 r_0) (uncurry12 r_1)).

Definition upaco12_2_0( r_0 r_1: rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11) := paco12_2_0 r_0 r_1 \12/ r_0.
Definition upaco12_2_1( r_0 r_1: rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11) := paco12_2_1 r_0 r_1 \12/ r_1.
End Arg12_2_def.
Arguments paco12_2_0 : clear implicits.
Arguments upaco12_2_0 : clear implicits.
Hint Unfold upaco12_2_0.
Arguments paco12_2_1 : clear implicits.
Arguments upaco12_2_1 : clear implicits.
Hint Unfold upaco12_2_1.

Section Arg12_3_def.
Variable gf_0 gf_1 gf_2 : rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.
Arguments gf_2 : clear implicits.

Definition paco12_3_0( r_0 r_1 r_2: rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11) : rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 :=
  curry12 (paco_3_0 (fun R0 R1 R2 => uncurry12 (gf_0 (curry12 R0) (curry12 R1) (curry12 R2))) (fun R0 R1 R2 => uncurry12 (gf_1 (curry12 R0) (curry12 R1) (curry12 R2))) (fun R0 R1 R2 => uncurry12 (gf_2 (curry12 R0) (curry12 R1) (curry12 R2))) (uncurry12 r_0) (uncurry12 r_1) (uncurry12 r_2)).

Definition paco12_3_1( r_0 r_1 r_2: rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11) : rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 :=
  curry12 (paco_3_1 (fun R0 R1 R2 => uncurry12 (gf_0 (curry12 R0) (curry12 R1) (curry12 R2))) (fun R0 R1 R2 => uncurry12 (gf_1 (curry12 R0) (curry12 R1) (curry12 R2))) (fun R0 R1 R2 => uncurry12 (gf_2 (curry12 R0) (curry12 R1) (curry12 R2))) (uncurry12 r_0) (uncurry12 r_1) (uncurry12 r_2)).

Definition paco12_3_2( r_0 r_1 r_2: rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11) : rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 :=
  curry12 (paco_3_2 (fun R0 R1 R2 => uncurry12 (gf_0 (curry12 R0) (curry12 R1) (curry12 R2))) (fun R0 R1 R2 => uncurry12 (gf_1 (curry12 R0) (curry12 R1) (curry12 R2))) (fun R0 R1 R2 => uncurry12 (gf_2 (curry12 R0) (curry12 R1) (curry12 R2))) (uncurry12 r_0) (uncurry12 r_1) (uncurry12 r_2)).

Definition upaco12_3_0( r_0 r_1 r_2: rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11) := paco12_3_0 r_0 r_1 r_2 \12/ r_0.
Definition upaco12_3_1( r_0 r_1 r_2: rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11) := paco12_3_1 r_0 r_1 r_2 \12/ r_1.
Definition upaco12_3_2( r_0 r_1 r_2: rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11) := paco12_3_2 r_0 r_1 r_2 \12/ r_2.
End Arg12_3_def.
Arguments paco12_3_0 : clear implicits.
Arguments upaco12_3_0 : clear implicits.
Hint Unfold upaco12_3_0.
Arguments paco12_3_1 : clear implicits.
Arguments upaco12_3_1 : clear implicits.
Hint Unfold upaco12_3_1.
Arguments paco12_3_2 : clear implicits.
Arguments upaco12_3_2 : clear implicits.
Hint Unfold upaco12_3_2.

(** 1 Mutual Coinduction *)

Section Arg12_1.

Definition monotone12 (gf: rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11) :=
  forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 r r' (IN: gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) (LE: r <12= r'), gf r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11.

Definition _monotone12 (gf: rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11) :=
  forall r r'(LE: r <12= r'), gf r <12== gf r'.

Lemma monotone12_eq (gf: rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11) :
  monotone12 gf <-> _monotone12 gf.
Proof. unfold monotone12, _monotone12, le12. split; eauto. Qed.

Lemma monotone12_map (gf: rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11)
      (MON: _monotone12 gf) :
  _monotone (fun R0 => uncurry12 (gf (curry12 R0))).
Proof.
  repeat_intros 3. apply uncurry_map12. apply MON; apply curry_map12; auto.
Qed.

Variable gf : rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11.
Arguments gf : clear implicits.

Theorem _paco12_mon: _monotone12 (paco12 gf).
Proof.
  repeat_intros 3. eapply curry_map12, _paco_mon; apply uncurry_map12; auto.
Qed.

Theorem _paco12_acc: forall
  l r (OBG: forall rr (INC: r <12== rr) (CIH: l <12== rr), l <12== paco12 gf rr),
  l <12== paco12 gf r.
Proof.
  intros. apply uncurry_adjoint1_12.
  eapply _paco_acc. intros.
  apply uncurry_adjoint1_12 in INC. apply uncurry_adjoint1_12 in CIH.
  apply uncurry_adjoint2_12.
  eapply le12_trans. eapply (OBG _ INC CIH).
  apply curry_map12.
  apply _paco_mon; try apply le1_refl; apply curry_bij1_12.
Qed.

Theorem _paco12_mult_strong: forall r,
  paco12 gf (upaco12 gf r) <12== paco12 gf r.
Proof.
  intros. apply curry_map12.
  eapply le1_trans; [| eapply _paco_mult_strong].
  apply _paco_mon; intros []; eauto.
Qed.

Theorem _paco12_fold: forall r,
  gf (upaco12 gf r) <12== paco12 gf r.
Proof.
  intros. apply uncurry_adjoint1_12.
  eapply le1_trans; [| apply _paco_fold]. apply le1_refl.
Qed.

Theorem _paco12_unfold: forall (MON: _monotone12 gf) r,
  paco12 gf r <12== gf (upaco12 gf r).
Proof.
  intros. apply curry_adjoint2_12.
  eapply _paco_unfold; apply monotone12_map; auto.
Qed.

Theorem paco12_acc: forall
  l r (OBG: forall rr (INC: r <12= rr) (CIH: l <12= rr), l <12= paco12 gf rr),
  l <12= paco12 gf r.
Proof.
  apply _paco12_acc.
Qed.

Theorem paco12_mon: monotone12 (paco12 gf).
Proof.
  apply monotone12_eq.
  apply _paco12_mon.
Qed.

Theorem paco12_mult_strong: forall r,
  paco12 gf (upaco12 gf r) <12= paco12 gf r.
Proof.
  apply _paco12_mult_strong.
Qed.

Corollary paco12_mult: forall r,
  paco12 gf (paco12 gf r) <12= paco12 gf r.
Proof. intros; eapply paco12_mult_strong, paco12_mon; eauto. Qed.

Theorem paco12_fold: forall r,
  gf (upaco12 gf r) <12= paco12 gf r.
Proof.
  apply _paco12_fold.
Qed.

Theorem paco12_unfold: forall (MON: monotone12 gf) r,
  paco12 gf r <12= gf (upaco12 gf r).
Proof.
  repeat_intros 1. eapply _paco12_unfold; apply monotone12_eq; auto.
Qed.

End Arg12_1.

Arguments paco12_acc : clear implicits.
Arguments paco12_mon : clear implicits.
Arguments paco12_mult_strong : clear implicits.
Arguments paco12_mult : clear implicits.
Arguments paco12_fold : clear implicits.
Arguments paco12_unfold : clear implicits.

Global Instance paco12_inst  (gf : rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11->_) r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : paco_class (paco12 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) :=
{ pacoacc    := paco12_acc gf;
  pacomult   := paco12_mult gf;
  pacofold   := paco12_fold gf;
  pacounfold := paco12_unfold gf }.

(** 2 Mutual Coinduction *)

Section Arg12_2.

Definition monotone12_2 (gf: rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11) :=
  forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 r_0 r_1 r'_0 r'_1 (IN: gf r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) (LE_0: r_0 <12= r'_0)(LE_1: r_1 <12= r'_1), gf r'_0 r'_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11.

Definition _monotone12_2 (gf: rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11) :=
  forall r_0 r_1 r'_0 r'_1(LE_0: r_0 <12= r'_0)(LE_1: r_1 <12= r'_1), gf r_0 r_1 <12== gf r'_0 r'_1.

Lemma monotone12_2_eq (gf: rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11) :
  monotone12_2 gf <-> _monotone12_2 gf.
Proof. unfold monotone12_2, _monotone12_2, le12. split; eauto. Qed.

Lemma monotone12_2_map (gf: rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11)
      (MON: _monotone12_2 gf) :
  _monotone_2 (fun R0 R1 => uncurry12 (gf (curry12 R0) (curry12 R1))).
Proof.
  repeat_intros 6. apply uncurry_map12. apply MON; apply curry_map12; auto.
Qed.

Variable gf_0 gf_1 : rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.

Theorem _paco12_2_0_mon: _monotone12_2 (paco12_2_0 gf_0 gf_1).
Proof.
  repeat_intros 6. eapply curry_map12, _paco_2_0_mon; apply uncurry_map12; auto.
Qed.

Theorem _paco12_2_1_mon: _monotone12_2 (paco12_2_1 gf_0 gf_1).
Proof.
  repeat_intros 6. eapply curry_map12, _paco_2_1_mon; apply uncurry_map12; auto.
Qed.

Theorem _paco12_2_0_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_0 <12== rr) (CIH: l <12== rr), l <12== paco12_2_0 gf_0 gf_1 rr r_1),
  l <12== paco12_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_12.
  eapply _paco_2_0_acc. intros.
  apply uncurry_adjoint1_12 in INC. apply uncurry_adjoint1_12 in CIH.
  apply uncurry_adjoint2_12.
  eapply le12_trans. eapply (OBG _ INC CIH).
  apply curry_map12.
  apply _paco_2_0_mon; try apply le1_refl; apply curry_bij1_12.
Qed.

Theorem _paco12_2_1_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_1 <12== rr) (CIH: l <12== rr), l <12== paco12_2_1 gf_0 gf_1 r_0 rr),
  l <12== paco12_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_12.
  eapply _paco_2_1_acc. intros.
  apply uncurry_adjoint1_12 in INC. apply uncurry_adjoint1_12 in CIH.
  apply uncurry_adjoint2_12.
  eapply le12_trans. eapply (OBG _ INC CIH).
  apply curry_map12.
  apply _paco_2_1_mon; try apply le1_refl; apply curry_bij1_12.
Qed.

Theorem _paco12_2_0_mult_strong: forall r_0 r_1,
  paco12_2_0 gf_0 gf_1 (upaco12_2_0 gf_0 gf_1 r_0 r_1) (upaco12_2_1 gf_0 gf_1 r_0 r_1) <12== paco12_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply curry_map12.
  eapply le1_trans; [| eapply _paco_2_0_mult_strong].
  apply _paco_2_0_mon; intros []; eauto.
Qed.

Theorem _paco12_2_1_mult_strong: forall r_0 r_1,
  paco12_2_1 gf_0 gf_1 (upaco12_2_0 gf_0 gf_1 r_0 r_1) (upaco12_2_1 gf_0 gf_1 r_0 r_1) <12== paco12_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply curry_map12.
  eapply le1_trans; [| eapply _paco_2_1_mult_strong].
  apply _paco_2_1_mon; intros []; eauto.
Qed.

Theorem _paco12_2_0_fold: forall r_0 r_1,
  gf_0 (upaco12_2_0 gf_0 gf_1 r_0 r_1) (upaco12_2_1 gf_0 gf_1 r_0 r_1) <12== paco12_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_12.
  eapply le1_trans; [| apply _paco_2_0_fold]. apply le1_refl.
Qed.

Theorem _paco12_2_1_fold: forall r_0 r_1,
  gf_1 (upaco12_2_0 gf_0 gf_1 r_0 r_1) (upaco12_2_1 gf_0 gf_1 r_0 r_1) <12== paco12_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_12.
  eapply le1_trans; [| apply _paco_2_1_fold]. apply le1_refl.
Qed.

Theorem _paco12_2_0_unfold: forall (MON: _monotone12_2 gf_0) (MON: _monotone12_2 gf_1) r_0 r_1,
  paco12_2_0 gf_0 gf_1 r_0 r_1 <12== gf_0 (upaco12_2_0 gf_0 gf_1 r_0 r_1) (upaco12_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  intros. apply curry_adjoint2_12.
  eapply _paco_2_0_unfold; apply monotone12_2_map; auto.
Qed.

Theorem _paco12_2_1_unfold: forall (MON: _monotone12_2 gf_0) (MON: _monotone12_2 gf_1) r_0 r_1,
  paco12_2_1 gf_0 gf_1 r_0 r_1 <12== gf_1 (upaco12_2_0 gf_0 gf_1 r_0 r_1) (upaco12_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  intros. apply curry_adjoint2_12.
  eapply _paco_2_1_unfold; apply monotone12_2_map; auto.
Qed.

Theorem paco12_2_0_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_0 <12= rr) (CIH: l <12= rr), l <12= paco12_2_0 gf_0 gf_1 rr r_1),
  l <12= paco12_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco12_2_0_acc.
Qed.

Theorem paco12_2_1_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_1 <12= rr) (CIH: l <12= rr), l <12= paco12_2_1 gf_0 gf_1 r_0 rr),
  l <12= paco12_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco12_2_1_acc.
Qed.

Theorem paco12_2_0_mon: monotone12_2 (paco12_2_0 gf_0 gf_1).
Proof.
  apply monotone12_2_eq.
  apply _paco12_2_0_mon.
Qed.

Theorem paco12_2_1_mon: monotone12_2 (paco12_2_1 gf_0 gf_1).
Proof.
  apply monotone12_2_eq.
  apply _paco12_2_1_mon.
Qed.

Theorem paco12_2_0_mult_strong: forall r_0 r_1,
  paco12_2_0 gf_0 gf_1 (upaco12_2_0 gf_0 gf_1 r_0 r_1) (upaco12_2_1 gf_0 gf_1 r_0 r_1) <12= paco12_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco12_2_0_mult_strong.
Qed.

Theorem paco12_2_1_mult_strong: forall r_0 r_1,
  paco12_2_1 gf_0 gf_1 (upaco12_2_0 gf_0 gf_1 r_0 r_1) (upaco12_2_1 gf_0 gf_1 r_0 r_1) <12= paco12_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco12_2_1_mult_strong.
Qed.

Corollary paco12_2_0_mult: forall r_0 r_1,
  paco12_2_0 gf_0 gf_1 (paco12_2_0 gf_0 gf_1 r_0 r_1) (paco12_2_1 gf_0 gf_1 r_0 r_1) <12= paco12_2_0 gf_0 gf_1 r_0 r_1.
Proof. intros; eapply paco12_2_0_mult_strong, paco12_2_0_mon; eauto. Qed.

Corollary paco12_2_1_mult: forall r_0 r_1,
  paco12_2_1 gf_0 gf_1 (paco12_2_0 gf_0 gf_1 r_0 r_1) (paco12_2_1 gf_0 gf_1 r_0 r_1) <12= paco12_2_1 gf_0 gf_1 r_0 r_1.
Proof. intros; eapply paco12_2_1_mult_strong, paco12_2_1_mon; eauto. Qed.

Theorem paco12_2_0_fold: forall r_0 r_1,
  gf_0 (upaco12_2_0 gf_0 gf_1 r_0 r_1) (upaco12_2_1 gf_0 gf_1 r_0 r_1) <12= paco12_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco12_2_0_fold.
Qed.

Theorem paco12_2_1_fold: forall r_0 r_1,
  gf_1 (upaco12_2_0 gf_0 gf_1 r_0 r_1) (upaco12_2_1 gf_0 gf_1 r_0 r_1) <12= paco12_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco12_2_1_fold.
Qed.

Theorem paco12_2_0_unfold: forall (MON: monotone12_2 gf_0) (MON: monotone12_2 gf_1) r_0 r_1,
  paco12_2_0 gf_0 gf_1 r_0 r_1 <12= gf_0 (upaco12_2_0 gf_0 gf_1 r_0 r_1) (upaco12_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  repeat_intros 2. eapply _paco12_2_0_unfold; apply monotone12_2_eq; auto.
Qed.

Theorem paco12_2_1_unfold: forall (MON: monotone12_2 gf_0) (MON: monotone12_2 gf_1) r_0 r_1,
  paco12_2_1 gf_0 gf_1 r_0 r_1 <12= gf_1 (upaco12_2_0 gf_0 gf_1 r_0 r_1) (upaco12_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  repeat_intros 2. eapply _paco12_2_1_unfold; apply monotone12_2_eq; auto.
Qed.

End Arg12_2.

Arguments paco12_2_0_acc : clear implicits.
Arguments paco12_2_1_acc : clear implicits.
Arguments paco12_2_0_mon : clear implicits.
Arguments paco12_2_1_mon : clear implicits.
Arguments paco12_2_0_mult_strong : clear implicits.
Arguments paco12_2_1_mult_strong : clear implicits.
Arguments paco12_2_0_mult : clear implicits.
Arguments paco12_2_1_mult : clear implicits.
Arguments paco12_2_0_fold : clear implicits.
Arguments paco12_2_1_fold : clear implicits.
Arguments paco12_2_0_unfold : clear implicits.
Arguments paco12_2_1_unfold : clear implicits.

Global Instance paco12_2_0_inst  (gf_0 gf_1 : rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11->_) r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : paco_class (paco12_2_0 gf_0 gf_1 r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) :=
{ pacoacc    := paco12_2_0_acc gf_0 gf_1;
  pacomult   := paco12_2_0_mult gf_0 gf_1;
  pacofold   := paco12_2_0_fold gf_0 gf_1;
  pacounfold := paco12_2_0_unfold gf_0 gf_1 }.

Global Instance paco12_2_1_inst  (gf_0 gf_1 : rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11->_) r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : paco_class (paco12_2_1 gf_0 gf_1 r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) :=
{ pacoacc    := paco12_2_1_acc gf_0 gf_1;
  pacomult   := paco12_2_1_mult gf_0 gf_1;
  pacofold   := paco12_2_1_fold gf_0 gf_1;
  pacounfold := paco12_2_1_unfold gf_0 gf_1 }.

(** 3 Mutual Coinduction *)

Section Arg12_3.

Definition monotone12_3 (gf: rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11) :=
  forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 r_0 r_1 r_2 r'_0 r'_1 r'_2 (IN: gf r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) (LE_0: r_0 <12= r'_0)(LE_1: r_1 <12= r'_1)(LE_2: r_2 <12= r'_2), gf r'_0 r'_1 r'_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11.

Definition _monotone12_3 (gf: rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11) :=
  forall r_0 r_1 r_2 r'_0 r'_1 r'_2(LE_0: r_0 <12= r'_0)(LE_1: r_1 <12= r'_1)(LE_2: r_2 <12= r'_2), gf r_0 r_1 r_2 <12== gf r'_0 r'_1 r'_2.

Lemma monotone12_3_eq (gf: rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11) :
  monotone12_3 gf <-> _monotone12_3 gf.
Proof. unfold monotone12_3, _monotone12_3, le12. split; eauto. Qed.

Lemma monotone12_3_map (gf: rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11)
      (MON: _monotone12_3 gf) :
  _monotone_3 (fun R0 R1 R2 => uncurry12 (gf (curry12 R0) (curry12 R1) (curry12 R2))).
Proof.
  repeat_intros 9. apply uncurry_map12. apply MON; apply curry_map12; auto.
Qed.

Variable gf_0 gf_1 gf_2 : rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.
Arguments gf_2 : clear implicits.

Theorem _paco12_3_0_mon: _monotone12_3 (paco12_3_0 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 9. eapply curry_map12, _paco_3_0_mon; apply uncurry_map12; auto.
Qed.

Theorem _paco12_3_1_mon: _monotone12_3 (paco12_3_1 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 9. eapply curry_map12, _paco_3_1_mon; apply uncurry_map12; auto.
Qed.

Theorem _paco12_3_2_mon: _monotone12_3 (paco12_3_2 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 9. eapply curry_map12, _paco_3_2_mon; apply uncurry_map12; auto.
Qed.

Theorem _paco12_3_0_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_0 <12== rr) (CIH: l <12== rr), l <12== paco12_3_0 gf_0 gf_1 gf_2 rr r_1 r_2),
  l <12== paco12_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_12.
  eapply _paco_3_0_acc. intros.
  apply uncurry_adjoint1_12 in INC. apply uncurry_adjoint1_12 in CIH.
  apply uncurry_adjoint2_12.
  eapply le12_trans. eapply (OBG _ INC CIH).
  apply curry_map12.
  apply _paco_3_0_mon; try apply le1_refl; apply curry_bij1_12.
Qed.

Theorem _paco12_3_1_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_1 <12== rr) (CIH: l <12== rr), l <12== paco12_3_1 gf_0 gf_1 gf_2 r_0 rr r_2),
  l <12== paco12_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_12.
  eapply _paco_3_1_acc. intros.
  apply uncurry_adjoint1_12 in INC. apply uncurry_adjoint1_12 in CIH.
  apply uncurry_adjoint2_12.
  eapply le12_trans. eapply (OBG _ INC CIH).
  apply curry_map12.
  apply _paco_3_1_mon; try apply le1_refl; apply curry_bij1_12.
Qed.

Theorem _paco12_3_2_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_2 <12== rr) (CIH: l <12== rr), l <12== paco12_3_2 gf_0 gf_1 gf_2 r_0 r_1 rr),
  l <12== paco12_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_12.
  eapply _paco_3_2_acc. intros.
  apply uncurry_adjoint1_12 in INC. apply uncurry_adjoint1_12 in CIH.
  apply uncurry_adjoint2_12.
  eapply le12_trans. eapply (OBG _ INC CIH).
  apply curry_map12.
  apply _paco_3_2_mon; try apply le1_refl; apply curry_bij1_12.
Qed.

Theorem _paco12_3_0_mult_strong: forall r_0 r_1 r_2,
  paco12_3_0 gf_0 gf_1 gf_2 (upaco12_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco12_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco12_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <12== paco12_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply curry_map12.
  eapply le1_trans; [| eapply _paco_3_0_mult_strong].
  apply _paco_3_0_mon; intros []; eauto.
Qed.

Theorem _paco12_3_1_mult_strong: forall r_0 r_1 r_2,
  paco12_3_1 gf_0 gf_1 gf_2 (upaco12_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco12_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco12_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <12== paco12_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply curry_map12.
  eapply le1_trans; [| eapply _paco_3_1_mult_strong].
  apply _paco_3_1_mon; intros []; eauto.
Qed.

Theorem _paco12_3_2_mult_strong: forall r_0 r_1 r_2,
  paco12_3_2 gf_0 gf_1 gf_2 (upaco12_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco12_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco12_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <12== paco12_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply curry_map12.
  eapply le1_trans; [| eapply _paco_3_2_mult_strong].
  apply _paco_3_2_mon; intros []; eauto.
Qed.

Theorem _paco12_3_0_fold: forall r_0 r_1 r_2,
  gf_0 (upaco12_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco12_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco12_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <12== paco12_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_12.
  eapply le1_trans; [| apply _paco_3_0_fold]. apply le1_refl.
Qed.

Theorem _paco12_3_1_fold: forall r_0 r_1 r_2,
  gf_1 (upaco12_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco12_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco12_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <12== paco12_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_12.
  eapply le1_trans; [| apply _paco_3_1_fold]. apply le1_refl.
Qed.

Theorem _paco12_3_2_fold: forall r_0 r_1 r_2,
  gf_2 (upaco12_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco12_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco12_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <12== paco12_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_12.
  eapply le1_trans; [| apply _paco_3_2_fold]. apply le1_refl.
Qed.

Theorem _paco12_3_0_unfold: forall (MON: _monotone12_3 gf_0) (MON: _monotone12_3 gf_1) (MON: _monotone12_3 gf_2) r_0 r_1 r_2,
  paco12_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 <12== gf_0 (upaco12_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco12_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco12_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  intros. apply curry_adjoint2_12.
  eapply _paco_3_0_unfold; apply monotone12_3_map; auto.
Qed.

Theorem _paco12_3_1_unfold: forall (MON: _monotone12_3 gf_0) (MON: _monotone12_3 gf_1) (MON: _monotone12_3 gf_2) r_0 r_1 r_2,
  paco12_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 <12== gf_1 (upaco12_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco12_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco12_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  intros. apply curry_adjoint2_12.
  eapply _paco_3_1_unfold; apply monotone12_3_map; auto.
Qed.

Theorem _paco12_3_2_unfold: forall (MON: _monotone12_3 gf_0) (MON: _monotone12_3 gf_1) (MON: _monotone12_3 gf_2) r_0 r_1 r_2,
  paco12_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 <12== gf_2 (upaco12_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco12_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco12_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  intros. apply curry_adjoint2_12.
  eapply _paco_3_2_unfold; apply monotone12_3_map; auto.
Qed.

Theorem paco12_3_0_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_0 <12= rr) (CIH: l <12= rr), l <12= paco12_3_0 gf_0 gf_1 gf_2 rr r_1 r_2),
  l <12= paco12_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco12_3_0_acc.
Qed.

Theorem paco12_3_1_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_1 <12= rr) (CIH: l <12= rr), l <12= paco12_3_1 gf_0 gf_1 gf_2 r_0 rr r_2),
  l <12= paco12_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco12_3_1_acc.
Qed.

Theorem paco12_3_2_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_2 <12= rr) (CIH: l <12= rr), l <12= paco12_3_2 gf_0 gf_1 gf_2 r_0 r_1 rr),
  l <12= paco12_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco12_3_2_acc.
Qed.

Theorem paco12_3_0_mon: monotone12_3 (paco12_3_0 gf_0 gf_1 gf_2).
Proof.
  apply monotone12_3_eq.
  apply _paco12_3_0_mon.
Qed.

Theorem paco12_3_1_mon: monotone12_3 (paco12_3_1 gf_0 gf_1 gf_2).
Proof.
  apply monotone12_3_eq.
  apply _paco12_3_1_mon.
Qed.

Theorem paco12_3_2_mon: monotone12_3 (paco12_3_2 gf_0 gf_1 gf_2).
Proof.
  apply monotone12_3_eq.
  apply _paco12_3_2_mon.
Qed.

Theorem paco12_3_0_mult_strong: forall r_0 r_1 r_2,
  paco12_3_0 gf_0 gf_1 gf_2 (upaco12_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco12_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco12_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <12= paco12_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco12_3_0_mult_strong.
Qed.

Theorem paco12_3_1_mult_strong: forall r_0 r_1 r_2,
  paco12_3_1 gf_0 gf_1 gf_2 (upaco12_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco12_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco12_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <12= paco12_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco12_3_1_mult_strong.
Qed.

Theorem paco12_3_2_mult_strong: forall r_0 r_1 r_2,
  paco12_3_2 gf_0 gf_1 gf_2 (upaco12_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco12_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco12_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <12= paco12_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco12_3_2_mult_strong.
Qed.

Corollary paco12_3_0_mult: forall r_0 r_1 r_2,
  paco12_3_0 gf_0 gf_1 gf_2 (paco12_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco12_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco12_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <12= paco12_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco12_3_0_mult_strong, paco12_3_0_mon; eauto. Qed.

Corollary paco12_3_1_mult: forall r_0 r_1 r_2,
  paco12_3_1 gf_0 gf_1 gf_2 (paco12_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco12_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco12_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <12= paco12_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco12_3_1_mult_strong, paco12_3_1_mon; eauto. Qed.

Corollary paco12_3_2_mult: forall r_0 r_1 r_2,
  paco12_3_2 gf_0 gf_1 gf_2 (paco12_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco12_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco12_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <12= paco12_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco12_3_2_mult_strong, paco12_3_2_mon; eauto. Qed.

Theorem paco12_3_0_fold: forall r_0 r_1 r_2,
  gf_0 (upaco12_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco12_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco12_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <12= paco12_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco12_3_0_fold.
Qed.

Theorem paco12_3_1_fold: forall r_0 r_1 r_2,
  gf_1 (upaco12_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco12_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco12_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <12= paco12_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco12_3_1_fold.
Qed.

Theorem paco12_3_2_fold: forall r_0 r_1 r_2,
  gf_2 (upaco12_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco12_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco12_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <12= paco12_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco12_3_2_fold.
Qed.

Theorem paco12_3_0_unfold: forall (MON: monotone12_3 gf_0) (MON: monotone12_3 gf_1) (MON: monotone12_3 gf_2) r_0 r_1 r_2,
  paco12_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 <12= gf_0 (upaco12_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco12_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco12_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  repeat_intros 3. eapply _paco12_3_0_unfold; apply monotone12_3_eq; auto.
Qed.

Theorem paco12_3_1_unfold: forall (MON: monotone12_3 gf_0) (MON: monotone12_3 gf_1) (MON: monotone12_3 gf_2) r_0 r_1 r_2,
  paco12_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 <12= gf_1 (upaco12_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco12_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco12_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  repeat_intros 3. eapply _paco12_3_1_unfold; apply monotone12_3_eq; auto.
Qed.

Theorem paco12_3_2_unfold: forall (MON: monotone12_3 gf_0) (MON: monotone12_3 gf_1) (MON: monotone12_3 gf_2) r_0 r_1 r_2,
  paco12_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 <12= gf_2 (upaco12_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco12_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco12_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  repeat_intros 3. eapply _paco12_3_2_unfold; apply monotone12_3_eq; auto.
Qed.

End Arg12_3.

Arguments paco12_3_0_acc : clear implicits.
Arguments paco12_3_1_acc : clear implicits.
Arguments paco12_3_2_acc : clear implicits.
Arguments paco12_3_0_mon : clear implicits.
Arguments paco12_3_1_mon : clear implicits.
Arguments paco12_3_2_mon : clear implicits.
Arguments paco12_3_0_mult_strong : clear implicits.
Arguments paco12_3_1_mult_strong : clear implicits.
Arguments paco12_3_2_mult_strong : clear implicits.
Arguments paco12_3_0_mult : clear implicits.
Arguments paco12_3_1_mult : clear implicits.
Arguments paco12_3_2_mult : clear implicits.
Arguments paco12_3_0_fold : clear implicits.
Arguments paco12_3_1_fold : clear implicits.
Arguments paco12_3_2_fold : clear implicits.
Arguments paco12_3_0_unfold : clear implicits.
Arguments paco12_3_1_unfold : clear implicits.
Arguments paco12_3_2_unfold : clear implicits.

Global Instance paco12_3_0_inst  (gf_0 gf_1 gf_2 : rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : paco_class (paco12_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) :=
{ pacoacc    := paco12_3_0_acc gf_0 gf_1 gf_2;
  pacomult   := paco12_3_0_mult gf_0 gf_1 gf_2;
  pacofold   := paco12_3_0_fold gf_0 gf_1 gf_2;
  pacounfold := paco12_3_0_unfold gf_0 gf_1 gf_2 }.

Global Instance paco12_3_1_inst  (gf_0 gf_1 gf_2 : rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : paco_class (paco12_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) :=
{ pacoacc    := paco12_3_1_acc gf_0 gf_1 gf_2;
  pacomult   := paco12_3_1_mult gf_0 gf_1 gf_2;
  pacofold   := paco12_3_1_fold gf_0 gf_1 gf_2;
  pacounfold := paco12_3_1_unfold gf_0 gf_1 gf_2 }.

Global Instance paco12_3_2_inst  (gf_0 gf_1 gf_2 : rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : paco_class (paco12_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) :=
{ pacoacc    := paco12_3_2_acc gf_0 gf_1 gf_2;
  pacomult   := paco12_3_2_mult gf_0 gf_1 gf_2;
  pacofold   := paco12_3_2_fold gf_0 gf_1 gf_2;
  pacounfold := paco12_3_2_unfold gf_0 gf_1 gf_2 }.

End PACO12.

Global Opaque paco12.

Hint Unfold upaco12.
Hint Resolve paco12_fold.
Hint Unfold monotone12.

Global Opaque paco12_2_0.
Global Opaque paco12_2_1.

Hint Unfold upaco12_2_0.
Hint Unfold upaco12_2_1.
Hint Resolve paco12_2_0_fold.
Hint Resolve paco12_2_1_fold.
Hint Unfold monotone12_2.

Global Opaque paco12_3_0.
Global Opaque paco12_3_1.
Global Opaque paco12_3_2.

Hint Unfold upaco12_3_0.
Hint Unfold upaco12_3_1.
Hint Unfold upaco12_3_2.
Hint Resolve paco12_3_0_fold.
Hint Resolve paco12_3_1_fold.
Hint Resolve paco12_3_2_fold.
Hint Unfold monotone12_3.

