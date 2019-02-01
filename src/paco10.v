Require Export paconotation pacotacuser.
Require Import paconotation_internal pacotac pacon.
Set Implicit Arguments.

Section PACO10.

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

Record sig10T :=
  exist10T { 
      proj10T0: @T0;
      proj10T1: @T1 proj10T0;
      proj10T2: @T2 proj10T0 proj10T1;
      proj10T3: @T3 proj10T0 proj10T1 proj10T2;
      proj10T4: @T4 proj10T0 proj10T1 proj10T2 proj10T3;
      proj10T5: @T5 proj10T0 proj10T1 proj10T2 proj10T3 proj10T4;
      proj10T6: @T6 proj10T0 proj10T1 proj10T2 proj10T3 proj10T4 proj10T5;
      proj10T7: @T7 proj10T0 proj10T1 proj10T2 proj10T3 proj10T4 proj10T5 proj10T6;
      proj10T8: @T8 proj10T0 proj10T1 proj10T2 proj10T3 proj10T4 proj10T5 proj10T6 proj10T7;
      proj10T9: @T9 proj10T0 proj10T1 proj10T2 proj10T3 proj10T4 proj10T5 proj10T6 proj10T7 proj10T8;
    }.

Definition uncurry10 (R: rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9): rel1 sig10T := fun x => R (proj10T0 x) (proj10T1 x) (proj10T2 x) (proj10T3 x) (proj10T4 x) (proj10T5 x) (proj10T6 x) (proj10T7 x) (proj10T8 x) (proj10T9 x).

Definition curry10 (R: rel1 sig10T): rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 :=
  fun x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 => R (exist10T x9).

Lemma uncurry_map10 r0 r1 (LE : r0 <10== r1) : uncurry10 r0 <1== uncurry10 r1.
Proof. intros [] H. apply LE. apply H. Qed.

Lemma uncurry_map_rev10 r0 r1 (LE: uncurry10 r0 <1== uncurry10 r1) : r0 <10== r1.
Proof.
  repeat_intros 10. intros H. apply (LE (exist10T x9) H).
Qed.

Lemma curry_map10 r0 r1 (LE: r0 <1== r1) : curry10 r0 <10== curry10 r1.
Proof. 
  repeat_intros 10. intros H. apply (LE (exist10T x9) H).
Qed.

Lemma curry_map_rev10 r0 r1 (LE: curry10 r0 <10== curry10 r1) : r0 <1== r1.
Proof. 
  intros [] H. apply LE. apply H.
Qed.

Lemma uncurry_bij1_10 r : curry10 (uncurry10 r) <10== r.
Proof. unfold le10. repeat_intros 10. intros H. apply H. Qed.

Lemma uncurry_bij2_10 r : r <10== curry10 (uncurry10 r).
Proof. unfold le10. repeat_intros 10. intros H. apply H. Qed.

Lemma curry_bij1_10 r : uncurry10 (curry10 r) <1== r.
Proof. intros []. intro H. apply H. Qed.

Lemma curry_bij2_10 r : r <1== uncurry10 (curry10 r).
Proof. intros []. intro H. apply H. Qed.

Lemma uncurry_adjoint1_10 r0 r1 (LE: uncurry10 r0 <1== r1) : r0 <10== curry10 r1.
Proof.
  apply uncurry_map_rev10. eapply le1_trans; [apply LE|]. apply curry_bij2_10.
Qed.

Lemma uncurry_adjoint2_10 r0 r1 (LE: r0 <10== curry10 r1) : uncurry10 r0 <1== r1.
Proof.
  apply curry_map_rev10. eapply le10_trans; [|apply LE]. apply uncurry_bij2_10.
Qed.

Lemma curry_adjoint1_10 r0 r1 (LE: curry10 r0 <10== r1) : r0 <1== uncurry10 r1.
Proof.
  apply curry_map_rev10. eapply le10_trans; [apply LE|]. apply uncurry_bij2_10.
Qed.

Lemma curry_adjoint2_10 r0 r1 (LE: r0 <1== uncurry10 r1) : curry10 r0 <10== r1.
Proof.
  apply uncurry_map_rev10. eapply le1_trans; [|apply LE]. apply curry_bij1_10.
Qed.

(** ** Predicates of Arity 10
*)

Section Arg10_def.
Variable gf : rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9.
Arguments gf : clear implicits.

Definition paco10( r: rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) : rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 :=
  curry10 (paco (fun R0 => uncurry10 (gf (curry10 R0))) (uncurry10 r)).

Definition upaco10( r: rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) := paco10 r \10/ r.
End Arg10_def.
Arguments paco10 : clear implicits.
Arguments upaco10 : clear implicits.
Hint Unfold upaco10.

Section Arg10_2_def.
Variable gf_0 gf_1 : rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.

Definition paco10_2_0( r_0 r_1: rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) : rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 :=
  curry10 (paco_2_0 (fun R0 R1 => uncurry10 (gf_0 (curry10 R0) (curry10 R1))) (fun R0 R1 => uncurry10 (gf_1 (curry10 R0) (curry10 R1))) (uncurry10 r_0) (uncurry10 r_1)).

Definition paco10_2_1( r_0 r_1: rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) : rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 :=
  curry10 (paco_2_1 (fun R0 R1 => uncurry10 (gf_0 (curry10 R0) (curry10 R1))) (fun R0 R1 => uncurry10 (gf_1 (curry10 R0) (curry10 R1))) (uncurry10 r_0) (uncurry10 r_1)).

Definition upaco10_2_0( r_0 r_1: rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) := paco10_2_0 r_0 r_1 \10/ r_0.
Definition upaco10_2_1( r_0 r_1: rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) := paco10_2_1 r_0 r_1 \10/ r_1.
End Arg10_2_def.
Arguments paco10_2_0 : clear implicits.
Arguments upaco10_2_0 : clear implicits.
Hint Unfold upaco10_2_0.
Arguments paco10_2_1 : clear implicits.
Arguments upaco10_2_1 : clear implicits.
Hint Unfold upaco10_2_1.

Section Arg10_3_def.
Variable gf_0 gf_1 gf_2 : rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.
Arguments gf_2 : clear implicits.

Definition paco10_3_0( r_0 r_1 r_2: rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) : rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 :=
  curry10 (paco_3_0 (fun R0 R1 R2 => uncurry10 (gf_0 (curry10 R0) (curry10 R1) (curry10 R2))) (fun R0 R1 R2 => uncurry10 (gf_1 (curry10 R0) (curry10 R1) (curry10 R2))) (fun R0 R1 R2 => uncurry10 (gf_2 (curry10 R0) (curry10 R1) (curry10 R2))) (uncurry10 r_0) (uncurry10 r_1) (uncurry10 r_2)).

Definition paco10_3_1( r_0 r_1 r_2: rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) : rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 :=
  curry10 (paco_3_1 (fun R0 R1 R2 => uncurry10 (gf_0 (curry10 R0) (curry10 R1) (curry10 R2))) (fun R0 R1 R2 => uncurry10 (gf_1 (curry10 R0) (curry10 R1) (curry10 R2))) (fun R0 R1 R2 => uncurry10 (gf_2 (curry10 R0) (curry10 R1) (curry10 R2))) (uncurry10 r_0) (uncurry10 r_1) (uncurry10 r_2)).

Definition paco10_3_2( r_0 r_1 r_2: rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) : rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 :=
  curry10 (paco_3_2 (fun R0 R1 R2 => uncurry10 (gf_0 (curry10 R0) (curry10 R1) (curry10 R2))) (fun R0 R1 R2 => uncurry10 (gf_1 (curry10 R0) (curry10 R1) (curry10 R2))) (fun R0 R1 R2 => uncurry10 (gf_2 (curry10 R0) (curry10 R1) (curry10 R2))) (uncurry10 r_0) (uncurry10 r_1) (uncurry10 r_2)).

Definition upaco10_3_0( r_0 r_1 r_2: rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) := paco10_3_0 r_0 r_1 r_2 \10/ r_0.
Definition upaco10_3_1( r_0 r_1 r_2: rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) := paco10_3_1 r_0 r_1 r_2 \10/ r_1.
Definition upaco10_3_2( r_0 r_1 r_2: rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) := paco10_3_2 r_0 r_1 r_2 \10/ r_2.
End Arg10_3_def.
Arguments paco10_3_0 : clear implicits.
Arguments upaco10_3_0 : clear implicits.
Hint Unfold upaco10_3_0.
Arguments paco10_3_1 : clear implicits.
Arguments upaco10_3_1 : clear implicits.
Hint Unfold upaco10_3_1.
Arguments paco10_3_2 : clear implicits.
Arguments upaco10_3_2 : clear implicits.
Hint Unfold upaco10_3_2.

(** 1 Mutual Coinduction *)

Section Arg10_1.

Definition monotone10 (gf: rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) :=
  forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 r r' (IN: gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (LE: r <10= r'), gf r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9.

Definition _monotone10 (gf: rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) :=
  forall r r'(LE: r <10= r'), gf r <10== gf r'.

Lemma monotone10_eq (gf: rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) :
  monotone10 gf <-> _monotone10 gf.
Proof. unfold monotone10, _monotone10, le10. split; intros; eapply H; eassumption. Qed.

Lemma monotone10_map (gf: rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9)
      (MON: _monotone10 gf) :
  _monotone (fun R0 => uncurry10 (gf (curry10 R0))).
Proof.
  repeat_intros 3. apply uncurry_map10. apply MON; apply curry_map10; assumption.
Qed.

Variable gf : rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9.
Arguments gf : clear implicits.

Theorem _paco10_mon: _monotone10 (paco10 gf).
Proof.
  repeat_intros 3. eapply curry_map10, _paco_mon; apply uncurry_map10; assumption.
Qed.

Theorem _paco10_acc: forall
  l r (OBG: forall rr (INC: r <10== rr) (CIH: l <10== rr), l <10== paco10 gf rr),
  l <10== paco10 gf r.
Proof.
  intros. apply uncurry_adjoint1_10.
  eapply _paco_acc. intros.
  apply uncurry_adjoint1_10 in INC. apply uncurry_adjoint1_10 in CIH.
  apply uncurry_adjoint2_10.
  eapply le10_trans. eapply (OBG _ INC CIH).
  apply curry_map10.
  apply _paco_mon; try apply le1_refl; apply curry_bij1_10.
Qed.

Theorem _paco10_mult_strong: forall r,
  paco10 gf (upaco10 gf r) <10== paco10 gf r.
Proof.
  intros. apply curry_map10.
  eapply le1_trans; [| eapply _paco_mult_strong].
  apply _paco_mon; intros []; intros H; apply H.
Qed.

Theorem _paco10_fold: forall r,
  gf (upaco10 gf r) <10== paco10 gf r.
Proof.
  intros. apply uncurry_adjoint1_10.
  eapply le1_trans; [| apply _paco_fold]. apply le1_refl.
Qed.

Theorem _paco10_unfold: forall (MON: _monotone10 gf) r,
  paco10 gf r <10== gf (upaco10 gf r).
Proof.
  intros. apply curry_adjoint2_10.
  eapply _paco_unfold; apply monotone10_map; assumption.
Qed.

Theorem paco10_acc: forall
  l r (OBG: forall rr (INC: r <10= rr) (CIH: l <10= rr), l <10= paco10 gf rr),
  l <10= paco10 gf r.
Proof.
  apply _paco10_acc.
Qed.

Theorem paco10_mon: monotone10 (paco10 gf).
Proof.
  apply monotone10_eq.
  apply _paco10_mon.
Qed.

Theorem upaco10_mon: monotone10 (upaco10 gf).
Proof.
  repeat_intros 12. intros R  LE0.
  destruct R.
  - left. eapply paco10_mon. apply H. apply LE0.
  - right. apply LE0, H.
Qed.
Theorem paco10_mult_strong: forall r,
  paco10 gf (upaco10 gf r) <10= paco10 gf r.
Proof.
  apply _paco10_mult_strong.
Qed.

Corollary paco10_mult: forall r,
  paco10 gf (paco10 gf r) <10= paco10 gf r.
Proof. intros; eapply paco10_mult_strong, paco10_mon; [apply PR|..]; intros; left; assumption. Qed.

Theorem paco10_fold: forall r,
  gf (upaco10 gf r) <10= paco10 gf r.
Proof.
  apply _paco10_fold.
Qed.

Theorem paco10_unfold: forall (MON: monotone10 gf) r,
  paco10 gf r <10= gf (upaco10 gf r).
Proof.
  repeat_intros 1. eapply _paco10_unfold; apply monotone10_eq; assumption.
Qed.

End Arg10_1.

Arguments paco10_acc : clear implicits.
Arguments paco10_mon : clear implicits.
Arguments upaco10_mon : clear implicits.
Arguments paco10_mult_strong : clear implicits.
Arguments paco10_mult : clear implicits.
Arguments paco10_fold : clear implicits.
Arguments paco10_unfold : clear implicits.

Global Instance paco10_inst  (gf : rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9->_) r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : paco_class (paco10 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) :=
{ pacoacc    := paco10_acc gf;
  pacomult   := paco10_mult gf;
  pacofold   := paco10_fold gf;
  pacounfold := paco10_unfold gf }.

(** 2 Mutual Coinduction *)

Section Arg10_2.

Definition monotone10_2 (gf: rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) :=
  forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 r_0 r_1 r'_0 r'_1 (IN: gf r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (LE_0: r_0 <10= r'_0)(LE_1: r_1 <10= r'_1), gf r'_0 r'_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9.

Definition _monotone10_2 (gf: rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) :=
  forall r_0 r_1 r'_0 r'_1(LE_0: r_0 <10= r'_0)(LE_1: r_1 <10= r'_1), gf r_0 r_1 <10== gf r'_0 r'_1.

Lemma monotone10_2_eq (gf: rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) :
  monotone10_2 gf <-> _monotone10_2 gf.
Proof. unfold monotone10_2, _monotone10_2, le10. split; intros; eapply H; eassumption. Qed.

Lemma monotone10_2_map (gf: rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9)
      (MON: _monotone10_2 gf) :
  _monotone_2 (fun R0 R1 => uncurry10 (gf (curry10 R0) (curry10 R1))).
Proof.
  repeat_intros 6. apply uncurry_map10. apply MON; apply curry_map10; assumption.
Qed.

Variable gf_0 gf_1 : rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.

Theorem _paco10_2_0_mon: _monotone10_2 (paco10_2_0 gf_0 gf_1).
Proof.
  repeat_intros 6. eapply curry_map10, _paco_2_0_mon; apply uncurry_map10; assumption.
Qed.

Theorem _paco10_2_1_mon: _monotone10_2 (paco10_2_1 gf_0 gf_1).
Proof.
  repeat_intros 6. eapply curry_map10, _paco_2_1_mon; apply uncurry_map10; assumption.
Qed.

Theorem _paco10_2_0_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_0 <10== rr) (CIH: l <10== rr), l <10== paco10_2_0 gf_0 gf_1 rr r_1),
  l <10== paco10_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_10.
  eapply _paco_2_0_acc. intros.
  apply uncurry_adjoint1_10 in INC. apply uncurry_adjoint1_10 in CIH.
  apply uncurry_adjoint2_10.
  eapply le10_trans. eapply (OBG _ INC CIH).
  apply curry_map10.
  apply _paco_2_0_mon; try apply le1_refl; apply curry_bij1_10.
Qed.

Theorem _paco10_2_1_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_1 <10== rr) (CIH: l <10== rr), l <10== paco10_2_1 gf_0 gf_1 r_0 rr),
  l <10== paco10_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_10.
  eapply _paco_2_1_acc. intros.
  apply uncurry_adjoint1_10 in INC. apply uncurry_adjoint1_10 in CIH.
  apply uncurry_adjoint2_10.
  eapply le10_trans. eapply (OBG _ INC CIH).
  apply curry_map10.
  apply _paco_2_1_mon; try apply le1_refl; apply curry_bij1_10.
Qed.

Theorem _paco10_2_0_mult_strong: forall r_0 r_1,
  paco10_2_0 gf_0 gf_1 (upaco10_2_0 gf_0 gf_1 r_0 r_1) (upaco10_2_1 gf_0 gf_1 r_0 r_1) <10== paco10_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply curry_map10.
  eapply le1_trans; [| eapply _paco_2_0_mult_strong].
  apply _paco_2_0_mon; intros []; intros H; apply H.
Qed.

Theorem _paco10_2_1_mult_strong: forall r_0 r_1,
  paco10_2_1 gf_0 gf_1 (upaco10_2_0 gf_0 gf_1 r_0 r_1) (upaco10_2_1 gf_0 gf_1 r_0 r_1) <10== paco10_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply curry_map10.
  eapply le1_trans; [| eapply _paco_2_1_mult_strong].
  apply _paco_2_1_mon; intros []; intros H; apply H.
Qed.

Theorem _paco10_2_0_fold: forall r_0 r_1,
  gf_0 (upaco10_2_0 gf_0 gf_1 r_0 r_1) (upaco10_2_1 gf_0 gf_1 r_0 r_1) <10== paco10_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_10.
  eapply le1_trans; [| apply _paco_2_0_fold]. apply le1_refl.
Qed.

Theorem _paco10_2_1_fold: forall r_0 r_1,
  gf_1 (upaco10_2_0 gf_0 gf_1 r_0 r_1) (upaco10_2_1 gf_0 gf_1 r_0 r_1) <10== paco10_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_10.
  eapply le1_trans; [| apply _paco_2_1_fold]. apply le1_refl.
Qed.

Theorem _paco10_2_0_unfold: forall (MON: _monotone10_2 gf_0) (MON: _monotone10_2 gf_1) r_0 r_1,
  paco10_2_0 gf_0 gf_1 r_0 r_1 <10== gf_0 (upaco10_2_0 gf_0 gf_1 r_0 r_1) (upaco10_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  intros. apply curry_adjoint2_10.
  eapply _paco_2_0_unfold; apply monotone10_2_map; assumption.
Qed.

Theorem _paco10_2_1_unfold: forall (MON: _monotone10_2 gf_0) (MON: _monotone10_2 gf_1) r_0 r_1,
  paco10_2_1 gf_0 gf_1 r_0 r_1 <10== gf_1 (upaco10_2_0 gf_0 gf_1 r_0 r_1) (upaco10_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  intros. apply curry_adjoint2_10.
  eapply _paco_2_1_unfold; apply monotone10_2_map; assumption.
Qed.

Theorem paco10_2_0_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_0 <10= rr) (CIH: l <10= rr), l <10= paco10_2_0 gf_0 gf_1 rr r_1),
  l <10= paco10_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco10_2_0_acc.
Qed.

Theorem paco10_2_1_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_1 <10= rr) (CIH: l <10= rr), l <10= paco10_2_1 gf_0 gf_1 r_0 rr),
  l <10= paco10_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco10_2_1_acc.
Qed.

Theorem paco10_2_0_mon: monotone10_2 (paco10_2_0 gf_0 gf_1).
Proof.
  apply monotone10_2_eq.
  apply _paco10_2_0_mon.
Qed.

Theorem paco10_2_1_mon: monotone10_2 (paco10_2_1 gf_0 gf_1).
Proof.
  apply monotone10_2_eq.
  apply _paco10_2_1_mon.
Qed.

Theorem upaco10_2_0_mon: monotone10_2 (upaco10_2_0 gf_0 gf_1).
Proof.
  repeat_intros 14. intros R  LE0 LE1.
  destruct R.
  - left. eapply paco10_2_0_mon. apply H. apply LE0. apply LE1.
  - right. apply LE0, H.
Qed.
Theorem upaco10_2_1_mon: monotone10_2 (upaco10_2_1 gf_0 gf_1).
Proof.
  repeat_intros 14. intros R  LE0 LE1.
  destruct R.
  - left. eapply paco10_2_1_mon. apply H. apply LE0. apply LE1.
  - right. apply LE1, H.
Qed.
Theorem paco10_2_0_mult_strong: forall r_0 r_1,
  paco10_2_0 gf_0 gf_1 (upaco10_2_0 gf_0 gf_1 r_0 r_1) (upaco10_2_1 gf_0 gf_1 r_0 r_1) <10= paco10_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco10_2_0_mult_strong.
Qed.

Theorem paco10_2_1_mult_strong: forall r_0 r_1,
  paco10_2_1 gf_0 gf_1 (upaco10_2_0 gf_0 gf_1 r_0 r_1) (upaco10_2_1 gf_0 gf_1 r_0 r_1) <10= paco10_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco10_2_1_mult_strong.
Qed.

Corollary paco10_2_0_mult: forall r_0 r_1,
  paco10_2_0 gf_0 gf_1 (paco10_2_0 gf_0 gf_1 r_0 r_1) (paco10_2_1 gf_0 gf_1 r_0 r_1) <10= paco10_2_0 gf_0 gf_1 r_0 r_1.
Proof. intros; eapply paco10_2_0_mult_strong, paco10_2_0_mon; [apply PR|..]; intros; left; assumption. Qed.

Corollary paco10_2_1_mult: forall r_0 r_1,
  paco10_2_1 gf_0 gf_1 (paco10_2_0 gf_0 gf_1 r_0 r_1) (paco10_2_1 gf_0 gf_1 r_0 r_1) <10= paco10_2_1 gf_0 gf_1 r_0 r_1.
Proof. intros; eapply paco10_2_1_mult_strong, paco10_2_1_mon; [apply PR|..]; intros; left; assumption. Qed.

Theorem paco10_2_0_fold: forall r_0 r_1,
  gf_0 (upaco10_2_0 gf_0 gf_1 r_0 r_1) (upaco10_2_1 gf_0 gf_1 r_0 r_1) <10= paco10_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco10_2_0_fold.
Qed.

Theorem paco10_2_1_fold: forall r_0 r_1,
  gf_1 (upaco10_2_0 gf_0 gf_1 r_0 r_1) (upaco10_2_1 gf_0 gf_1 r_0 r_1) <10= paco10_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco10_2_1_fold.
Qed.

Theorem paco10_2_0_unfold: forall (MON: monotone10_2 gf_0) (MON: monotone10_2 gf_1) r_0 r_1,
  paco10_2_0 gf_0 gf_1 r_0 r_1 <10= gf_0 (upaco10_2_0 gf_0 gf_1 r_0 r_1) (upaco10_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  repeat_intros 2. eapply _paco10_2_0_unfold; apply monotone10_2_eq; assumption.
Qed.

Theorem paco10_2_1_unfold: forall (MON: monotone10_2 gf_0) (MON: monotone10_2 gf_1) r_0 r_1,
  paco10_2_1 gf_0 gf_1 r_0 r_1 <10= gf_1 (upaco10_2_0 gf_0 gf_1 r_0 r_1) (upaco10_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  repeat_intros 2. eapply _paco10_2_1_unfold; apply monotone10_2_eq; assumption.
Qed.

End Arg10_2.

Arguments paco10_2_0_acc : clear implicits.
Arguments paco10_2_1_acc : clear implicits.
Arguments paco10_2_0_mon : clear implicits.
Arguments paco10_2_1_mon : clear implicits.
Arguments upaco10_2_0_mon : clear implicits.
Arguments upaco10_2_1_mon : clear implicits.
Arguments paco10_2_0_mult_strong : clear implicits.
Arguments paco10_2_1_mult_strong : clear implicits.
Arguments paco10_2_0_mult : clear implicits.
Arguments paco10_2_1_mult : clear implicits.
Arguments paco10_2_0_fold : clear implicits.
Arguments paco10_2_1_fold : clear implicits.
Arguments paco10_2_0_unfold : clear implicits.
Arguments paco10_2_1_unfold : clear implicits.

Global Instance paco10_2_0_inst  (gf_0 gf_1 : rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9->_) r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : paco_class (paco10_2_0 gf_0 gf_1 r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) :=
{ pacoacc    := paco10_2_0_acc gf_0 gf_1;
  pacomult   := paco10_2_0_mult gf_0 gf_1;
  pacofold   := paco10_2_0_fold gf_0 gf_1;
  pacounfold := paco10_2_0_unfold gf_0 gf_1 }.

Global Instance paco10_2_1_inst  (gf_0 gf_1 : rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9->_) r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : paco_class (paco10_2_1 gf_0 gf_1 r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) :=
{ pacoacc    := paco10_2_1_acc gf_0 gf_1;
  pacomult   := paco10_2_1_mult gf_0 gf_1;
  pacofold   := paco10_2_1_fold gf_0 gf_1;
  pacounfold := paco10_2_1_unfold gf_0 gf_1 }.

(** 3 Mutual Coinduction *)

Section Arg10_3.

Definition monotone10_3 (gf: rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) :=
  forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 r_0 r_1 r_2 r'_0 r'_1 r'_2 (IN: gf r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (LE_0: r_0 <10= r'_0)(LE_1: r_1 <10= r'_1)(LE_2: r_2 <10= r'_2), gf r'_0 r'_1 r'_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9.

Definition _monotone10_3 (gf: rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) :=
  forall r_0 r_1 r_2 r'_0 r'_1 r'_2(LE_0: r_0 <10= r'_0)(LE_1: r_1 <10= r'_1)(LE_2: r_2 <10= r'_2), gf r_0 r_1 r_2 <10== gf r'_0 r'_1 r'_2.

Lemma monotone10_3_eq (gf: rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) :
  monotone10_3 gf <-> _monotone10_3 gf.
Proof. unfold monotone10_3, _monotone10_3, le10. split; intros; eapply H; eassumption. Qed.

Lemma monotone10_3_map (gf: rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9)
      (MON: _monotone10_3 gf) :
  _monotone_3 (fun R0 R1 R2 => uncurry10 (gf (curry10 R0) (curry10 R1) (curry10 R2))).
Proof.
  repeat_intros 9. apply uncurry_map10. apply MON; apply curry_map10; assumption.
Qed.

Variable gf_0 gf_1 gf_2 : rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.
Arguments gf_2 : clear implicits.

Theorem _paco10_3_0_mon: _monotone10_3 (paco10_3_0 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 9. eapply curry_map10, _paco_3_0_mon; apply uncurry_map10; assumption.
Qed.

Theorem _paco10_3_1_mon: _monotone10_3 (paco10_3_1 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 9. eapply curry_map10, _paco_3_1_mon; apply uncurry_map10; assumption.
Qed.

Theorem _paco10_3_2_mon: _monotone10_3 (paco10_3_2 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 9. eapply curry_map10, _paco_3_2_mon; apply uncurry_map10; assumption.
Qed.

Theorem _paco10_3_0_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_0 <10== rr) (CIH: l <10== rr), l <10== paco10_3_0 gf_0 gf_1 gf_2 rr r_1 r_2),
  l <10== paco10_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_10.
  eapply _paco_3_0_acc. intros.
  apply uncurry_adjoint1_10 in INC. apply uncurry_adjoint1_10 in CIH.
  apply uncurry_adjoint2_10.
  eapply le10_trans. eapply (OBG _ INC CIH).
  apply curry_map10.
  apply _paco_3_0_mon; try apply le1_refl; apply curry_bij1_10.
Qed.

Theorem _paco10_3_1_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_1 <10== rr) (CIH: l <10== rr), l <10== paco10_3_1 gf_0 gf_1 gf_2 r_0 rr r_2),
  l <10== paco10_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_10.
  eapply _paco_3_1_acc. intros.
  apply uncurry_adjoint1_10 in INC. apply uncurry_adjoint1_10 in CIH.
  apply uncurry_adjoint2_10.
  eapply le10_trans. eapply (OBG _ INC CIH).
  apply curry_map10.
  apply _paco_3_1_mon; try apply le1_refl; apply curry_bij1_10.
Qed.

Theorem _paco10_3_2_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_2 <10== rr) (CIH: l <10== rr), l <10== paco10_3_2 gf_0 gf_1 gf_2 r_0 r_1 rr),
  l <10== paco10_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_10.
  eapply _paco_3_2_acc. intros.
  apply uncurry_adjoint1_10 in INC. apply uncurry_adjoint1_10 in CIH.
  apply uncurry_adjoint2_10.
  eapply le10_trans. eapply (OBG _ INC CIH).
  apply curry_map10.
  apply _paco_3_2_mon; try apply le1_refl; apply curry_bij1_10.
Qed.

Theorem _paco10_3_0_mult_strong: forall r_0 r_1 r_2,
  paco10_3_0 gf_0 gf_1 gf_2 (upaco10_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco10_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco10_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <10== paco10_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply curry_map10.
  eapply le1_trans; [| eapply _paco_3_0_mult_strong].
  apply _paco_3_0_mon; intros []; intros H; apply H.
Qed.

Theorem _paco10_3_1_mult_strong: forall r_0 r_1 r_2,
  paco10_3_1 gf_0 gf_1 gf_2 (upaco10_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco10_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco10_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <10== paco10_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply curry_map10.
  eapply le1_trans; [| eapply _paco_3_1_mult_strong].
  apply _paco_3_1_mon; intros []; intros H; apply H.
Qed.

Theorem _paco10_3_2_mult_strong: forall r_0 r_1 r_2,
  paco10_3_2 gf_0 gf_1 gf_2 (upaco10_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco10_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco10_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <10== paco10_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply curry_map10.
  eapply le1_trans; [| eapply _paco_3_2_mult_strong].
  apply _paco_3_2_mon; intros []; intros H; apply H.
Qed.

Theorem _paco10_3_0_fold: forall r_0 r_1 r_2,
  gf_0 (upaco10_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco10_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco10_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <10== paco10_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_10.
  eapply le1_trans; [| apply _paco_3_0_fold]. apply le1_refl.
Qed.

Theorem _paco10_3_1_fold: forall r_0 r_1 r_2,
  gf_1 (upaco10_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco10_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco10_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <10== paco10_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_10.
  eapply le1_trans; [| apply _paco_3_1_fold]. apply le1_refl.
Qed.

Theorem _paco10_3_2_fold: forall r_0 r_1 r_2,
  gf_2 (upaco10_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco10_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco10_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <10== paco10_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_10.
  eapply le1_trans; [| apply _paco_3_2_fold]. apply le1_refl.
Qed.

Theorem _paco10_3_0_unfold: forall (MON: _monotone10_3 gf_0) (MON: _monotone10_3 gf_1) (MON: _monotone10_3 gf_2) r_0 r_1 r_2,
  paco10_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 <10== gf_0 (upaco10_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco10_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco10_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  intros. apply curry_adjoint2_10.
  eapply _paco_3_0_unfold; apply monotone10_3_map; assumption.
Qed.

Theorem _paco10_3_1_unfold: forall (MON: _monotone10_3 gf_0) (MON: _monotone10_3 gf_1) (MON: _monotone10_3 gf_2) r_0 r_1 r_2,
  paco10_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 <10== gf_1 (upaco10_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco10_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco10_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  intros. apply curry_adjoint2_10.
  eapply _paco_3_1_unfold; apply monotone10_3_map; assumption.
Qed.

Theorem _paco10_3_2_unfold: forall (MON: _monotone10_3 gf_0) (MON: _monotone10_3 gf_1) (MON: _monotone10_3 gf_2) r_0 r_1 r_2,
  paco10_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 <10== gf_2 (upaco10_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco10_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco10_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  intros. apply curry_adjoint2_10.
  eapply _paco_3_2_unfold; apply monotone10_3_map; assumption.
Qed.

Theorem paco10_3_0_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_0 <10= rr) (CIH: l <10= rr), l <10= paco10_3_0 gf_0 gf_1 gf_2 rr r_1 r_2),
  l <10= paco10_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco10_3_0_acc.
Qed.

Theorem paco10_3_1_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_1 <10= rr) (CIH: l <10= rr), l <10= paco10_3_1 gf_0 gf_1 gf_2 r_0 rr r_2),
  l <10= paco10_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco10_3_1_acc.
Qed.

Theorem paco10_3_2_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_2 <10= rr) (CIH: l <10= rr), l <10= paco10_3_2 gf_0 gf_1 gf_2 r_0 r_1 rr),
  l <10= paco10_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco10_3_2_acc.
Qed.

Theorem paco10_3_0_mon: monotone10_3 (paco10_3_0 gf_0 gf_1 gf_2).
Proof.
  apply monotone10_3_eq.
  apply _paco10_3_0_mon.
Qed.

Theorem paco10_3_1_mon: monotone10_3 (paco10_3_1 gf_0 gf_1 gf_2).
Proof.
  apply monotone10_3_eq.
  apply _paco10_3_1_mon.
Qed.

Theorem paco10_3_2_mon: monotone10_3 (paco10_3_2 gf_0 gf_1 gf_2).
Proof.
  apply monotone10_3_eq.
  apply _paco10_3_2_mon.
Qed.

Theorem upaco10_3_0_mon: monotone10_3 (upaco10_3_0 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 16. intros R  LE0 LE1 LE2.
  destruct R.
  - left. eapply paco10_3_0_mon. apply H. apply LE0. apply LE1. apply LE2.
  - right. apply LE0, H.
Qed.
Theorem upaco10_3_1_mon: monotone10_3 (upaco10_3_1 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 16. intros R  LE0 LE1 LE2.
  destruct R.
  - left. eapply paco10_3_1_mon. apply H. apply LE0. apply LE1. apply LE2.
  - right. apply LE1, H.
Qed.
Theorem upaco10_3_2_mon: monotone10_3 (upaco10_3_2 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 16. intros R  LE0 LE1 LE2.
  destruct R.
  - left. eapply paco10_3_2_mon. apply H. apply LE0. apply LE1. apply LE2.
  - right. apply LE2, H.
Qed.
Theorem paco10_3_0_mult_strong: forall r_0 r_1 r_2,
  paco10_3_0 gf_0 gf_1 gf_2 (upaco10_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco10_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco10_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <10= paco10_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco10_3_0_mult_strong.
Qed.

Theorem paco10_3_1_mult_strong: forall r_0 r_1 r_2,
  paco10_3_1 gf_0 gf_1 gf_2 (upaco10_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco10_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco10_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <10= paco10_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco10_3_1_mult_strong.
Qed.

Theorem paco10_3_2_mult_strong: forall r_0 r_1 r_2,
  paco10_3_2 gf_0 gf_1 gf_2 (upaco10_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco10_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco10_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <10= paco10_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco10_3_2_mult_strong.
Qed.

Corollary paco10_3_0_mult: forall r_0 r_1 r_2,
  paco10_3_0 gf_0 gf_1 gf_2 (paco10_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco10_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco10_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <10= paco10_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco10_3_0_mult_strong, paco10_3_0_mon; [apply PR|..]; intros; left; assumption. Qed.

Corollary paco10_3_1_mult: forall r_0 r_1 r_2,
  paco10_3_1 gf_0 gf_1 gf_2 (paco10_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco10_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco10_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <10= paco10_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco10_3_1_mult_strong, paco10_3_1_mon; [apply PR|..]; intros; left; assumption. Qed.

Corollary paco10_3_2_mult: forall r_0 r_1 r_2,
  paco10_3_2 gf_0 gf_1 gf_2 (paco10_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco10_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco10_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <10= paco10_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco10_3_2_mult_strong, paco10_3_2_mon; [apply PR|..]; intros; left; assumption. Qed.

Theorem paco10_3_0_fold: forall r_0 r_1 r_2,
  gf_0 (upaco10_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco10_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco10_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <10= paco10_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco10_3_0_fold.
Qed.

Theorem paco10_3_1_fold: forall r_0 r_1 r_2,
  gf_1 (upaco10_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco10_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco10_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <10= paco10_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco10_3_1_fold.
Qed.

Theorem paco10_3_2_fold: forall r_0 r_1 r_2,
  gf_2 (upaco10_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco10_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco10_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <10= paco10_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco10_3_2_fold.
Qed.

Theorem paco10_3_0_unfold: forall (MON: monotone10_3 gf_0) (MON: monotone10_3 gf_1) (MON: monotone10_3 gf_2) r_0 r_1 r_2,
  paco10_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 <10= gf_0 (upaco10_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco10_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco10_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  repeat_intros 3. eapply _paco10_3_0_unfold; apply monotone10_3_eq; assumption.
Qed.

Theorem paco10_3_1_unfold: forall (MON: monotone10_3 gf_0) (MON: monotone10_3 gf_1) (MON: monotone10_3 gf_2) r_0 r_1 r_2,
  paco10_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 <10= gf_1 (upaco10_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco10_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco10_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  repeat_intros 3. eapply _paco10_3_1_unfold; apply monotone10_3_eq; assumption.
Qed.

Theorem paco10_3_2_unfold: forall (MON: monotone10_3 gf_0) (MON: monotone10_3 gf_1) (MON: monotone10_3 gf_2) r_0 r_1 r_2,
  paco10_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 <10= gf_2 (upaco10_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco10_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco10_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  repeat_intros 3. eapply _paco10_3_2_unfold; apply monotone10_3_eq; assumption.
Qed.

End Arg10_3.

Arguments paco10_3_0_acc : clear implicits.
Arguments paco10_3_1_acc : clear implicits.
Arguments paco10_3_2_acc : clear implicits.
Arguments paco10_3_0_mon : clear implicits.
Arguments paco10_3_1_mon : clear implicits.
Arguments paco10_3_2_mon : clear implicits.
Arguments upaco10_3_0_mon : clear implicits.
Arguments upaco10_3_1_mon : clear implicits.
Arguments upaco10_3_2_mon : clear implicits.
Arguments paco10_3_0_mult_strong : clear implicits.
Arguments paco10_3_1_mult_strong : clear implicits.
Arguments paco10_3_2_mult_strong : clear implicits.
Arguments paco10_3_0_mult : clear implicits.
Arguments paco10_3_1_mult : clear implicits.
Arguments paco10_3_2_mult : clear implicits.
Arguments paco10_3_0_fold : clear implicits.
Arguments paco10_3_1_fold : clear implicits.
Arguments paco10_3_2_fold : clear implicits.
Arguments paco10_3_0_unfold : clear implicits.
Arguments paco10_3_1_unfold : clear implicits.
Arguments paco10_3_2_unfold : clear implicits.

Global Instance paco10_3_0_inst  (gf_0 gf_1 gf_2 : rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : paco_class (paco10_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) :=
{ pacoacc    := paco10_3_0_acc gf_0 gf_1 gf_2;
  pacomult   := paco10_3_0_mult gf_0 gf_1 gf_2;
  pacofold   := paco10_3_0_fold gf_0 gf_1 gf_2;
  pacounfold := paco10_3_0_unfold gf_0 gf_1 gf_2 }.

Global Instance paco10_3_1_inst  (gf_0 gf_1 gf_2 : rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : paco_class (paco10_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) :=
{ pacoacc    := paco10_3_1_acc gf_0 gf_1 gf_2;
  pacomult   := paco10_3_1_mult gf_0 gf_1 gf_2;
  pacofold   := paco10_3_1_fold gf_0 gf_1 gf_2;
  pacounfold := paco10_3_1_unfold gf_0 gf_1 gf_2 }.

Global Instance paco10_3_2_inst  (gf_0 gf_1 gf_2 : rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : paco_class (paco10_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) :=
{ pacoacc    := paco10_3_2_acc gf_0 gf_1 gf_2;
  pacomult   := paco10_3_2_mult gf_0 gf_1 gf_2;
  pacofold   := paco10_3_2_fold gf_0 gf_1 gf_2;
  pacounfold := paco10_3_2_unfold gf_0 gf_1 gf_2 }.

Lemma upaco10_clear gf x0 x1 x2 x3 x4 x5 x6 x7 x8 x9:
  upaco10 gf bot10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 <-> paco10 gf bot10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9.
Proof. split; intros; [destruct H;[apply H|destruct H]|left; apply H]. Qed.

End PACO10.

Global Opaque paco10.

Hint Unfold upaco10.
Hint Resolve paco10_fold.
Hint Unfold monotone10.

Global Opaque paco10_2_0.
Global Opaque paco10_2_1.

Hint Unfold upaco10_2_0.
Hint Unfold upaco10_2_1.
Hint Resolve paco10_2_0_fold.
Hint Resolve paco10_2_1_fold.
Hint Unfold monotone10_2.

Global Opaque paco10_3_0.
Global Opaque paco10_3_1.
Global Opaque paco10_3_2.

Hint Unfold upaco10_3_0.
Hint Unfold upaco10_3_1.
Hint Unfold upaco10_3_2.
Hint Resolve paco10_3_0_fold.
Hint Resolve paco10_3_1_fold.
Hint Resolve paco10_3_2_fold.
Hint Unfold monotone10_3.

