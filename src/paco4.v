Require Export paconotation pacotacuser.
Require Import paconotation_internal pacotac pacon.
Set Implicit Arguments.

Section PACO4.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.

Record sig4T :=
  exist4T { 
      proj4T0: @T0;
      proj4T1: @T1 proj4T0;
      proj4T2: @T2 proj4T0 proj4T1;
      proj4T3: @T3 proj4T0 proj4T1 proj4T2;
    }.

Definition uncurry4 (R: rel4 T0 T1 T2 T3): rel1 sig4T := fun x => R (proj4T0 x) (proj4T1 x) (proj4T2 x) (proj4T3 x).

Definition curry4 (R: rel1 sig4T): rel4 T0 T1 T2 T3 :=
  fun x0 x1 x2 x3 => R (exist4T x3).

Lemma uncurry_map4 r0 r1 (LE : r0 <4== r1) : uncurry4 r0 <1== uncurry4 r1.
Proof. intros [] H. apply LE. apply H. Qed.

Lemma uncurry_map_rev4 r0 r1 (LE: uncurry4 r0 <1== uncurry4 r1) : r0 <4== r1.
Proof.
  repeat_intros 4. intros H. apply (LE (exist4T x3) H).
Qed.

Lemma curry_map4 r0 r1 (LE: r0 <1== r1) : curry4 r0 <4== curry4 r1.
Proof. 
  repeat_intros 4. intros H. apply (LE (exist4T x3) H).
Qed.

Lemma curry_map_rev4 r0 r1 (LE: curry4 r0 <4== curry4 r1) : r0 <1== r1.
Proof. 
  intros [] H. apply LE. apply H.
Qed.

Lemma uncurry_bij1_4 r : curry4 (uncurry4 r) <4== r.
Proof. unfold le4. repeat_intros 4. intros H. apply H. Qed.

Lemma uncurry_bij2_4 r : r <4== curry4 (uncurry4 r).
Proof. unfold le4. repeat_intros 4. intros H. apply H. Qed.

Lemma curry_bij1_4 r : uncurry4 (curry4 r) <1== r.
Proof. intros []. intro H. apply H. Qed.

Lemma curry_bij2_4 r : r <1== uncurry4 (curry4 r).
Proof. intros []. intro H. apply H. Qed.

Lemma uncurry_adjoint1_4 r0 r1 (LE: uncurry4 r0 <1== r1) : r0 <4== curry4 r1.
Proof.
  apply uncurry_map_rev4. eapply le1_trans; [apply LE|]. apply curry_bij2_4.
Qed.

Lemma uncurry_adjoint2_4 r0 r1 (LE: r0 <4== curry4 r1) : uncurry4 r0 <1== r1.
Proof.
  apply curry_map_rev4. eapply le4_trans; [|apply LE]. apply uncurry_bij2_4.
Qed.

Lemma curry_adjoint1_4 r0 r1 (LE: curry4 r0 <4== r1) : r0 <1== uncurry4 r1.
Proof.
  apply curry_map_rev4. eapply le4_trans; [apply LE|]. apply uncurry_bij2_4.
Qed.

Lemma curry_adjoint2_4 r0 r1 (LE: r0 <1== uncurry4 r1) : curry4 r0 <4== r1.
Proof.
  apply uncurry_map_rev4. eapply le1_trans; [|apply LE]. apply curry_bij1_4.
Qed.

(** ** Predicates of Arity 4
*)

Section Arg4_def.
Variable gf : rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3.
Arguments gf : clear implicits.

Definition paco4( r: rel4 T0 T1 T2 T3) : rel4 T0 T1 T2 T3 :=
  curry4 (paco (fun R0 => uncurry4 (gf (curry4 R0))) (uncurry4 r)).

Definition upaco4( r: rel4 T0 T1 T2 T3) := paco4 r \4/ r.
End Arg4_def.
Arguments paco4 : clear implicits.
Arguments upaco4 : clear implicits.
Hint Unfold upaco4.

Section Arg4_2_def.
Variable gf_0 gf_1 : rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.

Definition paco4_2_0( r_0 r_1: rel4 T0 T1 T2 T3) : rel4 T0 T1 T2 T3 :=
  curry4 (paco_2_0 (fun R0 R1 => uncurry4 (gf_0 (curry4 R0) (curry4 R1))) (fun R0 R1 => uncurry4 (gf_1 (curry4 R0) (curry4 R1))) (uncurry4 r_0) (uncurry4 r_1)).

Definition paco4_2_1( r_0 r_1: rel4 T0 T1 T2 T3) : rel4 T0 T1 T2 T3 :=
  curry4 (paco_2_1 (fun R0 R1 => uncurry4 (gf_0 (curry4 R0) (curry4 R1))) (fun R0 R1 => uncurry4 (gf_1 (curry4 R0) (curry4 R1))) (uncurry4 r_0) (uncurry4 r_1)).

Definition upaco4_2_0( r_0 r_1: rel4 T0 T1 T2 T3) := paco4_2_0 r_0 r_1 \4/ r_0.
Definition upaco4_2_1( r_0 r_1: rel4 T0 T1 T2 T3) := paco4_2_1 r_0 r_1 \4/ r_1.
End Arg4_2_def.
Arguments paco4_2_0 : clear implicits.
Arguments upaco4_2_0 : clear implicits.
Hint Unfold upaco4_2_0.
Arguments paco4_2_1 : clear implicits.
Arguments upaco4_2_1 : clear implicits.
Hint Unfold upaco4_2_1.

Section Arg4_3_def.
Variable gf_0 gf_1 gf_2 : rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.
Arguments gf_2 : clear implicits.

Definition paco4_3_0( r_0 r_1 r_2: rel4 T0 T1 T2 T3) : rel4 T0 T1 T2 T3 :=
  curry4 (paco_3_0 (fun R0 R1 R2 => uncurry4 (gf_0 (curry4 R0) (curry4 R1) (curry4 R2))) (fun R0 R1 R2 => uncurry4 (gf_1 (curry4 R0) (curry4 R1) (curry4 R2))) (fun R0 R1 R2 => uncurry4 (gf_2 (curry4 R0) (curry4 R1) (curry4 R2))) (uncurry4 r_0) (uncurry4 r_1) (uncurry4 r_2)).

Definition paco4_3_1( r_0 r_1 r_2: rel4 T0 T1 T2 T3) : rel4 T0 T1 T2 T3 :=
  curry4 (paco_3_1 (fun R0 R1 R2 => uncurry4 (gf_0 (curry4 R0) (curry4 R1) (curry4 R2))) (fun R0 R1 R2 => uncurry4 (gf_1 (curry4 R0) (curry4 R1) (curry4 R2))) (fun R0 R1 R2 => uncurry4 (gf_2 (curry4 R0) (curry4 R1) (curry4 R2))) (uncurry4 r_0) (uncurry4 r_1) (uncurry4 r_2)).

Definition paco4_3_2( r_0 r_1 r_2: rel4 T0 T1 T2 T3) : rel4 T0 T1 T2 T3 :=
  curry4 (paco_3_2 (fun R0 R1 R2 => uncurry4 (gf_0 (curry4 R0) (curry4 R1) (curry4 R2))) (fun R0 R1 R2 => uncurry4 (gf_1 (curry4 R0) (curry4 R1) (curry4 R2))) (fun R0 R1 R2 => uncurry4 (gf_2 (curry4 R0) (curry4 R1) (curry4 R2))) (uncurry4 r_0) (uncurry4 r_1) (uncurry4 r_2)).

Definition upaco4_3_0( r_0 r_1 r_2: rel4 T0 T1 T2 T3) := paco4_3_0 r_0 r_1 r_2 \4/ r_0.
Definition upaco4_3_1( r_0 r_1 r_2: rel4 T0 T1 T2 T3) := paco4_3_1 r_0 r_1 r_2 \4/ r_1.
Definition upaco4_3_2( r_0 r_1 r_2: rel4 T0 T1 T2 T3) := paco4_3_2 r_0 r_1 r_2 \4/ r_2.
End Arg4_3_def.
Arguments paco4_3_0 : clear implicits.
Arguments upaco4_3_0 : clear implicits.
Hint Unfold upaco4_3_0.
Arguments paco4_3_1 : clear implicits.
Arguments upaco4_3_1 : clear implicits.
Hint Unfold upaco4_3_1.
Arguments paco4_3_2 : clear implicits.
Arguments upaco4_3_2 : clear implicits.
Hint Unfold upaco4_3_2.

(** 1 Mutual Coinduction *)

Section Arg4_1.

Definition monotone4 (gf: rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3) :=
  forall x0 x1 x2 x3 r r' (IN: gf r x0 x1 x2 x3) (LE: r <4= r'), gf r' x0 x1 x2 x3.

Definition _monotone4 (gf: rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3) :=
  forall r r'(LE: r <4= r'), gf r <4== gf r'.

Lemma monotone4_eq (gf: rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3) :
  monotone4 gf <-> _monotone4 gf.
Proof. unfold monotone4, _monotone4, le4. split; intros; eapply H; eassumption. Qed.

Lemma monotone4_map (gf: rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3)
      (MON: _monotone4 gf) :
  _monotone (fun R0 => uncurry4 (gf (curry4 R0))).
Proof.
  repeat_intros 3. apply uncurry_map4. apply MON; apply curry_map4; assumption.
Qed.

Variable gf : rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3.
Arguments gf : clear implicits.

Theorem _paco4_mon: _monotone4 (paco4 gf).
Proof.
  repeat_intros 3. eapply curry_map4, _paco_mon; apply uncurry_map4; assumption.
Qed.

Theorem _paco4_acc: forall
  l r (OBG: forall rr (INC: r <4== rr) (CIH: l <4== rr), l <4== paco4 gf rr),
  l <4== paco4 gf r.
Proof.
  intros. apply uncurry_adjoint1_4.
  eapply _paco_acc. intros.
  apply uncurry_adjoint1_4 in INC. apply uncurry_adjoint1_4 in CIH.
  apply uncurry_adjoint2_4.
  eapply le4_trans. eapply (OBG _ INC CIH).
  apply curry_map4.
  apply _paco_mon; try apply le1_refl; apply curry_bij1_4.
Qed.

Theorem _paco4_mult_strong: forall r,
  paco4 gf (upaco4 gf r) <4== paco4 gf r.
Proof.
  intros. apply curry_map4.
  eapply le1_trans; [| eapply _paco_mult_strong].
  apply _paco_mon; intros []; intros H; apply H.
Qed.

Theorem _paco4_fold: forall r,
  gf (upaco4 gf r) <4== paco4 gf r.
Proof.
  intros. apply uncurry_adjoint1_4.
  eapply le1_trans; [| apply _paco_fold]. apply le1_refl.
Qed.

Theorem _paco4_unfold: forall (MON: _monotone4 gf) r,
  paco4 gf r <4== gf (upaco4 gf r).
Proof.
  intros. apply curry_adjoint2_4.
  eapply _paco_unfold; apply monotone4_map; assumption.
Qed.

Theorem paco4_acc: forall
  l r (OBG: forall rr (INC: r <4= rr) (CIH: l <4= rr), l <4= paco4 gf rr),
  l <4= paco4 gf r.
Proof.
  apply _paco4_acc.
Qed.

Theorem paco4_mon: monotone4 (paco4 gf).
Proof.
  apply monotone4_eq.
  apply _paco4_mon.
Qed.

Theorem paco4_mult_strong: forall r,
  paco4 gf (upaco4 gf r) <4= paco4 gf r.
Proof.
  apply _paco4_mult_strong.
Qed.

Corollary paco4_mult: forall r,
  paco4 gf (paco4 gf r) <4= paco4 gf r.
Proof. intros; eapply paco4_mult_strong, paco4_mon; [apply PR|..]; intros; left; assumption. Qed.

Theorem paco4_fold: forall r,
  gf (upaco4 gf r) <4= paco4 gf r.
Proof.
  apply _paco4_fold.
Qed.

Theorem paco4_unfold: forall (MON: monotone4 gf) r,
  paco4 gf r <4= gf (upaco4 gf r).
Proof.
  repeat_intros 1. eapply _paco4_unfold; apply monotone4_eq; assumption.
Qed.

End Arg4_1.

Arguments paco4_acc : clear implicits.
Arguments paco4_mon : clear implicits.
Arguments paco4_mult_strong : clear implicits.
Arguments paco4_mult : clear implicits.
Arguments paco4_fold : clear implicits.
Arguments paco4_unfold : clear implicits.

Global Instance paco4_inst  (gf : rel4 T0 T1 T2 T3->_) r x0 x1 x2 x3 : paco_class (paco4 gf r x0 x1 x2 x3) :=
{ pacoacc    := paco4_acc gf;
  pacomult   := paco4_mult gf;
  pacofold   := paco4_fold gf;
  pacounfold := paco4_unfold gf }.

(** 2 Mutual Coinduction *)

Section Arg4_2.

Definition monotone4_2 (gf: rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3) :=
  forall x0 x1 x2 x3 r_0 r_1 r'_0 r'_1 (IN: gf r_0 r_1 x0 x1 x2 x3) (LE_0: r_0 <4= r'_0)(LE_1: r_1 <4= r'_1), gf r'_0 r'_1 x0 x1 x2 x3.

Definition _monotone4_2 (gf: rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3) :=
  forall r_0 r_1 r'_0 r'_1(LE_0: r_0 <4= r'_0)(LE_1: r_1 <4= r'_1), gf r_0 r_1 <4== gf r'_0 r'_1.

Lemma monotone4_2_eq (gf: rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3) :
  monotone4_2 gf <-> _monotone4_2 gf.
Proof. unfold monotone4_2, _monotone4_2, le4. split; intros; eapply H; eassumption. Qed.

Lemma monotone4_2_map (gf: rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3)
      (MON: _monotone4_2 gf) :
  _monotone_2 (fun R0 R1 => uncurry4 (gf (curry4 R0) (curry4 R1))).
Proof.
  repeat_intros 6. apply uncurry_map4. apply MON; apply curry_map4; assumption.
Qed.

Variable gf_0 gf_1 : rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.

Theorem _paco4_2_0_mon: _monotone4_2 (paco4_2_0 gf_0 gf_1).
Proof.
  repeat_intros 6. eapply curry_map4, _paco_2_0_mon; apply uncurry_map4; assumption.
Qed.

Theorem _paco4_2_1_mon: _monotone4_2 (paco4_2_1 gf_0 gf_1).
Proof.
  repeat_intros 6. eapply curry_map4, _paco_2_1_mon; apply uncurry_map4; assumption.
Qed.

Theorem _paco4_2_0_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_0 <4== rr) (CIH: l <4== rr), l <4== paco4_2_0 gf_0 gf_1 rr r_1),
  l <4== paco4_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_4.
  eapply _paco_2_0_acc. intros.
  apply uncurry_adjoint1_4 in INC. apply uncurry_adjoint1_4 in CIH.
  apply uncurry_adjoint2_4.
  eapply le4_trans. eapply (OBG _ INC CIH).
  apply curry_map4.
  apply _paco_2_0_mon; try apply le1_refl; apply curry_bij1_4.
Qed.

Theorem _paco4_2_1_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_1 <4== rr) (CIH: l <4== rr), l <4== paco4_2_1 gf_0 gf_1 r_0 rr),
  l <4== paco4_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_4.
  eapply _paco_2_1_acc. intros.
  apply uncurry_adjoint1_4 in INC. apply uncurry_adjoint1_4 in CIH.
  apply uncurry_adjoint2_4.
  eapply le4_trans. eapply (OBG _ INC CIH).
  apply curry_map4.
  apply _paco_2_1_mon; try apply le1_refl; apply curry_bij1_4.
Qed.

Theorem _paco4_2_0_mult_strong: forall r_0 r_1,
  paco4_2_0 gf_0 gf_1 (upaco4_2_0 gf_0 gf_1 r_0 r_1) (upaco4_2_1 gf_0 gf_1 r_0 r_1) <4== paco4_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply curry_map4.
  eapply le1_trans; [| eapply _paco_2_0_mult_strong].
  apply _paco_2_0_mon; intros []; intros H; apply H.
Qed.

Theorem _paco4_2_1_mult_strong: forall r_0 r_1,
  paco4_2_1 gf_0 gf_1 (upaco4_2_0 gf_0 gf_1 r_0 r_1) (upaco4_2_1 gf_0 gf_1 r_0 r_1) <4== paco4_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply curry_map4.
  eapply le1_trans; [| eapply _paco_2_1_mult_strong].
  apply _paco_2_1_mon; intros []; intros H; apply H.
Qed.

Theorem _paco4_2_0_fold: forall r_0 r_1,
  gf_0 (upaco4_2_0 gf_0 gf_1 r_0 r_1) (upaco4_2_1 gf_0 gf_1 r_0 r_1) <4== paco4_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_4.
  eapply le1_trans; [| apply _paco_2_0_fold]. apply le1_refl.
Qed.

Theorem _paco4_2_1_fold: forall r_0 r_1,
  gf_1 (upaco4_2_0 gf_0 gf_1 r_0 r_1) (upaco4_2_1 gf_0 gf_1 r_0 r_1) <4== paco4_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_4.
  eapply le1_trans; [| apply _paco_2_1_fold]. apply le1_refl.
Qed.

Theorem _paco4_2_0_unfold: forall (MON: _monotone4_2 gf_0) (MON: _monotone4_2 gf_1) r_0 r_1,
  paco4_2_0 gf_0 gf_1 r_0 r_1 <4== gf_0 (upaco4_2_0 gf_0 gf_1 r_0 r_1) (upaco4_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  intros. apply curry_adjoint2_4.
  eapply _paco_2_0_unfold; apply monotone4_2_map; assumption.
Qed.

Theorem _paco4_2_1_unfold: forall (MON: _monotone4_2 gf_0) (MON: _monotone4_2 gf_1) r_0 r_1,
  paco4_2_1 gf_0 gf_1 r_0 r_1 <4== gf_1 (upaco4_2_0 gf_0 gf_1 r_0 r_1) (upaco4_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  intros. apply curry_adjoint2_4.
  eapply _paco_2_1_unfold; apply monotone4_2_map; assumption.
Qed.

Theorem paco4_2_0_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_0 <4= rr) (CIH: l <4= rr), l <4= paco4_2_0 gf_0 gf_1 rr r_1),
  l <4= paco4_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco4_2_0_acc.
Qed.

Theorem paco4_2_1_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_1 <4= rr) (CIH: l <4= rr), l <4= paco4_2_1 gf_0 gf_1 r_0 rr),
  l <4= paco4_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco4_2_1_acc.
Qed.

Theorem paco4_2_0_mon: monotone4_2 (paco4_2_0 gf_0 gf_1).
Proof.
  apply monotone4_2_eq.
  apply _paco4_2_0_mon.
Qed.

Theorem paco4_2_1_mon: monotone4_2 (paco4_2_1 gf_0 gf_1).
Proof.
  apply monotone4_2_eq.
  apply _paco4_2_1_mon.
Qed.

Theorem paco4_2_0_mult_strong: forall r_0 r_1,
  paco4_2_0 gf_0 gf_1 (upaco4_2_0 gf_0 gf_1 r_0 r_1) (upaco4_2_1 gf_0 gf_1 r_0 r_1) <4= paco4_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco4_2_0_mult_strong.
Qed.

Theorem paco4_2_1_mult_strong: forall r_0 r_1,
  paco4_2_1 gf_0 gf_1 (upaco4_2_0 gf_0 gf_1 r_0 r_1) (upaco4_2_1 gf_0 gf_1 r_0 r_1) <4= paco4_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco4_2_1_mult_strong.
Qed.

Corollary paco4_2_0_mult: forall r_0 r_1,
  paco4_2_0 gf_0 gf_1 (paco4_2_0 gf_0 gf_1 r_0 r_1) (paco4_2_1 gf_0 gf_1 r_0 r_1) <4= paco4_2_0 gf_0 gf_1 r_0 r_1.
Proof. intros; eapply paco4_2_0_mult_strong, paco4_2_0_mon; [apply PR|..]; intros; left; assumption. Qed.

Corollary paco4_2_1_mult: forall r_0 r_1,
  paco4_2_1 gf_0 gf_1 (paco4_2_0 gf_0 gf_1 r_0 r_1) (paco4_2_1 gf_0 gf_1 r_0 r_1) <4= paco4_2_1 gf_0 gf_1 r_0 r_1.
Proof. intros; eapply paco4_2_1_mult_strong, paco4_2_1_mon; [apply PR|..]; intros; left; assumption. Qed.

Theorem paco4_2_0_fold: forall r_0 r_1,
  gf_0 (upaco4_2_0 gf_0 gf_1 r_0 r_1) (upaco4_2_1 gf_0 gf_1 r_0 r_1) <4= paco4_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco4_2_0_fold.
Qed.

Theorem paco4_2_1_fold: forall r_0 r_1,
  gf_1 (upaco4_2_0 gf_0 gf_1 r_0 r_1) (upaco4_2_1 gf_0 gf_1 r_0 r_1) <4= paco4_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco4_2_1_fold.
Qed.

Theorem paco4_2_0_unfold: forall (MON: monotone4_2 gf_0) (MON: monotone4_2 gf_1) r_0 r_1,
  paco4_2_0 gf_0 gf_1 r_0 r_1 <4= gf_0 (upaco4_2_0 gf_0 gf_1 r_0 r_1) (upaco4_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  repeat_intros 2. eapply _paco4_2_0_unfold; apply monotone4_2_eq; assumption.
Qed.

Theorem paco4_2_1_unfold: forall (MON: monotone4_2 gf_0) (MON: monotone4_2 gf_1) r_0 r_1,
  paco4_2_1 gf_0 gf_1 r_0 r_1 <4= gf_1 (upaco4_2_0 gf_0 gf_1 r_0 r_1) (upaco4_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  repeat_intros 2. eapply _paco4_2_1_unfold; apply monotone4_2_eq; assumption.
Qed.

End Arg4_2.

Arguments paco4_2_0_acc : clear implicits.
Arguments paco4_2_1_acc : clear implicits.
Arguments paco4_2_0_mon : clear implicits.
Arguments paco4_2_1_mon : clear implicits.
Arguments paco4_2_0_mult_strong : clear implicits.
Arguments paco4_2_1_mult_strong : clear implicits.
Arguments paco4_2_0_mult : clear implicits.
Arguments paco4_2_1_mult : clear implicits.
Arguments paco4_2_0_fold : clear implicits.
Arguments paco4_2_1_fold : clear implicits.
Arguments paco4_2_0_unfold : clear implicits.
Arguments paco4_2_1_unfold : clear implicits.

Global Instance paco4_2_0_inst  (gf_0 gf_1 : rel4 T0 T1 T2 T3->_) r_0 r_1 x0 x1 x2 x3 : paco_class (paco4_2_0 gf_0 gf_1 r_0 r_1 x0 x1 x2 x3) :=
{ pacoacc    := paco4_2_0_acc gf_0 gf_1;
  pacomult   := paco4_2_0_mult gf_0 gf_1;
  pacofold   := paco4_2_0_fold gf_0 gf_1;
  pacounfold := paco4_2_0_unfold gf_0 gf_1 }.

Global Instance paco4_2_1_inst  (gf_0 gf_1 : rel4 T0 T1 T2 T3->_) r_0 r_1 x0 x1 x2 x3 : paco_class (paco4_2_1 gf_0 gf_1 r_0 r_1 x0 x1 x2 x3) :=
{ pacoacc    := paco4_2_1_acc gf_0 gf_1;
  pacomult   := paco4_2_1_mult gf_0 gf_1;
  pacofold   := paco4_2_1_fold gf_0 gf_1;
  pacounfold := paco4_2_1_unfold gf_0 gf_1 }.

(** 3 Mutual Coinduction *)

Section Arg4_3.

Definition monotone4_3 (gf: rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3) :=
  forall x0 x1 x2 x3 r_0 r_1 r_2 r'_0 r'_1 r'_2 (IN: gf r_0 r_1 r_2 x0 x1 x2 x3) (LE_0: r_0 <4= r'_0)(LE_1: r_1 <4= r'_1)(LE_2: r_2 <4= r'_2), gf r'_0 r'_1 r'_2 x0 x1 x2 x3.

Definition _monotone4_3 (gf: rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3) :=
  forall r_0 r_1 r_2 r'_0 r'_1 r'_2(LE_0: r_0 <4= r'_0)(LE_1: r_1 <4= r'_1)(LE_2: r_2 <4= r'_2), gf r_0 r_1 r_2 <4== gf r'_0 r'_1 r'_2.

Lemma monotone4_3_eq (gf: rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3) :
  monotone4_3 gf <-> _monotone4_3 gf.
Proof. unfold monotone4_3, _monotone4_3, le4. split; intros; eapply H; eassumption. Qed.

Lemma monotone4_3_map (gf: rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3)
      (MON: _monotone4_3 gf) :
  _monotone_3 (fun R0 R1 R2 => uncurry4 (gf (curry4 R0) (curry4 R1) (curry4 R2))).
Proof.
  repeat_intros 9. apply uncurry_map4. apply MON; apply curry_map4; assumption.
Qed.

Variable gf_0 gf_1 gf_2 : rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.
Arguments gf_2 : clear implicits.

Theorem _paco4_3_0_mon: _monotone4_3 (paco4_3_0 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 9. eapply curry_map4, _paco_3_0_mon; apply uncurry_map4; assumption.
Qed.

Theorem _paco4_3_1_mon: _monotone4_3 (paco4_3_1 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 9. eapply curry_map4, _paco_3_1_mon; apply uncurry_map4; assumption.
Qed.

Theorem _paco4_3_2_mon: _monotone4_3 (paco4_3_2 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 9. eapply curry_map4, _paco_3_2_mon; apply uncurry_map4; assumption.
Qed.

Theorem _paco4_3_0_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_0 <4== rr) (CIH: l <4== rr), l <4== paco4_3_0 gf_0 gf_1 gf_2 rr r_1 r_2),
  l <4== paco4_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_4.
  eapply _paco_3_0_acc. intros.
  apply uncurry_adjoint1_4 in INC. apply uncurry_adjoint1_4 in CIH.
  apply uncurry_adjoint2_4.
  eapply le4_trans. eapply (OBG _ INC CIH).
  apply curry_map4.
  apply _paco_3_0_mon; try apply le1_refl; apply curry_bij1_4.
Qed.

Theorem _paco4_3_1_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_1 <4== rr) (CIH: l <4== rr), l <4== paco4_3_1 gf_0 gf_1 gf_2 r_0 rr r_2),
  l <4== paco4_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_4.
  eapply _paco_3_1_acc. intros.
  apply uncurry_adjoint1_4 in INC. apply uncurry_adjoint1_4 in CIH.
  apply uncurry_adjoint2_4.
  eapply le4_trans. eapply (OBG _ INC CIH).
  apply curry_map4.
  apply _paco_3_1_mon; try apply le1_refl; apply curry_bij1_4.
Qed.

Theorem _paco4_3_2_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_2 <4== rr) (CIH: l <4== rr), l <4== paco4_3_2 gf_0 gf_1 gf_2 r_0 r_1 rr),
  l <4== paco4_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_4.
  eapply _paco_3_2_acc. intros.
  apply uncurry_adjoint1_4 in INC. apply uncurry_adjoint1_4 in CIH.
  apply uncurry_adjoint2_4.
  eapply le4_trans. eapply (OBG _ INC CIH).
  apply curry_map4.
  apply _paco_3_2_mon; try apply le1_refl; apply curry_bij1_4.
Qed.

Theorem _paco4_3_0_mult_strong: forall r_0 r_1 r_2,
  paco4_3_0 gf_0 gf_1 gf_2 (upaco4_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco4_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco4_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <4== paco4_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply curry_map4.
  eapply le1_trans; [| eapply _paco_3_0_mult_strong].
  apply _paco_3_0_mon; intros []; intros H; apply H.
Qed.

Theorem _paco4_3_1_mult_strong: forall r_0 r_1 r_2,
  paco4_3_1 gf_0 gf_1 gf_2 (upaco4_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco4_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco4_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <4== paco4_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply curry_map4.
  eapply le1_trans; [| eapply _paco_3_1_mult_strong].
  apply _paco_3_1_mon; intros []; intros H; apply H.
Qed.

Theorem _paco4_3_2_mult_strong: forall r_0 r_1 r_2,
  paco4_3_2 gf_0 gf_1 gf_2 (upaco4_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco4_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco4_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <4== paco4_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply curry_map4.
  eapply le1_trans; [| eapply _paco_3_2_mult_strong].
  apply _paco_3_2_mon; intros []; intros H; apply H.
Qed.

Theorem _paco4_3_0_fold: forall r_0 r_1 r_2,
  gf_0 (upaco4_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco4_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco4_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <4== paco4_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_4.
  eapply le1_trans; [| apply _paco_3_0_fold]. apply le1_refl.
Qed.

Theorem _paco4_3_1_fold: forall r_0 r_1 r_2,
  gf_1 (upaco4_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco4_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco4_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <4== paco4_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_4.
  eapply le1_trans; [| apply _paco_3_1_fold]. apply le1_refl.
Qed.

Theorem _paco4_3_2_fold: forall r_0 r_1 r_2,
  gf_2 (upaco4_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco4_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco4_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <4== paco4_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_4.
  eapply le1_trans; [| apply _paco_3_2_fold]. apply le1_refl.
Qed.

Theorem _paco4_3_0_unfold: forall (MON: _monotone4_3 gf_0) (MON: _monotone4_3 gf_1) (MON: _monotone4_3 gf_2) r_0 r_1 r_2,
  paco4_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 <4== gf_0 (upaco4_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco4_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco4_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  intros. apply curry_adjoint2_4.
  eapply _paco_3_0_unfold; apply monotone4_3_map; assumption.
Qed.

Theorem _paco4_3_1_unfold: forall (MON: _monotone4_3 gf_0) (MON: _monotone4_3 gf_1) (MON: _monotone4_3 gf_2) r_0 r_1 r_2,
  paco4_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 <4== gf_1 (upaco4_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco4_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco4_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  intros. apply curry_adjoint2_4.
  eapply _paco_3_1_unfold; apply monotone4_3_map; assumption.
Qed.

Theorem _paco4_3_2_unfold: forall (MON: _monotone4_3 gf_0) (MON: _monotone4_3 gf_1) (MON: _monotone4_3 gf_2) r_0 r_1 r_2,
  paco4_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 <4== gf_2 (upaco4_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco4_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco4_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  intros. apply curry_adjoint2_4.
  eapply _paco_3_2_unfold; apply monotone4_3_map; assumption.
Qed.

Theorem paco4_3_0_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_0 <4= rr) (CIH: l <4= rr), l <4= paco4_3_0 gf_0 gf_1 gf_2 rr r_1 r_2),
  l <4= paco4_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco4_3_0_acc.
Qed.

Theorem paco4_3_1_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_1 <4= rr) (CIH: l <4= rr), l <4= paco4_3_1 gf_0 gf_1 gf_2 r_0 rr r_2),
  l <4= paco4_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco4_3_1_acc.
Qed.

Theorem paco4_3_2_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_2 <4= rr) (CIH: l <4= rr), l <4= paco4_3_2 gf_0 gf_1 gf_2 r_0 r_1 rr),
  l <4= paco4_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco4_3_2_acc.
Qed.

Theorem paco4_3_0_mon: monotone4_3 (paco4_3_0 gf_0 gf_1 gf_2).
Proof.
  apply monotone4_3_eq.
  apply _paco4_3_0_mon.
Qed.

Theorem paco4_3_1_mon: monotone4_3 (paco4_3_1 gf_0 gf_1 gf_2).
Proof.
  apply monotone4_3_eq.
  apply _paco4_3_1_mon.
Qed.

Theorem paco4_3_2_mon: monotone4_3 (paco4_3_2 gf_0 gf_1 gf_2).
Proof.
  apply monotone4_3_eq.
  apply _paco4_3_2_mon.
Qed.

Theorem paco4_3_0_mult_strong: forall r_0 r_1 r_2,
  paco4_3_0 gf_0 gf_1 gf_2 (upaco4_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco4_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco4_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <4= paco4_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco4_3_0_mult_strong.
Qed.

Theorem paco4_3_1_mult_strong: forall r_0 r_1 r_2,
  paco4_3_1 gf_0 gf_1 gf_2 (upaco4_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco4_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco4_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <4= paco4_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco4_3_1_mult_strong.
Qed.

Theorem paco4_3_2_mult_strong: forall r_0 r_1 r_2,
  paco4_3_2 gf_0 gf_1 gf_2 (upaco4_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco4_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco4_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <4= paco4_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco4_3_2_mult_strong.
Qed.

Corollary paco4_3_0_mult: forall r_0 r_1 r_2,
  paco4_3_0 gf_0 gf_1 gf_2 (paco4_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco4_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco4_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <4= paco4_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco4_3_0_mult_strong, paco4_3_0_mon; [apply PR|..]; intros; left; assumption. Qed.

Corollary paco4_3_1_mult: forall r_0 r_1 r_2,
  paco4_3_1 gf_0 gf_1 gf_2 (paco4_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco4_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco4_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <4= paco4_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco4_3_1_mult_strong, paco4_3_1_mon; [apply PR|..]; intros; left; assumption. Qed.

Corollary paco4_3_2_mult: forall r_0 r_1 r_2,
  paco4_3_2 gf_0 gf_1 gf_2 (paco4_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco4_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco4_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <4= paco4_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco4_3_2_mult_strong, paco4_3_2_mon; [apply PR|..]; intros; left; assumption. Qed.

Theorem paco4_3_0_fold: forall r_0 r_1 r_2,
  gf_0 (upaco4_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco4_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco4_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <4= paco4_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco4_3_0_fold.
Qed.

Theorem paco4_3_1_fold: forall r_0 r_1 r_2,
  gf_1 (upaco4_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco4_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco4_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <4= paco4_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco4_3_1_fold.
Qed.

Theorem paco4_3_2_fold: forall r_0 r_1 r_2,
  gf_2 (upaco4_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco4_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco4_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <4= paco4_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco4_3_2_fold.
Qed.

Theorem paco4_3_0_unfold: forall (MON: monotone4_3 gf_0) (MON: monotone4_3 gf_1) (MON: monotone4_3 gf_2) r_0 r_1 r_2,
  paco4_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 <4= gf_0 (upaco4_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco4_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco4_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  repeat_intros 3. eapply _paco4_3_0_unfold; apply monotone4_3_eq; assumption.
Qed.

Theorem paco4_3_1_unfold: forall (MON: monotone4_3 gf_0) (MON: monotone4_3 gf_1) (MON: monotone4_3 gf_2) r_0 r_1 r_2,
  paco4_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 <4= gf_1 (upaco4_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco4_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco4_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  repeat_intros 3. eapply _paco4_3_1_unfold; apply monotone4_3_eq; assumption.
Qed.

Theorem paco4_3_2_unfold: forall (MON: monotone4_3 gf_0) (MON: monotone4_3 gf_1) (MON: monotone4_3 gf_2) r_0 r_1 r_2,
  paco4_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 <4= gf_2 (upaco4_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco4_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco4_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  repeat_intros 3. eapply _paco4_3_2_unfold; apply monotone4_3_eq; assumption.
Qed.

End Arg4_3.

Arguments paco4_3_0_acc : clear implicits.
Arguments paco4_3_1_acc : clear implicits.
Arguments paco4_3_2_acc : clear implicits.
Arguments paco4_3_0_mon : clear implicits.
Arguments paco4_3_1_mon : clear implicits.
Arguments paco4_3_2_mon : clear implicits.
Arguments paco4_3_0_mult_strong : clear implicits.
Arguments paco4_3_1_mult_strong : clear implicits.
Arguments paco4_3_2_mult_strong : clear implicits.
Arguments paco4_3_0_mult : clear implicits.
Arguments paco4_3_1_mult : clear implicits.
Arguments paco4_3_2_mult : clear implicits.
Arguments paco4_3_0_fold : clear implicits.
Arguments paco4_3_1_fold : clear implicits.
Arguments paco4_3_2_fold : clear implicits.
Arguments paco4_3_0_unfold : clear implicits.
Arguments paco4_3_1_unfold : clear implicits.
Arguments paco4_3_2_unfold : clear implicits.

Global Instance paco4_3_0_inst  (gf_0 gf_1 gf_2 : rel4 T0 T1 T2 T3->_) r_0 r_1 r_2 x0 x1 x2 x3 : paco_class (paco4_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3) :=
{ pacoacc    := paco4_3_0_acc gf_0 gf_1 gf_2;
  pacomult   := paco4_3_0_mult gf_0 gf_1 gf_2;
  pacofold   := paco4_3_0_fold gf_0 gf_1 gf_2;
  pacounfold := paco4_3_0_unfold gf_0 gf_1 gf_2 }.

Global Instance paco4_3_1_inst  (gf_0 gf_1 gf_2 : rel4 T0 T1 T2 T3->_) r_0 r_1 r_2 x0 x1 x2 x3 : paco_class (paco4_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3) :=
{ pacoacc    := paco4_3_1_acc gf_0 gf_1 gf_2;
  pacomult   := paco4_3_1_mult gf_0 gf_1 gf_2;
  pacofold   := paco4_3_1_fold gf_0 gf_1 gf_2;
  pacounfold := paco4_3_1_unfold gf_0 gf_1 gf_2 }.

Global Instance paco4_3_2_inst  (gf_0 gf_1 gf_2 : rel4 T0 T1 T2 T3->_) r_0 r_1 r_2 x0 x1 x2 x3 : paco_class (paco4_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3) :=
{ pacoacc    := paco4_3_2_acc gf_0 gf_1 gf_2;
  pacomult   := paco4_3_2_mult gf_0 gf_1 gf_2;
  pacofold   := paco4_3_2_fold gf_0 gf_1 gf_2;
  pacounfold := paco4_3_2_unfold gf_0 gf_1 gf_2 }.

End PACO4.

Global Opaque paco4.

Hint Unfold upaco4.
Hint Resolve paco4_fold.
Hint Unfold monotone4.

Global Opaque paco4_2_0.
Global Opaque paco4_2_1.

Hint Unfold upaco4_2_0.
Hint Unfold upaco4_2_1.
Hint Resolve paco4_2_0_fold.
Hint Resolve paco4_2_1_fold.
Hint Unfold monotone4_2.

Global Opaque paco4_3_0.
Global Opaque paco4_3_1.
Global Opaque paco4_3_2.

Hint Unfold upaco4_3_0.
Hint Unfold upaco4_3_1.
Hint Unfold upaco4_3_2.
Hint Resolve paco4_3_0_fold.
Hint Resolve paco4_3_1_fold.
Hint Resolve paco4_3_2_fold.
Hint Unfold monotone4_3.

