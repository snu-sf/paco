Require Export paconotation pacotacuser.
Require Import paconotation_internal pacotac pacon.
Set Implicit Arguments.

Section PACO3.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.

Record sig3T :=
  exist3T { 
      proj3T0: @T0;
      proj3T1: @T1 proj3T0;
      proj3T2: @T2 proj3T0 proj3T1;
    }.

Definition uncurry3 (R: rel3 T0 T1 T2): rel1 sig3T := fun x => R (proj3T0 x) (proj3T1 x) (proj3T2 x).

Definition curry3 (R: rel1 sig3T): rel3 T0 T1 T2 :=
  fun x0 x1 x2 => R (exist3T x2).

Lemma uncurry_map3 r0 r1 (LE : r0 <3== r1) : uncurry3 r0 <1== uncurry3 r1.
Proof. intros [] H. apply LE. apply H. Qed.

Lemma uncurry_map_rev3 r0 r1 (LE: uncurry3 r0 <1== uncurry3 r1) : r0 <3== r1.
Proof.
  repeat_intros 3. intros H. apply (LE (exist3T x2) H).
Qed.

Lemma curry_map3 r0 r1 (LE: r0 <1== r1) : curry3 r0 <3== curry3 r1.
Proof. 
  repeat_intros 3. intros H. apply (LE (exist3T x2) H).
Qed.

Lemma curry_map_rev3 r0 r1 (LE: curry3 r0 <3== curry3 r1) : r0 <1== r1.
Proof. 
  intros [] H. apply LE. apply H.
Qed.

Lemma uncurry_bij1_3 r : curry3 (uncurry3 r) <3== r.
Proof. unfold le3. repeat_intros 3. intros H. apply H. Qed.

Lemma uncurry_bij2_3 r : r <3== curry3 (uncurry3 r).
Proof. unfold le3. repeat_intros 3. intros H. apply H. Qed.

Lemma curry_bij1_3 r : uncurry3 (curry3 r) <1== r.
Proof. intros []. intro H. apply H. Qed.

Lemma curry_bij2_3 r : r <1== uncurry3 (curry3 r).
Proof. intros []. intro H. apply H. Qed.

Lemma uncurry_adjoint1_3 r0 r1 (LE: uncurry3 r0 <1== r1) : r0 <3== curry3 r1.
Proof.
  apply uncurry_map_rev3. eapply le1_trans; [apply LE|]. apply curry_bij2_3.
Qed.

Lemma uncurry_adjoint2_3 r0 r1 (LE: r0 <3== curry3 r1) : uncurry3 r0 <1== r1.
Proof.
  apply curry_map_rev3. eapply le3_trans; [|apply LE]. apply uncurry_bij2_3.
Qed.

Lemma curry_adjoint1_3 r0 r1 (LE: curry3 r0 <3== r1) : r0 <1== uncurry3 r1.
Proof.
  apply curry_map_rev3. eapply le3_trans; [apply LE|]. apply uncurry_bij2_3.
Qed.

Lemma curry_adjoint2_3 r0 r1 (LE: r0 <1== uncurry3 r1) : curry3 r0 <3== r1.
Proof.
  apply uncurry_map_rev3. eapply le1_trans; [|apply LE]. apply curry_bij1_3.
Qed.

(** ** Predicates of Arity 3
*)

Section Arg3_def.
Variable gf : rel3 T0 T1 T2 -> rel3 T0 T1 T2.
Arguments gf : clear implicits.

Definition paco3( r: rel3 T0 T1 T2) : rel3 T0 T1 T2 :=
  curry3 (paco (fun R0 => uncurry3 (gf (curry3 R0))) (uncurry3 r)).

Definition upaco3( r: rel3 T0 T1 T2) := paco3 r \3/ r.
End Arg3_def.
Arguments paco3 : clear implicits.
Arguments upaco3 : clear implicits.
Hint Unfold upaco3.

Section Arg3_2_def.
Variable gf_0 gf_1 : rel3 T0 T1 T2 -> rel3 T0 T1 T2 -> rel3 T0 T1 T2.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.

Definition paco3_2_0( r_0 r_1: rel3 T0 T1 T2) : rel3 T0 T1 T2 :=
  curry3 (paco_2_0 (fun R0 R1 => uncurry3 (gf_0 (curry3 R0) (curry3 R1))) (fun R0 R1 => uncurry3 (gf_1 (curry3 R0) (curry3 R1))) (uncurry3 r_0) (uncurry3 r_1)).

Definition paco3_2_1( r_0 r_1: rel3 T0 T1 T2) : rel3 T0 T1 T2 :=
  curry3 (paco_2_1 (fun R0 R1 => uncurry3 (gf_0 (curry3 R0) (curry3 R1))) (fun R0 R1 => uncurry3 (gf_1 (curry3 R0) (curry3 R1))) (uncurry3 r_0) (uncurry3 r_1)).

Definition upaco3_2_0( r_0 r_1: rel3 T0 T1 T2) := paco3_2_0 r_0 r_1 \3/ r_0.
Definition upaco3_2_1( r_0 r_1: rel3 T0 T1 T2) := paco3_2_1 r_0 r_1 \3/ r_1.
End Arg3_2_def.
Arguments paco3_2_0 : clear implicits.
Arguments upaco3_2_0 : clear implicits.
Hint Unfold upaco3_2_0.
Arguments paco3_2_1 : clear implicits.
Arguments upaco3_2_1 : clear implicits.
Hint Unfold upaco3_2_1.

Section Arg3_3_def.
Variable gf_0 gf_1 gf_2 : rel3 T0 T1 T2 -> rel3 T0 T1 T2 -> rel3 T0 T1 T2 -> rel3 T0 T1 T2.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.
Arguments gf_2 : clear implicits.

Definition paco3_3_0( r_0 r_1 r_2: rel3 T0 T1 T2) : rel3 T0 T1 T2 :=
  curry3 (paco_3_0 (fun R0 R1 R2 => uncurry3 (gf_0 (curry3 R0) (curry3 R1) (curry3 R2))) (fun R0 R1 R2 => uncurry3 (gf_1 (curry3 R0) (curry3 R1) (curry3 R2))) (fun R0 R1 R2 => uncurry3 (gf_2 (curry3 R0) (curry3 R1) (curry3 R2))) (uncurry3 r_0) (uncurry3 r_1) (uncurry3 r_2)).

Definition paco3_3_1( r_0 r_1 r_2: rel3 T0 T1 T2) : rel3 T0 T1 T2 :=
  curry3 (paco_3_1 (fun R0 R1 R2 => uncurry3 (gf_0 (curry3 R0) (curry3 R1) (curry3 R2))) (fun R0 R1 R2 => uncurry3 (gf_1 (curry3 R0) (curry3 R1) (curry3 R2))) (fun R0 R1 R2 => uncurry3 (gf_2 (curry3 R0) (curry3 R1) (curry3 R2))) (uncurry3 r_0) (uncurry3 r_1) (uncurry3 r_2)).

Definition paco3_3_2( r_0 r_1 r_2: rel3 T0 T1 T2) : rel3 T0 T1 T2 :=
  curry3 (paco_3_2 (fun R0 R1 R2 => uncurry3 (gf_0 (curry3 R0) (curry3 R1) (curry3 R2))) (fun R0 R1 R2 => uncurry3 (gf_1 (curry3 R0) (curry3 R1) (curry3 R2))) (fun R0 R1 R2 => uncurry3 (gf_2 (curry3 R0) (curry3 R1) (curry3 R2))) (uncurry3 r_0) (uncurry3 r_1) (uncurry3 r_2)).

Definition upaco3_3_0( r_0 r_1 r_2: rel3 T0 T1 T2) := paco3_3_0 r_0 r_1 r_2 \3/ r_0.
Definition upaco3_3_1( r_0 r_1 r_2: rel3 T0 T1 T2) := paco3_3_1 r_0 r_1 r_2 \3/ r_1.
Definition upaco3_3_2( r_0 r_1 r_2: rel3 T0 T1 T2) := paco3_3_2 r_0 r_1 r_2 \3/ r_2.
End Arg3_3_def.
Arguments paco3_3_0 : clear implicits.
Arguments upaco3_3_0 : clear implicits.
Hint Unfold upaco3_3_0.
Arguments paco3_3_1 : clear implicits.
Arguments upaco3_3_1 : clear implicits.
Hint Unfold upaco3_3_1.
Arguments paco3_3_2 : clear implicits.
Arguments upaco3_3_2 : clear implicits.
Hint Unfold upaco3_3_2.

(** 1 Mutual Coinduction *)

Section Arg3_1.

Definition monotone3 (gf: rel3 T0 T1 T2 -> rel3 T0 T1 T2) :=
  forall x0 x1 x2 r r' (IN: gf r x0 x1 x2) (LE: r <3= r'), gf r' x0 x1 x2.

Definition _monotone3 (gf: rel3 T0 T1 T2 -> rel3 T0 T1 T2) :=
  forall r r'(LE: r <3= r'), gf r <3== gf r'.

Lemma monotone3_eq (gf: rel3 T0 T1 T2 -> rel3 T0 T1 T2) :
  monotone3 gf <-> _monotone3 gf.
Proof. unfold monotone3, _monotone3, le3. split; intros; eapply H; eassumption. Qed.

Lemma monotone3_map (gf: rel3 T0 T1 T2 -> rel3 T0 T1 T2)
      (MON: _monotone3 gf) :
  _monotone (fun R0 => uncurry3 (gf (curry3 R0))).
Proof.
  repeat_intros 3. apply uncurry_map3. apply MON; apply curry_map3; assumption.
Qed.

Variable gf : rel3 T0 T1 T2 -> rel3 T0 T1 T2.
Arguments gf : clear implicits.

Theorem _paco3_mon: _monotone3 (paco3 gf).
Proof.
  repeat_intros 3. eapply curry_map3, _paco_mon; apply uncurry_map3; assumption.
Qed.

Theorem _paco3_acc: forall
  l r (OBG: forall rr (INC: r <3== rr) (CIH: l <3== rr), l <3== paco3 gf rr),
  l <3== paco3 gf r.
Proof.
  intros. apply uncurry_adjoint1_3.
  eapply _paco_acc. intros.
  apply uncurry_adjoint1_3 in INC. apply uncurry_adjoint1_3 in CIH.
  apply uncurry_adjoint2_3.
  eapply le3_trans. eapply (OBG _ INC CIH).
  apply curry_map3.
  apply _paco_mon; try apply le1_refl; apply curry_bij1_3.
Qed.

Theorem _paco3_mult_strong: forall r,
  paco3 gf (upaco3 gf r) <3== paco3 gf r.
Proof.
  intros. apply curry_map3.
  eapply le1_trans; [| eapply _paco_mult_strong].
  apply _paco_mon; intros []; intros H; apply H.
Qed.

Theorem _paco3_fold: forall r,
  gf (upaco3 gf r) <3== paco3 gf r.
Proof.
  intros. apply uncurry_adjoint1_3.
  eapply le1_trans; [| apply _paco_fold]. apply le1_refl.
Qed.

Theorem _paco3_unfold: forall (MON: _monotone3 gf) r,
  paco3 gf r <3== gf (upaco3 gf r).
Proof.
  intros. apply curry_adjoint2_3.
  eapply _paco_unfold; apply monotone3_map; assumption.
Qed.

Theorem paco3_acc: forall
  l r (OBG: forall rr (INC: r <3= rr) (CIH: l <3= rr), l <3= paco3 gf rr),
  l <3= paco3 gf r.
Proof.
  apply _paco3_acc.
Qed.

Theorem paco3_mon: monotone3 (paco3 gf).
Proof.
  apply monotone3_eq.
  apply _paco3_mon.
Qed.

Theorem upaco3_mon: monotone3 (upaco3 gf).
Proof.
  repeat_intros 5. intros R  LE0.
  destruct R.
  - left. eapply paco3_mon. apply H. apply LE0.
  - right. apply LE0, H.
Qed.
Theorem paco3_mult_strong: forall r,
  paco3 gf (upaco3 gf r) <3= paco3 gf r.
Proof.
  apply _paco3_mult_strong.
Qed.

Corollary paco3_mult: forall r,
  paco3 gf (paco3 gf r) <3= paco3 gf r.
Proof. intros; eapply paco3_mult_strong, paco3_mon; [apply PR|..]; intros; left; assumption. Qed.

Theorem paco3_fold: forall r,
  gf (upaco3 gf r) <3= paco3 gf r.
Proof.
  apply _paco3_fold.
Qed.

Theorem paco3_unfold: forall (MON: monotone3 gf) r,
  paco3 gf r <3= gf (upaco3 gf r).
Proof.
  repeat_intros 1. eapply _paco3_unfold; apply monotone3_eq; assumption.
Qed.

End Arg3_1.

Arguments paco3_acc : clear implicits.
Arguments paco3_mon : clear implicits.
Arguments upaco3_mon : clear implicits.
Arguments paco3_mult_strong : clear implicits.
Arguments paco3_mult : clear implicits.
Arguments paco3_fold : clear implicits.
Arguments paco3_unfold : clear implicits.

Global Instance paco3_inst  (gf : rel3 T0 T1 T2->_) r x0 x1 x2 : paco_class (paco3 gf r x0 x1 x2) :=
{ pacoacc    := paco3_acc gf;
  pacomult   := paco3_mult gf;
  pacofold   := paco3_fold gf;
  pacounfold := paco3_unfold gf }.

(** 2 Mutual Coinduction *)

Section Arg3_2.

Definition monotone3_2 (gf: rel3 T0 T1 T2 -> rel3 T0 T1 T2 -> rel3 T0 T1 T2) :=
  forall x0 x1 x2 r_0 r_1 r'_0 r'_1 (IN: gf r_0 r_1 x0 x1 x2) (LE_0: r_0 <3= r'_0)(LE_1: r_1 <3= r'_1), gf r'_0 r'_1 x0 x1 x2.

Definition _monotone3_2 (gf: rel3 T0 T1 T2 -> rel3 T0 T1 T2 -> rel3 T0 T1 T2) :=
  forall r_0 r_1 r'_0 r'_1(LE_0: r_0 <3= r'_0)(LE_1: r_1 <3= r'_1), gf r_0 r_1 <3== gf r'_0 r'_1.

Lemma monotone3_2_eq (gf: rel3 T0 T1 T2 -> rel3 T0 T1 T2 -> rel3 T0 T1 T2) :
  monotone3_2 gf <-> _monotone3_2 gf.
Proof. unfold monotone3_2, _monotone3_2, le3. split; intros; eapply H; eassumption. Qed.

Lemma monotone3_2_map (gf: rel3 T0 T1 T2 -> rel3 T0 T1 T2 -> rel3 T0 T1 T2)
      (MON: _monotone3_2 gf) :
  _monotone_2 (fun R0 R1 => uncurry3 (gf (curry3 R0) (curry3 R1))).
Proof.
  repeat_intros 6. apply uncurry_map3. apply MON; apply curry_map3; assumption.
Qed.

Variable gf_0 gf_1 : rel3 T0 T1 T2 -> rel3 T0 T1 T2 -> rel3 T0 T1 T2.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.

Theorem _paco3_2_0_mon: _monotone3_2 (paco3_2_0 gf_0 gf_1).
Proof.
  repeat_intros 6. eapply curry_map3, _paco_2_0_mon; apply uncurry_map3; assumption.
Qed.

Theorem _paco3_2_1_mon: _monotone3_2 (paco3_2_1 gf_0 gf_1).
Proof.
  repeat_intros 6. eapply curry_map3, _paco_2_1_mon; apply uncurry_map3; assumption.
Qed.

Theorem _paco3_2_0_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_0 <3== rr) (CIH: l <3== rr), l <3== paco3_2_0 gf_0 gf_1 rr r_1),
  l <3== paco3_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_3.
  eapply _paco_2_0_acc. intros.
  apply uncurry_adjoint1_3 in INC. apply uncurry_adjoint1_3 in CIH.
  apply uncurry_adjoint2_3.
  eapply le3_trans. eapply (OBG _ INC CIH).
  apply curry_map3.
  apply _paco_2_0_mon; try apply le1_refl; apply curry_bij1_3.
Qed.

Theorem _paco3_2_1_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_1 <3== rr) (CIH: l <3== rr), l <3== paco3_2_1 gf_0 gf_1 r_0 rr),
  l <3== paco3_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_3.
  eapply _paco_2_1_acc. intros.
  apply uncurry_adjoint1_3 in INC. apply uncurry_adjoint1_3 in CIH.
  apply uncurry_adjoint2_3.
  eapply le3_trans. eapply (OBG _ INC CIH).
  apply curry_map3.
  apply _paco_2_1_mon; try apply le1_refl; apply curry_bij1_3.
Qed.

Theorem _paco3_2_0_mult_strong: forall r_0 r_1,
  paco3_2_0 gf_0 gf_1 (upaco3_2_0 gf_0 gf_1 r_0 r_1) (upaco3_2_1 gf_0 gf_1 r_0 r_1) <3== paco3_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply curry_map3.
  eapply le1_trans; [| eapply _paco_2_0_mult_strong].
  apply _paco_2_0_mon; intros []; intros H; apply H.
Qed.

Theorem _paco3_2_1_mult_strong: forall r_0 r_1,
  paco3_2_1 gf_0 gf_1 (upaco3_2_0 gf_0 gf_1 r_0 r_1) (upaco3_2_1 gf_0 gf_1 r_0 r_1) <3== paco3_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply curry_map3.
  eapply le1_trans; [| eapply _paco_2_1_mult_strong].
  apply _paco_2_1_mon; intros []; intros H; apply H.
Qed.

Theorem _paco3_2_0_fold: forall r_0 r_1,
  gf_0 (upaco3_2_0 gf_0 gf_1 r_0 r_1) (upaco3_2_1 gf_0 gf_1 r_0 r_1) <3== paco3_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_3.
  eapply le1_trans; [| apply _paco_2_0_fold]. apply le1_refl.
Qed.

Theorem _paco3_2_1_fold: forall r_0 r_1,
  gf_1 (upaco3_2_0 gf_0 gf_1 r_0 r_1) (upaco3_2_1 gf_0 gf_1 r_0 r_1) <3== paco3_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_3.
  eapply le1_trans; [| apply _paco_2_1_fold]. apply le1_refl.
Qed.

Theorem _paco3_2_0_unfold: forall (MON: _monotone3_2 gf_0) (MON: _monotone3_2 gf_1) r_0 r_1,
  paco3_2_0 gf_0 gf_1 r_0 r_1 <3== gf_0 (upaco3_2_0 gf_0 gf_1 r_0 r_1) (upaco3_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  intros. apply curry_adjoint2_3.
  eapply _paco_2_0_unfold; apply monotone3_2_map; assumption.
Qed.

Theorem _paco3_2_1_unfold: forall (MON: _monotone3_2 gf_0) (MON: _monotone3_2 gf_1) r_0 r_1,
  paco3_2_1 gf_0 gf_1 r_0 r_1 <3== gf_1 (upaco3_2_0 gf_0 gf_1 r_0 r_1) (upaco3_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  intros. apply curry_adjoint2_3.
  eapply _paco_2_1_unfold; apply monotone3_2_map; assumption.
Qed.

Theorem paco3_2_0_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_0 <3= rr) (CIH: l <3= rr), l <3= paco3_2_0 gf_0 gf_1 rr r_1),
  l <3= paco3_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco3_2_0_acc.
Qed.

Theorem paco3_2_1_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_1 <3= rr) (CIH: l <3= rr), l <3= paco3_2_1 gf_0 gf_1 r_0 rr),
  l <3= paco3_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco3_2_1_acc.
Qed.

Theorem paco3_2_0_mon: monotone3_2 (paco3_2_0 gf_0 gf_1).
Proof.
  apply monotone3_2_eq.
  apply _paco3_2_0_mon.
Qed.

Theorem paco3_2_1_mon: monotone3_2 (paco3_2_1 gf_0 gf_1).
Proof.
  apply monotone3_2_eq.
  apply _paco3_2_1_mon.
Qed.

Theorem upaco3_2_0_mon: monotone3_2 (upaco3_2_0 gf_0 gf_1).
Proof.
  repeat_intros 7. intros R  LE0 LE1.
  destruct R.
  - left. eapply paco3_2_0_mon. apply H. apply LE0. apply LE1.
  - right. apply LE0, H.
Qed.
Theorem upaco3_2_1_mon: monotone3_2 (upaco3_2_1 gf_0 gf_1).
Proof.
  repeat_intros 7. intros R  LE0 LE1.
  destruct R.
  - left. eapply paco3_2_1_mon. apply H. apply LE0. apply LE1.
  - right. apply LE1, H.
Qed.
Theorem paco3_2_0_mult_strong: forall r_0 r_1,
  paco3_2_0 gf_0 gf_1 (upaco3_2_0 gf_0 gf_1 r_0 r_1) (upaco3_2_1 gf_0 gf_1 r_0 r_1) <3= paco3_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco3_2_0_mult_strong.
Qed.

Theorem paco3_2_1_mult_strong: forall r_0 r_1,
  paco3_2_1 gf_0 gf_1 (upaco3_2_0 gf_0 gf_1 r_0 r_1) (upaco3_2_1 gf_0 gf_1 r_0 r_1) <3= paco3_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco3_2_1_mult_strong.
Qed.

Corollary paco3_2_0_mult: forall r_0 r_1,
  paco3_2_0 gf_0 gf_1 (paco3_2_0 gf_0 gf_1 r_0 r_1) (paco3_2_1 gf_0 gf_1 r_0 r_1) <3= paco3_2_0 gf_0 gf_1 r_0 r_1.
Proof. intros; eapply paco3_2_0_mult_strong, paco3_2_0_mon; [apply PR|..]; intros; left; assumption. Qed.

Corollary paco3_2_1_mult: forall r_0 r_1,
  paco3_2_1 gf_0 gf_1 (paco3_2_0 gf_0 gf_1 r_0 r_1) (paco3_2_1 gf_0 gf_1 r_0 r_1) <3= paco3_2_1 gf_0 gf_1 r_0 r_1.
Proof. intros; eapply paco3_2_1_mult_strong, paco3_2_1_mon; [apply PR|..]; intros; left; assumption. Qed.

Theorem paco3_2_0_fold: forall r_0 r_1,
  gf_0 (upaco3_2_0 gf_0 gf_1 r_0 r_1) (upaco3_2_1 gf_0 gf_1 r_0 r_1) <3= paco3_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco3_2_0_fold.
Qed.

Theorem paco3_2_1_fold: forall r_0 r_1,
  gf_1 (upaco3_2_0 gf_0 gf_1 r_0 r_1) (upaco3_2_1 gf_0 gf_1 r_0 r_1) <3= paco3_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco3_2_1_fold.
Qed.

Theorem paco3_2_0_unfold: forall (MON: monotone3_2 gf_0) (MON: monotone3_2 gf_1) r_0 r_1,
  paco3_2_0 gf_0 gf_1 r_0 r_1 <3= gf_0 (upaco3_2_0 gf_0 gf_1 r_0 r_1) (upaco3_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  repeat_intros 2. eapply _paco3_2_0_unfold; apply monotone3_2_eq; assumption.
Qed.

Theorem paco3_2_1_unfold: forall (MON: monotone3_2 gf_0) (MON: monotone3_2 gf_1) r_0 r_1,
  paco3_2_1 gf_0 gf_1 r_0 r_1 <3= gf_1 (upaco3_2_0 gf_0 gf_1 r_0 r_1) (upaco3_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  repeat_intros 2. eapply _paco3_2_1_unfold; apply monotone3_2_eq; assumption.
Qed.

End Arg3_2.

Arguments paco3_2_0_acc : clear implicits.
Arguments paco3_2_1_acc : clear implicits.
Arguments paco3_2_0_mon : clear implicits.
Arguments paco3_2_1_mon : clear implicits.
Arguments upaco3_2_0_mon : clear implicits.
Arguments upaco3_2_1_mon : clear implicits.
Arguments paco3_2_0_mult_strong : clear implicits.
Arguments paco3_2_1_mult_strong : clear implicits.
Arguments paco3_2_0_mult : clear implicits.
Arguments paco3_2_1_mult : clear implicits.
Arguments paco3_2_0_fold : clear implicits.
Arguments paco3_2_1_fold : clear implicits.
Arguments paco3_2_0_unfold : clear implicits.
Arguments paco3_2_1_unfold : clear implicits.

Global Instance paco3_2_0_inst  (gf_0 gf_1 : rel3 T0 T1 T2->_) r_0 r_1 x0 x1 x2 : paco_class (paco3_2_0 gf_0 gf_1 r_0 r_1 x0 x1 x2) :=
{ pacoacc    := paco3_2_0_acc gf_0 gf_1;
  pacomult   := paco3_2_0_mult gf_0 gf_1;
  pacofold   := paco3_2_0_fold gf_0 gf_1;
  pacounfold := paco3_2_0_unfold gf_0 gf_1 }.

Global Instance paco3_2_1_inst  (gf_0 gf_1 : rel3 T0 T1 T2->_) r_0 r_1 x0 x1 x2 : paco_class (paco3_2_1 gf_0 gf_1 r_0 r_1 x0 x1 x2) :=
{ pacoacc    := paco3_2_1_acc gf_0 gf_1;
  pacomult   := paco3_2_1_mult gf_0 gf_1;
  pacofold   := paco3_2_1_fold gf_0 gf_1;
  pacounfold := paco3_2_1_unfold gf_0 gf_1 }.

(** 3 Mutual Coinduction *)

Section Arg3_3.

Definition monotone3_3 (gf: rel3 T0 T1 T2 -> rel3 T0 T1 T2 -> rel3 T0 T1 T2 -> rel3 T0 T1 T2) :=
  forall x0 x1 x2 r_0 r_1 r_2 r'_0 r'_1 r'_2 (IN: gf r_0 r_1 r_2 x0 x1 x2) (LE_0: r_0 <3= r'_0)(LE_1: r_1 <3= r'_1)(LE_2: r_2 <3= r'_2), gf r'_0 r'_1 r'_2 x0 x1 x2.

Definition _monotone3_3 (gf: rel3 T0 T1 T2 -> rel3 T0 T1 T2 -> rel3 T0 T1 T2 -> rel3 T0 T1 T2) :=
  forall r_0 r_1 r_2 r'_0 r'_1 r'_2(LE_0: r_0 <3= r'_0)(LE_1: r_1 <3= r'_1)(LE_2: r_2 <3= r'_2), gf r_0 r_1 r_2 <3== gf r'_0 r'_1 r'_2.

Lemma monotone3_3_eq (gf: rel3 T0 T1 T2 -> rel3 T0 T1 T2 -> rel3 T0 T1 T2 -> rel3 T0 T1 T2) :
  monotone3_3 gf <-> _monotone3_3 gf.
Proof. unfold monotone3_3, _monotone3_3, le3. split; intros; eapply H; eassumption. Qed.

Lemma monotone3_3_map (gf: rel3 T0 T1 T2 -> rel3 T0 T1 T2 -> rel3 T0 T1 T2 -> rel3 T0 T1 T2)
      (MON: _monotone3_3 gf) :
  _monotone_3 (fun R0 R1 R2 => uncurry3 (gf (curry3 R0) (curry3 R1) (curry3 R2))).
Proof.
  repeat_intros 9. apply uncurry_map3. apply MON; apply curry_map3; assumption.
Qed.

Variable gf_0 gf_1 gf_2 : rel3 T0 T1 T2 -> rel3 T0 T1 T2 -> rel3 T0 T1 T2 -> rel3 T0 T1 T2.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.
Arguments gf_2 : clear implicits.

Theorem _paco3_3_0_mon: _monotone3_3 (paco3_3_0 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 9. eapply curry_map3, _paco_3_0_mon; apply uncurry_map3; assumption.
Qed.

Theorem _paco3_3_1_mon: _monotone3_3 (paco3_3_1 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 9. eapply curry_map3, _paco_3_1_mon; apply uncurry_map3; assumption.
Qed.

Theorem _paco3_3_2_mon: _monotone3_3 (paco3_3_2 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 9. eapply curry_map3, _paco_3_2_mon; apply uncurry_map3; assumption.
Qed.

Theorem _paco3_3_0_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_0 <3== rr) (CIH: l <3== rr), l <3== paco3_3_0 gf_0 gf_1 gf_2 rr r_1 r_2),
  l <3== paco3_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_3.
  eapply _paco_3_0_acc. intros.
  apply uncurry_adjoint1_3 in INC. apply uncurry_adjoint1_3 in CIH.
  apply uncurry_adjoint2_3.
  eapply le3_trans. eapply (OBG _ INC CIH).
  apply curry_map3.
  apply _paco_3_0_mon; try apply le1_refl; apply curry_bij1_3.
Qed.

Theorem _paco3_3_1_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_1 <3== rr) (CIH: l <3== rr), l <3== paco3_3_1 gf_0 gf_1 gf_2 r_0 rr r_2),
  l <3== paco3_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_3.
  eapply _paco_3_1_acc. intros.
  apply uncurry_adjoint1_3 in INC. apply uncurry_adjoint1_3 in CIH.
  apply uncurry_adjoint2_3.
  eapply le3_trans. eapply (OBG _ INC CIH).
  apply curry_map3.
  apply _paco_3_1_mon; try apply le1_refl; apply curry_bij1_3.
Qed.

Theorem _paco3_3_2_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_2 <3== rr) (CIH: l <3== rr), l <3== paco3_3_2 gf_0 gf_1 gf_2 r_0 r_1 rr),
  l <3== paco3_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_3.
  eapply _paco_3_2_acc. intros.
  apply uncurry_adjoint1_3 in INC. apply uncurry_adjoint1_3 in CIH.
  apply uncurry_adjoint2_3.
  eapply le3_trans. eapply (OBG _ INC CIH).
  apply curry_map3.
  apply _paco_3_2_mon; try apply le1_refl; apply curry_bij1_3.
Qed.

Theorem _paco3_3_0_mult_strong: forall r_0 r_1 r_2,
  paco3_3_0 gf_0 gf_1 gf_2 (upaco3_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco3_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco3_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <3== paco3_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply curry_map3.
  eapply le1_trans; [| eapply _paco_3_0_mult_strong].
  apply _paco_3_0_mon; intros []; intros H; apply H.
Qed.

Theorem _paco3_3_1_mult_strong: forall r_0 r_1 r_2,
  paco3_3_1 gf_0 gf_1 gf_2 (upaco3_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco3_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco3_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <3== paco3_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply curry_map3.
  eapply le1_trans; [| eapply _paco_3_1_mult_strong].
  apply _paco_3_1_mon; intros []; intros H; apply H.
Qed.

Theorem _paco3_3_2_mult_strong: forall r_0 r_1 r_2,
  paco3_3_2 gf_0 gf_1 gf_2 (upaco3_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco3_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco3_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <3== paco3_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply curry_map3.
  eapply le1_trans; [| eapply _paco_3_2_mult_strong].
  apply _paco_3_2_mon; intros []; intros H; apply H.
Qed.

Theorem _paco3_3_0_fold: forall r_0 r_1 r_2,
  gf_0 (upaco3_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco3_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco3_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <3== paco3_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_3.
  eapply le1_trans; [| apply _paco_3_0_fold]. apply le1_refl.
Qed.

Theorem _paco3_3_1_fold: forall r_0 r_1 r_2,
  gf_1 (upaco3_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco3_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco3_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <3== paco3_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_3.
  eapply le1_trans; [| apply _paco_3_1_fold]. apply le1_refl.
Qed.

Theorem _paco3_3_2_fold: forall r_0 r_1 r_2,
  gf_2 (upaco3_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco3_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco3_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <3== paco3_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_3.
  eapply le1_trans; [| apply _paco_3_2_fold]. apply le1_refl.
Qed.

Theorem _paco3_3_0_unfold: forall (MON: _monotone3_3 gf_0) (MON: _monotone3_3 gf_1) (MON: _monotone3_3 gf_2) r_0 r_1 r_2,
  paco3_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 <3== gf_0 (upaco3_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco3_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco3_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  intros. apply curry_adjoint2_3.
  eapply _paco_3_0_unfold; apply monotone3_3_map; assumption.
Qed.

Theorem _paco3_3_1_unfold: forall (MON: _monotone3_3 gf_0) (MON: _monotone3_3 gf_1) (MON: _monotone3_3 gf_2) r_0 r_1 r_2,
  paco3_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 <3== gf_1 (upaco3_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco3_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco3_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  intros. apply curry_adjoint2_3.
  eapply _paco_3_1_unfold; apply monotone3_3_map; assumption.
Qed.

Theorem _paco3_3_2_unfold: forall (MON: _monotone3_3 gf_0) (MON: _monotone3_3 gf_1) (MON: _monotone3_3 gf_2) r_0 r_1 r_2,
  paco3_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 <3== gf_2 (upaco3_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco3_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco3_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  intros. apply curry_adjoint2_3.
  eapply _paco_3_2_unfold; apply monotone3_3_map; assumption.
Qed.

Theorem paco3_3_0_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_0 <3= rr) (CIH: l <3= rr), l <3= paco3_3_0 gf_0 gf_1 gf_2 rr r_1 r_2),
  l <3= paco3_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco3_3_0_acc.
Qed.

Theorem paco3_3_1_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_1 <3= rr) (CIH: l <3= rr), l <3= paco3_3_1 gf_0 gf_1 gf_2 r_0 rr r_2),
  l <3= paco3_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco3_3_1_acc.
Qed.

Theorem paco3_3_2_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_2 <3= rr) (CIH: l <3= rr), l <3= paco3_3_2 gf_0 gf_1 gf_2 r_0 r_1 rr),
  l <3= paco3_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco3_3_2_acc.
Qed.

Theorem paco3_3_0_mon: monotone3_3 (paco3_3_0 gf_0 gf_1 gf_2).
Proof.
  apply monotone3_3_eq.
  apply _paco3_3_0_mon.
Qed.

Theorem paco3_3_1_mon: monotone3_3 (paco3_3_1 gf_0 gf_1 gf_2).
Proof.
  apply monotone3_3_eq.
  apply _paco3_3_1_mon.
Qed.

Theorem paco3_3_2_mon: monotone3_3 (paco3_3_2 gf_0 gf_1 gf_2).
Proof.
  apply monotone3_3_eq.
  apply _paco3_3_2_mon.
Qed.

Theorem upaco3_3_0_mon: monotone3_3 (upaco3_3_0 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 9. intros R  LE0 LE1 LE2.
  destruct R.
  - left. eapply paco3_3_0_mon. apply H. apply LE0. apply LE1. apply LE2.
  - right. apply LE0, H.
Qed.
Theorem upaco3_3_1_mon: monotone3_3 (upaco3_3_1 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 9. intros R  LE0 LE1 LE2.
  destruct R.
  - left. eapply paco3_3_1_mon. apply H. apply LE0. apply LE1. apply LE2.
  - right. apply LE1, H.
Qed.
Theorem upaco3_3_2_mon: monotone3_3 (upaco3_3_2 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 9. intros R  LE0 LE1 LE2.
  destruct R.
  - left. eapply paco3_3_2_mon. apply H. apply LE0. apply LE1. apply LE2.
  - right. apply LE2, H.
Qed.
Theorem paco3_3_0_mult_strong: forall r_0 r_1 r_2,
  paco3_3_0 gf_0 gf_1 gf_2 (upaco3_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco3_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco3_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <3= paco3_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco3_3_0_mult_strong.
Qed.

Theorem paco3_3_1_mult_strong: forall r_0 r_1 r_2,
  paco3_3_1 gf_0 gf_1 gf_2 (upaco3_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco3_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco3_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <3= paco3_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco3_3_1_mult_strong.
Qed.

Theorem paco3_3_2_mult_strong: forall r_0 r_1 r_2,
  paco3_3_2 gf_0 gf_1 gf_2 (upaco3_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco3_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco3_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <3= paco3_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco3_3_2_mult_strong.
Qed.

Corollary paco3_3_0_mult: forall r_0 r_1 r_2,
  paco3_3_0 gf_0 gf_1 gf_2 (paco3_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco3_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco3_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <3= paco3_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco3_3_0_mult_strong, paco3_3_0_mon; [apply PR|..]; intros; left; assumption. Qed.

Corollary paco3_3_1_mult: forall r_0 r_1 r_2,
  paco3_3_1 gf_0 gf_1 gf_2 (paco3_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco3_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco3_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <3= paco3_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco3_3_1_mult_strong, paco3_3_1_mon; [apply PR|..]; intros; left; assumption. Qed.

Corollary paco3_3_2_mult: forall r_0 r_1 r_2,
  paco3_3_2 gf_0 gf_1 gf_2 (paco3_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco3_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco3_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <3= paco3_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco3_3_2_mult_strong, paco3_3_2_mon; [apply PR|..]; intros; left; assumption. Qed.

Theorem paco3_3_0_fold: forall r_0 r_1 r_2,
  gf_0 (upaco3_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco3_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco3_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <3= paco3_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco3_3_0_fold.
Qed.

Theorem paco3_3_1_fold: forall r_0 r_1 r_2,
  gf_1 (upaco3_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco3_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco3_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <3= paco3_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco3_3_1_fold.
Qed.

Theorem paco3_3_2_fold: forall r_0 r_1 r_2,
  gf_2 (upaco3_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco3_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco3_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <3= paco3_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco3_3_2_fold.
Qed.

Theorem paco3_3_0_unfold: forall (MON: monotone3_3 gf_0) (MON: monotone3_3 gf_1) (MON: monotone3_3 gf_2) r_0 r_1 r_2,
  paco3_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 <3= gf_0 (upaco3_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco3_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco3_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  repeat_intros 3. eapply _paco3_3_0_unfold; apply monotone3_3_eq; assumption.
Qed.

Theorem paco3_3_1_unfold: forall (MON: monotone3_3 gf_0) (MON: monotone3_3 gf_1) (MON: monotone3_3 gf_2) r_0 r_1 r_2,
  paco3_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 <3= gf_1 (upaco3_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco3_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco3_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  repeat_intros 3. eapply _paco3_3_1_unfold; apply monotone3_3_eq; assumption.
Qed.

Theorem paco3_3_2_unfold: forall (MON: monotone3_3 gf_0) (MON: monotone3_3 gf_1) (MON: monotone3_3 gf_2) r_0 r_1 r_2,
  paco3_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 <3= gf_2 (upaco3_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco3_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco3_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  repeat_intros 3. eapply _paco3_3_2_unfold; apply monotone3_3_eq; assumption.
Qed.

End Arg3_3.

Arguments paco3_3_0_acc : clear implicits.
Arguments paco3_3_1_acc : clear implicits.
Arguments paco3_3_2_acc : clear implicits.
Arguments paco3_3_0_mon : clear implicits.
Arguments paco3_3_1_mon : clear implicits.
Arguments paco3_3_2_mon : clear implicits.
Arguments upaco3_3_0_mon : clear implicits.
Arguments upaco3_3_1_mon : clear implicits.
Arguments upaco3_3_2_mon : clear implicits.
Arguments paco3_3_0_mult_strong : clear implicits.
Arguments paco3_3_1_mult_strong : clear implicits.
Arguments paco3_3_2_mult_strong : clear implicits.
Arguments paco3_3_0_mult : clear implicits.
Arguments paco3_3_1_mult : clear implicits.
Arguments paco3_3_2_mult : clear implicits.
Arguments paco3_3_0_fold : clear implicits.
Arguments paco3_3_1_fold : clear implicits.
Arguments paco3_3_2_fold : clear implicits.
Arguments paco3_3_0_unfold : clear implicits.
Arguments paco3_3_1_unfold : clear implicits.
Arguments paco3_3_2_unfold : clear implicits.

Global Instance paco3_3_0_inst  (gf_0 gf_1 gf_2 : rel3 T0 T1 T2->_) r_0 r_1 r_2 x0 x1 x2 : paco_class (paco3_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2) :=
{ pacoacc    := paco3_3_0_acc gf_0 gf_1 gf_2;
  pacomult   := paco3_3_0_mult gf_0 gf_1 gf_2;
  pacofold   := paco3_3_0_fold gf_0 gf_1 gf_2;
  pacounfold := paco3_3_0_unfold gf_0 gf_1 gf_2 }.

Global Instance paco3_3_1_inst  (gf_0 gf_1 gf_2 : rel3 T0 T1 T2->_) r_0 r_1 r_2 x0 x1 x2 : paco_class (paco3_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2) :=
{ pacoacc    := paco3_3_1_acc gf_0 gf_1 gf_2;
  pacomult   := paco3_3_1_mult gf_0 gf_1 gf_2;
  pacofold   := paco3_3_1_fold gf_0 gf_1 gf_2;
  pacounfold := paco3_3_1_unfold gf_0 gf_1 gf_2 }.

Global Instance paco3_3_2_inst  (gf_0 gf_1 gf_2 : rel3 T0 T1 T2->_) r_0 r_1 r_2 x0 x1 x2 : paco_class (paco3_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2) :=
{ pacoacc    := paco3_3_2_acc gf_0 gf_1 gf_2;
  pacomult   := paco3_3_2_mult gf_0 gf_1 gf_2;
  pacofold   := paco3_3_2_fold gf_0 gf_1 gf_2;
  pacounfold := paco3_3_2_unfold gf_0 gf_1 gf_2 }.

End PACO3.

Global Opaque paco3.

Hint Unfold upaco3.
Hint Resolve paco3_fold.
Hint Unfold monotone3.

Global Opaque paco3_2_0.
Global Opaque paco3_2_1.

Hint Unfold upaco3_2_0.
Hint Unfold upaco3_2_1.
Hint Resolve paco3_2_0_fold.
Hint Resolve paco3_2_1_fold.
Hint Unfold monotone3_2.

Global Opaque paco3_3_0.
Global Opaque paco3_3_1.
Global Opaque paco3_3_2.

Hint Unfold upaco3_3_0.
Hint Unfold upaco3_3_1.
Hint Unfold upaco3_3_2.
Hint Resolve paco3_3_0_fold.
Hint Resolve paco3_3_1_fold.
Hint Resolve paco3_3_2_fold.
Hint Unfold monotone3_3.

