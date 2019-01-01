Require Export paconotation pacotacuser.
Require Import paconotation_internal pacotac pacon.
Set Implicit Arguments.

Section PACO0.


Record sig0T :=
  exist0T { 
    }.

Definition uncurry0 (R: rel0): rel1 sig0T := fun x => R.

Definition curry0 (R: rel1 sig0T): rel0 :=
  R (exist0T).

Lemma uncurry_map0 r0 r1 (LE : r0 <0== r1) : uncurry0 r0 <1== uncurry0 r1.
Proof. intros [] H. apply LE. apply H. Qed.

Lemma uncurry_map_rev0 r0 r1 (LE: uncurry0 r0 <1== uncurry0 r1) : r0 <0== r1.
Proof.
  repeat_intros 0. intros H. apply (LE (exist0T) H).
Qed.

Lemma curry_map0 r0 r1 (LE: r0 <1== r1) : curry0 r0 <0== curry0 r1.
Proof. 
  repeat_intros 0. intros H. apply (LE (exist0T) H).
Qed.

Lemma curry_map_rev0 r0 r1 (LE: curry0 r0 <0== curry0 r1) : r0 <1== r1.
Proof. 
  intros [] H. apply LE. apply H.
Qed.

Lemma uncurry_bij1_0 r : curry0 (uncurry0 r) <0== r.
Proof. unfold le0. repeat_intros 0. intros H. apply H. Qed.

Lemma uncurry_bij2_0 r : r <0== curry0 (uncurry0 r).
Proof. unfold le0. repeat_intros 0. intros H. apply H. Qed.

Lemma curry_bij1_0 r : uncurry0 (curry0 r) <1== r.
Proof. intros []. intro H. apply H. Qed.

Lemma curry_bij2_0 r : r <1== uncurry0 (curry0 r).
Proof. intros []. intro H. apply H. Qed.

Lemma uncurry_adjoint1_0 r0 r1 (LE: uncurry0 r0 <1== r1) : r0 <0== curry0 r1.
Proof.
  apply uncurry_map_rev0. eapply le1_trans; [apply LE|]. apply curry_bij2_0.
Qed.

Lemma uncurry_adjoint2_0 r0 r1 (LE: r0 <0== curry0 r1) : uncurry0 r0 <1== r1.
Proof.
  apply curry_map_rev0. eapply le0_trans; [|apply LE]. apply uncurry_bij2_0.
Qed.

Lemma curry_adjoint1_0 r0 r1 (LE: curry0 r0 <0== r1) : r0 <1== uncurry0 r1.
Proof.
  apply curry_map_rev0. eapply le0_trans; [apply LE|]. apply uncurry_bij2_0.
Qed.

Lemma curry_adjoint2_0 r0 r1 (LE: r0 <1== uncurry0 r1) : curry0 r0 <0== r1.
Proof.
  apply uncurry_map_rev0. eapply le1_trans; [|apply LE]. apply curry_bij1_0.
Qed.

(** ** Predicates of Arity 0
*)

Section Arg0_def.
Variable gf : rel0 -> rel0.
Arguments gf : clear implicits.

Definition paco0( r: rel0) : rel0 :=
  curry0 (paco (fun R0 => uncurry0 (gf (curry0 R0))) (uncurry0 r)).

Definition upaco0( r: rel0) := paco0 r \0/ r.
End Arg0_def.
Arguments paco0 : clear implicits.
Arguments upaco0 : clear implicits.
Hint Unfold upaco0.

Section Arg0_2_def.
Variable gf_0 gf_1 : rel0 -> rel0 -> rel0.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.

Definition paco0_2_0( r_0 r_1: rel0) : rel0 :=
  curry0 (paco_2_0 (fun R0 R1 => uncurry0 (gf_0 (curry0 R0) (curry0 R1))) (fun R0 R1 => uncurry0 (gf_1 (curry0 R0) (curry0 R1))) (uncurry0 r_0) (uncurry0 r_1)).

Definition paco0_2_1( r_0 r_1: rel0) : rel0 :=
  curry0 (paco_2_1 (fun R0 R1 => uncurry0 (gf_0 (curry0 R0) (curry0 R1))) (fun R0 R1 => uncurry0 (gf_1 (curry0 R0) (curry0 R1))) (uncurry0 r_0) (uncurry0 r_1)).

Definition upaco0_2_0( r_0 r_1: rel0) := paco0_2_0 r_0 r_1 \0/ r_0.
Definition upaco0_2_1( r_0 r_1: rel0) := paco0_2_1 r_0 r_1 \0/ r_1.
End Arg0_2_def.
Arguments paco0_2_0 : clear implicits.
Arguments upaco0_2_0 : clear implicits.
Hint Unfold upaco0_2_0.
Arguments paco0_2_1 : clear implicits.
Arguments upaco0_2_1 : clear implicits.
Hint Unfold upaco0_2_1.

Section Arg0_3_def.
Variable gf_0 gf_1 gf_2 : rel0 -> rel0 -> rel0 -> rel0.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.
Arguments gf_2 : clear implicits.

Definition paco0_3_0( r_0 r_1 r_2: rel0) : rel0 :=
  curry0 (paco_3_0 (fun R0 R1 R2 => uncurry0 (gf_0 (curry0 R0) (curry0 R1) (curry0 R2))) (fun R0 R1 R2 => uncurry0 (gf_1 (curry0 R0) (curry0 R1) (curry0 R2))) (fun R0 R1 R2 => uncurry0 (gf_2 (curry0 R0) (curry0 R1) (curry0 R2))) (uncurry0 r_0) (uncurry0 r_1) (uncurry0 r_2)).

Definition paco0_3_1( r_0 r_1 r_2: rel0) : rel0 :=
  curry0 (paco_3_1 (fun R0 R1 R2 => uncurry0 (gf_0 (curry0 R0) (curry0 R1) (curry0 R2))) (fun R0 R1 R2 => uncurry0 (gf_1 (curry0 R0) (curry0 R1) (curry0 R2))) (fun R0 R1 R2 => uncurry0 (gf_2 (curry0 R0) (curry0 R1) (curry0 R2))) (uncurry0 r_0) (uncurry0 r_1) (uncurry0 r_2)).

Definition paco0_3_2( r_0 r_1 r_2: rel0) : rel0 :=
  curry0 (paco_3_2 (fun R0 R1 R2 => uncurry0 (gf_0 (curry0 R0) (curry0 R1) (curry0 R2))) (fun R0 R1 R2 => uncurry0 (gf_1 (curry0 R0) (curry0 R1) (curry0 R2))) (fun R0 R1 R2 => uncurry0 (gf_2 (curry0 R0) (curry0 R1) (curry0 R2))) (uncurry0 r_0) (uncurry0 r_1) (uncurry0 r_2)).

Definition upaco0_3_0( r_0 r_1 r_2: rel0) := paco0_3_0 r_0 r_1 r_2 \0/ r_0.
Definition upaco0_3_1( r_0 r_1 r_2: rel0) := paco0_3_1 r_0 r_1 r_2 \0/ r_1.
Definition upaco0_3_2( r_0 r_1 r_2: rel0) := paco0_3_2 r_0 r_1 r_2 \0/ r_2.
End Arg0_3_def.
Arguments paco0_3_0 : clear implicits.
Arguments upaco0_3_0 : clear implicits.
Hint Unfold upaco0_3_0.
Arguments paco0_3_1 : clear implicits.
Arguments upaco0_3_1 : clear implicits.
Hint Unfold upaco0_3_1.
Arguments paco0_3_2 : clear implicits.
Arguments upaco0_3_2 : clear implicits.
Hint Unfold upaco0_3_2.

(** 1 Mutual Coinduction *)

Section Arg0_1.

Definition monotone0 (gf: rel0 -> rel0) :=
  forall r r' (IN: gf r) (LE: r <0= r'), gf r'.

Definition _monotone0 (gf: rel0 -> rel0) :=
  forall r r'(LE: r <0= r'), gf r <0== gf r'.

Lemma monotone0_eq (gf: rel0 -> rel0) :
  monotone0 gf <-> _monotone0 gf.
Proof. unfold monotone0, _monotone0, le0. split; intros; eapply H; eassumption. Qed.

Lemma monotone0_map (gf: rel0 -> rel0)
      (MON: _monotone0 gf) :
  _monotone (fun R0 => uncurry0 (gf (curry0 R0))).
Proof.
  repeat_intros 3. apply uncurry_map0. apply MON; apply curry_map0; assumption.
Qed.

Variable gf : rel0 -> rel0.
Arguments gf : clear implicits.

Theorem _paco0_mon: _monotone0 (paco0 gf).
Proof.
  repeat_intros 3. eapply curry_map0, _paco_mon; apply uncurry_map0; assumption.
Qed.

Theorem _paco0_acc: forall
  l r (OBG: forall rr (INC: r <0== rr) (CIH: l <0== rr), l <0== paco0 gf rr),
  l <0== paco0 gf r.
Proof.
  intros. apply uncurry_adjoint1_0.
  eapply _paco_acc. intros.
  apply uncurry_adjoint1_0 in INC. apply uncurry_adjoint1_0 in CIH.
  apply uncurry_adjoint2_0.
  eapply le0_trans. eapply (OBG _ INC CIH).
  apply curry_map0.
  apply _paco_mon; try apply le1_refl; apply curry_bij1_0.
Qed.

Theorem _paco0_mult_strong: forall r,
  paco0 gf (upaco0 gf r) <0== paco0 gf r.
Proof.
  intros. apply curry_map0.
  eapply le1_trans; [| eapply _paco_mult_strong].
  apply _paco_mon; intros []; intros H; apply H.
Qed.

Theorem _paco0_fold: forall r,
  gf (upaco0 gf r) <0== paco0 gf r.
Proof.
  intros. apply uncurry_adjoint1_0.
  eapply le1_trans; [| apply _paco_fold]. apply le1_refl.
Qed.

Theorem _paco0_unfold: forall (MON: _monotone0 gf) r,
  paco0 gf r <0== gf (upaco0 gf r).
Proof.
  intros. apply curry_adjoint2_0.
  eapply _paco_unfold; apply monotone0_map; assumption.
Qed.

Theorem paco0_acc: forall
  l r (OBG: forall rr (INC: r <0= rr) (CIH: l <0= rr), l <0= paco0 gf rr),
  l <0= paco0 gf r.
Proof.
  apply _paco0_acc.
Qed.

Theorem paco0_mon: monotone0 (paco0 gf).
Proof.
  apply monotone0_eq.
  apply _paco0_mon.
Qed.

Theorem upaco0_mon: monotone0 (upaco0 gf).
Proof.
  repeat_intros 2. intros R  LE0.
  destruct R.
  - left. eapply paco0_mon. apply H. apply LE0.
  - right. apply LE0, H.
Qed.
Theorem paco0_mult_strong: forall r,
  paco0 gf (upaco0 gf r) <0= paco0 gf r.
Proof.
  apply _paco0_mult_strong.
Qed.

Corollary paco0_mult: forall r,
  paco0 gf (paco0 gf r) <0= paco0 gf r.
Proof. intros; eapply paco0_mult_strong, paco0_mon; [apply PR|..]; intros; left; assumption. Qed.

Theorem paco0_fold: forall r,
  gf (upaco0 gf r) <0= paco0 gf r.
Proof.
  apply _paco0_fold.
Qed.

Theorem paco0_unfold: forall (MON: monotone0 gf) r,
  paco0 gf r <0= gf (upaco0 gf r).
Proof.
  repeat_intros 1. eapply _paco0_unfold; apply monotone0_eq; assumption.
Qed.

End Arg0_1.

Arguments paco0_acc : clear implicits.
Arguments paco0_mon : clear implicits.
Arguments upaco0_mon : clear implicits.
Arguments paco0_mult_strong : clear implicits.
Arguments paco0_mult : clear implicits.
Arguments paco0_fold : clear implicits.
Arguments paco0_unfold : clear implicits.

Global Instance paco0_inst  (gf : rel0->_) r : paco_class (paco0 gf r) :=
{ pacoacc    := paco0_acc gf;
  pacomult   := paco0_mult gf;
  pacofold   := paco0_fold gf;
  pacounfold := paco0_unfold gf }.

(** 2 Mutual Coinduction *)

Section Arg0_2.

Definition monotone0_2 (gf: rel0 -> rel0 -> rel0) :=
  forall r_0 r_1 r'_0 r'_1 (IN: gf r_0 r_1) (LE_0: r_0 <0= r'_0)(LE_1: r_1 <0= r'_1), gf r'_0 r'_1.

Definition _monotone0_2 (gf: rel0 -> rel0 -> rel0) :=
  forall r_0 r_1 r'_0 r'_1(LE_0: r_0 <0= r'_0)(LE_1: r_1 <0= r'_1), gf r_0 r_1 <0== gf r'_0 r'_1.

Lemma monotone0_2_eq (gf: rel0 -> rel0 -> rel0) :
  monotone0_2 gf <-> _monotone0_2 gf.
Proof. unfold monotone0_2, _monotone0_2, le0. split; intros; eapply H; eassumption. Qed.

Lemma monotone0_2_map (gf: rel0 -> rel0 -> rel0)
      (MON: _monotone0_2 gf) :
  _monotone_2 (fun R0 R1 => uncurry0 (gf (curry0 R0) (curry0 R1))).
Proof.
  repeat_intros 6. apply uncurry_map0. apply MON; apply curry_map0; assumption.
Qed.

Variable gf_0 gf_1 : rel0 -> rel0 -> rel0.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.

Theorem _paco0_2_0_mon: _monotone0_2 (paco0_2_0 gf_0 gf_1).
Proof.
  repeat_intros 6. eapply curry_map0, _paco_2_0_mon; apply uncurry_map0; assumption.
Qed.

Theorem _paco0_2_1_mon: _monotone0_2 (paco0_2_1 gf_0 gf_1).
Proof.
  repeat_intros 6. eapply curry_map0, _paco_2_1_mon; apply uncurry_map0; assumption.
Qed.

Theorem _paco0_2_0_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_0 <0== rr) (CIH: l <0== rr), l <0== paco0_2_0 gf_0 gf_1 rr r_1),
  l <0== paco0_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_0.
  eapply _paco_2_0_acc. intros.
  apply uncurry_adjoint1_0 in INC. apply uncurry_adjoint1_0 in CIH.
  apply uncurry_adjoint2_0.
  eapply le0_trans. eapply (OBG _ INC CIH).
  apply curry_map0.
  apply _paco_2_0_mon; try apply le1_refl; apply curry_bij1_0.
Qed.

Theorem _paco0_2_1_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_1 <0== rr) (CIH: l <0== rr), l <0== paco0_2_1 gf_0 gf_1 r_0 rr),
  l <0== paco0_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_0.
  eapply _paco_2_1_acc. intros.
  apply uncurry_adjoint1_0 in INC. apply uncurry_adjoint1_0 in CIH.
  apply uncurry_adjoint2_0.
  eapply le0_trans. eapply (OBG _ INC CIH).
  apply curry_map0.
  apply _paco_2_1_mon; try apply le1_refl; apply curry_bij1_0.
Qed.

Theorem _paco0_2_0_mult_strong: forall r_0 r_1,
  paco0_2_0 gf_0 gf_1 (upaco0_2_0 gf_0 gf_1 r_0 r_1) (upaco0_2_1 gf_0 gf_1 r_0 r_1) <0== paco0_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply curry_map0.
  eapply le1_trans; [| eapply _paco_2_0_mult_strong].
  apply _paco_2_0_mon; intros []; intros H; apply H.
Qed.

Theorem _paco0_2_1_mult_strong: forall r_0 r_1,
  paco0_2_1 gf_0 gf_1 (upaco0_2_0 gf_0 gf_1 r_0 r_1) (upaco0_2_1 gf_0 gf_1 r_0 r_1) <0== paco0_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply curry_map0.
  eapply le1_trans; [| eapply _paco_2_1_mult_strong].
  apply _paco_2_1_mon; intros []; intros H; apply H.
Qed.

Theorem _paco0_2_0_fold: forall r_0 r_1,
  gf_0 (upaco0_2_0 gf_0 gf_1 r_0 r_1) (upaco0_2_1 gf_0 gf_1 r_0 r_1) <0== paco0_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_0.
  eapply le1_trans; [| apply _paco_2_0_fold]. apply le1_refl.
Qed.

Theorem _paco0_2_1_fold: forall r_0 r_1,
  gf_1 (upaco0_2_0 gf_0 gf_1 r_0 r_1) (upaco0_2_1 gf_0 gf_1 r_0 r_1) <0== paco0_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  intros. apply uncurry_adjoint1_0.
  eapply le1_trans; [| apply _paco_2_1_fold]. apply le1_refl.
Qed.

Theorem _paco0_2_0_unfold: forall (MON: _monotone0_2 gf_0) (MON: _monotone0_2 gf_1) r_0 r_1,
  paco0_2_0 gf_0 gf_1 r_0 r_1 <0== gf_0 (upaco0_2_0 gf_0 gf_1 r_0 r_1) (upaco0_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  intros. apply curry_adjoint2_0.
  eapply _paco_2_0_unfold; apply monotone0_2_map; assumption.
Qed.

Theorem _paco0_2_1_unfold: forall (MON: _monotone0_2 gf_0) (MON: _monotone0_2 gf_1) r_0 r_1,
  paco0_2_1 gf_0 gf_1 r_0 r_1 <0== gf_1 (upaco0_2_0 gf_0 gf_1 r_0 r_1) (upaco0_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  intros. apply curry_adjoint2_0.
  eapply _paco_2_1_unfold; apply monotone0_2_map; assumption.
Qed.

Theorem paco0_2_0_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_0 <0= rr) (CIH: l <0= rr), l <0= paco0_2_0 gf_0 gf_1 rr r_1),
  l <0= paco0_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco0_2_0_acc.
Qed.

Theorem paco0_2_1_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_1 <0= rr) (CIH: l <0= rr), l <0= paco0_2_1 gf_0 gf_1 r_0 rr),
  l <0= paco0_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco0_2_1_acc.
Qed.

Theorem paco0_2_0_mon: monotone0_2 (paco0_2_0 gf_0 gf_1).
Proof.
  apply monotone0_2_eq.
  apply _paco0_2_0_mon.
Qed.

Theorem paco0_2_1_mon: monotone0_2 (paco0_2_1 gf_0 gf_1).
Proof.
  apply monotone0_2_eq.
  apply _paco0_2_1_mon.
Qed.

Theorem upaco0_2_0_mon: monotone0_2 (upaco0_2_0 gf_0 gf_1).
Proof.
  repeat_intros 4. intros R  LE0 LE1.
  destruct R.
  - left. eapply paco0_2_0_mon. apply H. apply LE0. apply LE1.
  - right. apply LE0, H.
Qed.
Theorem upaco0_2_1_mon: monotone0_2 (upaco0_2_1 gf_0 gf_1).
Proof.
  repeat_intros 4. intros R  LE0 LE1.
  destruct R.
  - left. eapply paco0_2_1_mon. apply H. apply LE0. apply LE1.
  - right. apply LE1, H.
Qed.
Theorem paco0_2_0_mult_strong: forall r_0 r_1,
  paco0_2_0 gf_0 gf_1 (upaco0_2_0 gf_0 gf_1 r_0 r_1) (upaco0_2_1 gf_0 gf_1 r_0 r_1) <0= paco0_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco0_2_0_mult_strong.
Qed.

Theorem paco0_2_1_mult_strong: forall r_0 r_1,
  paco0_2_1 gf_0 gf_1 (upaco0_2_0 gf_0 gf_1 r_0 r_1) (upaco0_2_1 gf_0 gf_1 r_0 r_1) <0= paco0_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco0_2_1_mult_strong.
Qed.

Corollary paco0_2_0_mult: forall r_0 r_1,
  paco0_2_0 gf_0 gf_1 (paco0_2_0 gf_0 gf_1 r_0 r_1) (paco0_2_1 gf_0 gf_1 r_0 r_1) <0= paco0_2_0 gf_0 gf_1 r_0 r_1.
Proof. intros; eapply paco0_2_0_mult_strong, paco0_2_0_mon; [apply PR|..]; intros; left; assumption. Qed.

Corollary paco0_2_1_mult: forall r_0 r_1,
  paco0_2_1 gf_0 gf_1 (paco0_2_0 gf_0 gf_1 r_0 r_1) (paco0_2_1 gf_0 gf_1 r_0 r_1) <0= paco0_2_1 gf_0 gf_1 r_0 r_1.
Proof. intros; eapply paco0_2_1_mult_strong, paco0_2_1_mon; [apply PR|..]; intros; left; assumption. Qed.

Theorem paco0_2_0_fold: forall r_0 r_1,
  gf_0 (upaco0_2_0 gf_0 gf_1 r_0 r_1) (upaco0_2_1 gf_0 gf_1 r_0 r_1) <0= paco0_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco0_2_0_fold.
Qed.

Theorem paco0_2_1_fold: forall r_0 r_1,
  gf_1 (upaco0_2_0 gf_0 gf_1 r_0 r_1) (upaco0_2_1 gf_0 gf_1 r_0 r_1) <0= paco0_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  apply _paco0_2_1_fold.
Qed.

Theorem paco0_2_0_unfold: forall (MON: monotone0_2 gf_0) (MON: monotone0_2 gf_1) r_0 r_1,
  paco0_2_0 gf_0 gf_1 r_0 r_1 <0= gf_0 (upaco0_2_0 gf_0 gf_1 r_0 r_1) (upaco0_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  repeat_intros 2. eapply _paco0_2_0_unfold; apply monotone0_2_eq; assumption.
Qed.

Theorem paco0_2_1_unfold: forall (MON: monotone0_2 gf_0) (MON: monotone0_2 gf_1) r_0 r_1,
  paco0_2_1 gf_0 gf_1 r_0 r_1 <0= gf_1 (upaco0_2_0 gf_0 gf_1 r_0 r_1) (upaco0_2_1 gf_0 gf_1 r_0 r_1).
Proof.
  repeat_intros 2. eapply _paco0_2_1_unfold; apply monotone0_2_eq; assumption.
Qed.

End Arg0_2.

Arguments paco0_2_0_acc : clear implicits.
Arguments paco0_2_1_acc : clear implicits.
Arguments paco0_2_0_mon : clear implicits.
Arguments paco0_2_1_mon : clear implicits.
Arguments upaco0_2_0_mon : clear implicits.
Arguments upaco0_2_1_mon : clear implicits.
Arguments paco0_2_0_mult_strong : clear implicits.
Arguments paco0_2_1_mult_strong : clear implicits.
Arguments paco0_2_0_mult : clear implicits.
Arguments paco0_2_1_mult : clear implicits.
Arguments paco0_2_0_fold : clear implicits.
Arguments paco0_2_1_fold : clear implicits.
Arguments paco0_2_0_unfold : clear implicits.
Arguments paco0_2_1_unfold : clear implicits.

Global Instance paco0_2_0_inst  (gf_0 gf_1 : rel0->_) r_0 r_1 : paco_class (paco0_2_0 gf_0 gf_1 r_0 r_1) :=
{ pacoacc    := paco0_2_0_acc gf_0 gf_1;
  pacomult   := paco0_2_0_mult gf_0 gf_1;
  pacofold   := paco0_2_0_fold gf_0 gf_1;
  pacounfold := paco0_2_0_unfold gf_0 gf_1 }.

Global Instance paco0_2_1_inst  (gf_0 gf_1 : rel0->_) r_0 r_1 : paco_class (paco0_2_1 gf_0 gf_1 r_0 r_1) :=
{ pacoacc    := paco0_2_1_acc gf_0 gf_1;
  pacomult   := paco0_2_1_mult gf_0 gf_1;
  pacofold   := paco0_2_1_fold gf_0 gf_1;
  pacounfold := paco0_2_1_unfold gf_0 gf_1 }.

(** 3 Mutual Coinduction *)

Section Arg0_3.

Definition monotone0_3 (gf: rel0 -> rel0 -> rel0 -> rel0) :=
  forall r_0 r_1 r_2 r'_0 r'_1 r'_2 (IN: gf r_0 r_1 r_2) (LE_0: r_0 <0= r'_0)(LE_1: r_1 <0= r'_1)(LE_2: r_2 <0= r'_2), gf r'_0 r'_1 r'_2.

Definition _monotone0_3 (gf: rel0 -> rel0 -> rel0 -> rel0) :=
  forall r_0 r_1 r_2 r'_0 r'_1 r'_2(LE_0: r_0 <0= r'_0)(LE_1: r_1 <0= r'_1)(LE_2: r_2 <0= r'_2), gf r_0 r_1 r_2 <0== gf r'_0 r'_1 r'_2.

Lemma monotone0_3_eq (gf: rel0 -> rel0 -> rel0 -> rel0) :
  monotone0_3 gf <-> _monotone0_3 gf.
Proof. unfold monotone0_3, _monotone0_3, le0. split; intros; eapply H; eassumption. Qed.

Lemma monotone0_3_map (gf: rel0 -> rel0 -> rel0 -> rel0)
      (MON: _monotone0_3 gf) :
  _monotone_3 (fun R0 R1 R2 => uncurry0 (gf (curry0 R0) (curry0 R1) (curry0 R2))).
Proof.
  repeat_intros 9. apply uncurry_map0. apply MON; apply curry_map0; assumption.
Qed.

Variable gf_0 gf_1 gf_2 : rel0 -> rel0 -> rel0 -> rel0.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.
Arguments gf_2 : clear implicits.

Theorem _paco0_3_0_mon: _monotone0_3 (paco0_3_0 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 9. eapply curry_map0, _paco_3_0_mon; apply uncurry_map0; assumption.
Qed.

Theorem _paco0_3_1_mon: _monotone0_3 (paco0_3_1 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 9. eapply curry_map0, _paco_3_1_mon; apply uncurry_map0; assumption.
Qed.

Theorem _paco0_3_2_mon: _monotone0_3 (paco0_3_2 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 9. eapply curry_map0, _paco_3_2_mon; apply uncurry_map0; assumption.
Qed.

Theorem _paco0_3_0_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_0 <0== rr) (CIH: l <0== rr), l <0== paco0_3_0 gf_0 gf_1 gf_2 rr r_1 r_2),
  l <0== paco0_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_0.
  eapply _paco_3_0_acc. intros.
  apply uncurry_adjoint1_0 in INC. apply uncurry_adjoint1_0 in CIH.
  apply uncurry_adjoint2_0.
  eapply le0_trans. eapply (OBG _ INC CIH).
  apply curry_map0.
  apply _paco_3_0_mon; try apply le1_refl; apply curry_bij1_0.
Qed.

Theorem _paco0_3_1_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_1 <0== rr) (CIH: l <0== rr), l <0== paco0_3_1 gf_0 gf_1 gf_2 r_0 rr r_2),
  l <0== paco0_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_0.
  eapply _paco_3_1_acc. intros.
  apply uncurry_adjoint1_0 in INC. apply uncurry_adjoint1_0 in CIH.
  apply uncurry_adjoint2_0.
  eapply le0_trans. eapply (OBG _ INC CIH).
  apply curry_map0.
  apply _paco_3_1_mon; try apply le1_refl; apply curry_bij1_0.
Qed.

Theorem _paco0_3_2_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_2 <0== rr) (CIH: l <0== rr), l <0== paco0_3_2 gf_0 gf_1 gf_2 r_0 r_1 rr),
  l <0== paco0_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_0.
  eapply _paco_3_2_acc. intros.
  apply uncurry_adjoint1_0 in INC. apply uncurry_adjoint1_0 in CIH.
  apply uncurry_adjoint2_0.
  eapply le0_trans. eapply (OBG _ INC CIH).
  apply curry_map0.
  apply _paco_3_2_mon; try apply le1_refl; apply curry_bij1_0.
Qed.

Theorem _paco0_3_0_mult_strong: forall r_0 r_1 r_2,
  paco0_3_0 gf_0 gf_1 gf_2 (upaco0_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco0_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco0_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <0== paco0_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply curry_map0.
  eapply le1_trans; [| eapply _paco_3_0_mult_strong].
  apply _paco_3_0_mon; intros []; intros H; apply H.
Qed.

Theorem _paco0_3_1_mult_strong: forall r_0 r_1 r_2,
  paco0_3_1 gf_0 gf_1 gf_2 (upaco0_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco0_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco0_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <0== paco0_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply curry_map0.
  eapply le1_trans; [| eapply _paco_3_1_mult_strong].
  apply _paco_3_1_mon; intros []; intros H; apply H.
Qed.

Theorem _paco0_3_2_mult_strong: forall r_0 r_1 r_2,
  paco0_3_2 gf_0 gf_1 gf_2 (upaco0_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco0_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco0_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <0== paco0_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply curry_map0.
  eapply le1_trans; [| eapply _paco_3_2_mult_strong].
  apply _paco_3_2_mon; intros []; intros H; apply H.
Qed.

Theorem _paco0_3_0_fold: forall r_0 r_1 r_2,
  gf_0 (upaco0_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco0_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco0_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <0== paco0_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_0.
  eapply le1_trans; [| apply _paco_3_0_fold]. apply le1_refl.
Qed.

Theorem _paco0_3_1_fold: forall r_0 r_1 r_2,
  gf_1 (upaco0_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco0_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco0_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <0== paco0_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_0.
  eapply le1_trans; [| apply _paco_3_1_fold]. apply le1_refl.
Qed.

Theorem _paco0_3_2_fold: forall r_0 r_1 r_2,
  gf_2 (upaco0_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco0_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco0_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <0== paco0_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros. apply uncurry_adjoint1_0.
  eapply le1_trans; [| apply _paco_3_2_fold]. apply le1_refl.
Qed.

Theorem _paco0_3_0_unfold: forall (MON: _monotone0_3 gf_0) (MON: _monotone0_3 gf_1) (MON: _monotone0_3 gf_2) r_0 r_1 r_2,
  paco0_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 <0== gf_0 (upaco0_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco0_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco0_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  intros. apply curry_adjoint2_0.
  eapply _paco_3_0_unfold; apply monotone0_3_map; assumption.
Qed.

Theorem _paco0_3_1_unfold: forall (MON: _monotone0_3 gf_0) (MON: _monotone0_3 gf_1) (MON: _monotone0_3 gf_2) r_0 r_1 r_2,
  paco0_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 <0== gf_1 (upaco0_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco0_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco0_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  intros. apply curry_adjoint2_0.
  eapply _paco_3_1_unfold; apply monotone0_3_map; assumption.
Qed.

Theorem _paco0_3_2_unfold: forall (MON: _monotone0_3 gf_0) (MON: _monotone0_3 gf_1) (MON: _monotone0_3 gf_2) r_0 r_1 r_2,
  paco0_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 <0== gf_2 (upaco0_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco0_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco0_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  intros. apply curry_adjoint2_0.
  eapply _paco_3_2_unfold; apply monotone0_3_map; assumption.
Qed.

Theorem paco0_3_0_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_0 <0= rr) (CIH: l <0= rr), l <0= paco0_3_0 gf_0 gf_1 gf_2 rr r_1 r_2),
  l <0= paco0_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco0_3_0_acc.
Qed.

Theorem paco0_3_1_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_1 <0= rr) (CIH: l <0= rr), l <0= paco0_3_1 gf_0 gf_1 gf_2 r_0 rr r_2),
  l <0= paco0_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco0_3_1_acc.
Qed.

Theorem paco0_3_2_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_2 <0= rr) (CIH: l <0= rr), l <0= paco0_3_2 gf_0 gf_1 gf_2 r_0 r_1 rr),
  l <0= paco0_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco0_3_2_acc.
Qed.

Theorem paco0_3_0_mon: monotone0_3 (paco0_3_0 gf_0 gf_1 gf_2).
Proof.
  apply monotone0_3_eq.
  apply _paco0_3_0_mon.
Qed.

Theorem paco0_3_1_mon: monotone0_3 (paco0_3_1 gf_0 gf_1 gf_2).
Proof.
  apply monotone0_3_eq.
  apply _paco0_3_1_mon.
Qed.

Theorem paco0_3_2_mon: monotone0_3 (paco0_3_2 gf_0 gf_1 gf_2).
Proof.
  apply monotone0_3_eq.
  apply _paco0_3_2_mon.
Qed.

Theorem upaco0_3_0_mon: monotone0_3 (upaco0_3_0 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 6. intros R  LE0 LE1 LE2.
  destruct R.
  - left. eapply paco0_3_0_mon. apply H. apply LE0. apply LE1. apply LE2.
  - right. apply LE0, H.
Qed.
Theorem upaco0_3_1_mon: monotone0_3 (upaco0_3_1 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 6. intros R  LE0 LE1 LE2.
  destruct R.
  - left. eapply paco0_3_1_mon. apply H. apply LE0. apply LE1. apply LE2.
  - right. apply LE1, H.
Qed.
Theorem upaco0_3_2_mon: monotone0_3 (upaco0_3_2 gf_0 gf_1 gf_2).
Proof.
  repeat_intros 6. intros R  LE0 LE1 LE2.
  destruct R.
  - left. eapply paco0_3_2_mon. apply H. apply LE0. apply LE1. apply LE2.
  - right. apply LE2, H.
Qed.
Theorem paco0_3_0_mult_strong: forall r_0 r_1 r_2,
  paco0_3_0 gf_0 gf_1 gf_2 (upaco0_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco0_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco0_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <0= paco0_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco0_3_0_mult_strong.
Qed.

Theorem paco0_3_1_mult_strong: forall r_0 r_1 r_2,
  paco0_3_1 gf_0 gf_1 gf_2 (upaco0_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco0_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco0_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <0= paco0_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco0_3_1_mult_strong.
Qed.

Theorem paco0_3_2_mult_strong: forall r_0 r_1 r_2,
  paco0_3_2 gf_0 gf_1 gf_2 (upaco0_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco0_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco0_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <0= paco0_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco0_3_2_mult_strong.
Qed.

Corollary paco0_3_0_mult: forall r_0 r_1 r_2,
  paco0_3_0 gf_0 gf_1 gf_2 (paco0_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco0_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco0_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <0= paco0_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco0_3_0_mult_strong, paco0_3_0_mon; [apply PR|..]; intros; left; assumption. Qed.

Corollary paco0_3_1_mult: forall r_0 r_1 r_2,
  paco0_3_1 gf_0 gf_1 gf_2 (paco0_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco0_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco0_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <0= paco0_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco0_3_1_mult_strong, paco0_3_1_mon; [apply PR|..]; intros; left; assumption. Qed.

Corollary paco0_3_2_mult: forall r_0 r_1 r_2,
  paco0_3_2 gf_0 gf_1 gf_2 (paco0_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco0_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco0_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <0= paco0_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco0_3_2_mult_strong, paco0_3_2_mon; [apply PR|..]; intros; left; assumption. Qed.

Theorem paco0_3_0_fold: forall r_0 r_1 r_2,
  gf_0 (upaco0_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco0_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco0_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <0= paco0_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco0_3_0_fold.
Qed.

Theorem paco0_3_1_fold: forall r_0 r_1 r_2,
  gf_1 (upaco0_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco0_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco0_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <0= paco0_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco0_3_1_fold.
Qed.

Theorem paco0_3_2_fold: forall r_0 r_1 r_2,
  gf_2 (upaco0_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco0_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco0_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <0= paco0_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  apply _paco0_3_2_fold.
Qed.

Theorem paco0_3_0_unfold: forall (MON: monotone0_3 gf_0) (MON: monotone0_3 gf_1) (MON: monotone0_3 gf_2) r_0 r_1 r_2,
  paco0_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 <0= gf_0 (upaco0_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco0_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco0_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  repeat_intros 3. eapply _paco0_3_0_unfold; apply monotone0_3_eq; assumption.
Qed.

Theorem paco0_3_1_unfold: forall (MON: monotone0_3 gf_0) (MON: monotone0_3 gf_1) (MON: monotone0_3 gf_2) r_0 r_1 r_2,
  paco0_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 <0= gf_1 (upaco0_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco0_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco0_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  repeat_intros 3. eapply _paco0_3_1_unfold; apply monotone0_3_eq; assumption.
Qed.

Theorem paco0_3_2_unfold: forall (MON: monotone0_3 gf_0) (MON: monotone0_3 gf_1) (MON: monotone0_3 gf_2) r_0 r_1 r_2,
  paco0_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 <0= gf_2 (upaco0_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco0_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco0_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof.
  repeat_intros 3. eapply _paco0_3_2_unfold; apply monotone0_3_eq; assumption.
Qed.

End Arg0_3.

Arguments paco0_3_0_acc : clear implicits.
Arguments paco0_3_1_acc : clear implicits.
Arguments paco0_3_2_acc : clear implicits.
Arguments paco0_3_0_mon : clear implicits.
Arguments paco0_3_1_mon : clear implicits.
Arguments paco0_3_2_mon : clear implicits.
Arguments upaco0_3_0_mon : clear implicits.
Arguments upaco0_3_1_mon : clear implicits.
Arguments upaco0_3_2_mon : clear implicits.
Arguments paco0_3_0_mult_strong : clear implicits.
Arguments paco0_3_1_mult_strong : clear implicits.
Arguments paco0_3_2_mult_strong : clear implicits.
Arguments paco0_3_0_mult : clear implicits.
Arguments paco0_3_1_mult : clear implicits.
Arguments paco0_3_2_mult : clear implicits.
Arguments paco0_3_0_fold : clear implicits.
Arguments paco0_3_1_fold : clear implicits.
Arguments paco0_3_2_fold : clear implicits.
Arguments paco0_3_0_unfold : clear implicits.
Arguments paco0_3_1_unfold : clear implicits.
Arguments paco0_3_2_unfold : clear implicits.

Global Instance paco0_3_0_inst  (gf_0 gf_1 gf_2 : rel0->_) r_0 r_1 r_2 : paco_class (paco0_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) :=
{ pacoacc    := paco0_3_0_acc gf_0 gf_1 gf_2;
  pacomult   := paco0_3_0_mult gf_0 gf_1 gf_2;
  pacofold   := paco0_3_0_fold gf_0 gf_1 gf_2;
  pacounfold := paco0_3_0_unfold gf_0 gf_1 gf_2 }.

Global Instance paco0_3_1_inst  (gf_0 gf_1 gf_2 : rel0->_) r_0 r_1 r_2 : paco_class (paco0_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) :=
{ pacoacc    := paco0_3_1_acc gf_0 gf_1 gf_2;
  pacomult   := paco0_3_1_mult gf_0 gf_1 gf_2;
  pacofold   := paco0_3_1_fold gf_0 gf_1 gf_2;
  pacounfold := paco0_3_1_unfold gf_0 gf_1 gf_2 }.

Global Instance paco0_3_2_inst  (gf_0 gf_1 gf_2 : rel0->_) r_0 r_1 r_2 : paco_class (paco0_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) :=
{ pacoacc    := paco0_3_2_acc gf_0 gf_1 gf_2;
  pacomult   := paco0_3_2_mult gf_0 gf_1 gf_2;
  pacofold   := paco0_3_2_fold gf_0 gf_1 gf_2;
  pacounfold := paco0_3_2_unfold gf_0 gf_1 gf_2 }.

End PACO0.

Global Opaque paco0.

Hint Unfold upaco0.
Hint Resolve paco0_fold.
Hint Unfold monotone0.

Global Opaque paco0_2_0.
Global Opaque paco0_2_1.

Hint Unfold upaco0_2_0.
Hint Unfold upaco0_2_1.
Hint Resolve paco0_2_0_fold.
Hint Resolve paco0_2_1_fold.
Hint Unfold monotone0_2.

Global Opaque paco0_3_0.
Global Opaque paco0_3_1.
Global Opaque paco0_3_2.

Hint Unfold upaco0_3_0.
Hint Unfold upaco0_3_1.
Hint Unfold upaco0_3_2.
Hint Resolve paco0_3_0_fold.
Hint Resolve paco0_3_1_fold.
Hint Resolve paco0_3_2_fold.
Hint Unfold monotone0_3.

