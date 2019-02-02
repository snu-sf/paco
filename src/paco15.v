Require Export paconotation pacotacuser.
Require Import paconotation_internal pacotac pacon.
Set Implicit Arguments.

Section PACO15.

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
Variable T12 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10), Type.
Variable T13 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) (x12: @T12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11), Type.
Variable T14 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) (x12: @T12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) (x13: @T13 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12), Type.

Record sig15T :=
  exist15T { 
      proj15T0: @T0;
      proj15T1: @T1 proj15T0;
      proj15T2: @T2 proj15T0 proj15T1;
      proj15T3: @T3 proj15T0 proj15T1 proj15T2;
      proj15T4: @T4 proj15T0 proj15T1 proj15T2 proj15T3;
      proj15T5: @T5 proj15T0 proj15T1 proj15T2 proj15T3 proj15T4;
      proj15T6: @T6 proj15T0 proj15T1 proj15T2 proj15T3 proj15T4 proj15T5;
      proj15T7: @T7 proj15T0 proj15T1 proj15T2 proj15T3 proj15T4 proj15T5 proj15T6;
      proj15T8: @T8 proj15T0 proj15T1 proj15T2 proj15T3 proj15T4 proj15T5 proj15T6 proj15T7;
      proj15T9: @T9 proj15T0 proj15T1 proj15T2 proj15T3 proj15T4 proj15T5 proj15T6 proj15T7 proj15T8;
      proj15T10: @T10 proj15T0 proj15T1 proj15T2 proj15T3 proj15T4 proj15T5 proj15T6 proj15T7 proj15T8 proj15T9;
      proj15T11: @T11 proj15T0 proj15T1 proj15T2 proj15T3 proj15T4 proj15T5 proj15T6 proj15T7 proj15T8 proj15T9 proj15T10;
      proj15T12: @T12 proj15T0 proj15T1 proj15T2 proj15T3 proj15T4 proj15T5 proj15T6 proj15T7 proj15T8 proj15T9 proj15T10 proj15T11;
      proj15T13: @T13 proj15T0 proj15T1 proj15T2 proj15T3 proj15T4 proj15T5 proj15T6 proj15T7 proj15T8 proj15T9 proj15T10 proj15T11 proj15T12;
      proj15T14: @T14 proj15T0 proj15T1 proj15T2 proj15T3 proj15T4 proj15T5 proj15T6 proj15T7 proj15T8 proj15T9 proj15T10 proj15T11 proj15T12 proj15T13;
    }.

Definition uncurry15 (R: rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14): rel1 sig15T := fun x => R (proj15T0 x) (proj15T1 x) (proj15T2 x) (proj15T3 x) (proj15T4 x) (proj15T5 x) (proj15T6 x) (proj15T7 x) (proj15T8 x) (proj15T9 x) (proj15T10 x) (proj15T11 x) (proj15T12 x) (proj15T13 x) (proj15T14 x).

Definition curry15 (R: rel1 sig15T): rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 :=
  fun x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 => R (exist15T x14).

Lemma uncurry_map15 r0 r1 (LE : r0 <15== r1) : uncurry15 r0 <1== uncurry15 r1.
Proof. intros [] H. apply LE. apply H. Qed.

Lemma uncurry_map_rev15 r0 r1 (LE: uncurry15 r0 <1== uncurry15 r1) : r0 <15== r1.
Proof.
  repeat_intros 15. intros H. apply (LE (exist15T x14) H).
Qed.

Lemma curry_map15 r0 r1 (LE: r0 <1== r1) : curry15 r0 <15== curry15 r1.
Proof. 
  repeat_intros 15. intros H. apply (LE (exist15T x14) H).
Qed.

Lemma curry_map_rev15 r0 r1 (LE: curry15 r0 <15== curry15 r1) : r0 <1== r1.
Proof. 
  intros [] H. apply LE. apply H.
Qed.

Lemma uncurry_bij1_15 r : curry15 (uncurry15 r) <15== r.
Proof. unfold le15. repeat_intros 15. intros H. apply H. Qed.

Lemma uncurry_bij2_15 r : r <15== curry15 (uncurry15 r).
Proof. unfold le15. repeat_intros 15. intros H. apply H. Qed.

Lemma curry_bij1_15 r : uncurry15 (curry15 r) <1== r.
Proof. intros []. intro H. apply H. Qed.

Lemma curry_bij2_15 r : r <1== uncurry15 (curry15 r).
Proof. intros []. intro H. apply H. Qed.

Lemma uncurry_adjoint1_15 r0 r1 (LE: uncurry15 r0 <1== r1) : r0 <15== curry15 r1.
Proof.
  apply uncurry_map_rev15. eapply le1_trans; [apply LE|]. apply curry_bij2_15.
Qed.

Lemma uncurry_adjoint2_15 r0 r1 (LE: r0 <15== curry15 r1) : uncurry15 r0 <1== r1.
Proof.
  apply curry_map_rev15. eapply le15_trans; [|apply LE]. apply uncurry_bij2_15.
Qed.

Lemma curry_adjoint1_15 r0 r1 (LE: curry15 r0 <15== r1) : r0 <1== uncurry15 r1.
Proof.
  apply curry_map_rev15. eapply le15_trans; [apply LE|]. apply uncurry_bij2_15.
Qed.

Lemma curry_adjoint2_15 r0 r1 (LE: r0 <1== uncurry15 r1) : curry15 r0 <15== r1.
Proof.
  apply uncurry_map_rev15. eapply le1_trans; [|apply LE]. apply curry_bij1_15.
Qed.

(** ** Predicates of Arity 15
*)

Definition paco15(gf : rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 -> rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14)(r: rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14) : rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 :=
  curry15 (paco (fun R0 => uncurry15 (gf (curry15 R0))) (uncurry15 r)).

Definition upaco15(gf : rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 -> rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14)(r: rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14) := paco15 gf r \15/ r.
Arguments paco15 : clear implicits.
Arguments upaco15 : clear implicits.
Hint Unfold upaco15.

Definition monotone15 (gf: rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 -> rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14) :=
  forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 r r' (IN: gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14) (LE: r <15= r'), gf r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14.

Definition _monotone15 (gf: rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 -> rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14) :=
  forall r r'(LE: r <15= r'), gf r <15== gf r'.

Lemma monotone15_eq (gf: rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 -> rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14) :
  monotone15 gf <-> _monotone15 gf.
Proof. unfold monotone15, _monotone15, le15. split; intros; eapply H; eassumption. Qed.

Lemma monotone15_map (gf: rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 -> rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14)
      (MON: _monotone15 gf) :
  _monotone (fun R0 => uncurry15 (gf (curry15 R0))).
Proof.
  repeat_intros 3. apply uncurry_map15. apply MON; apply curry_map15; assumption.
Qed.

Section Arg15.

Variable gf : rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 -> rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14.
Arguments gf : clear implicits.

Theorem _paco15_mon: _monotone15 (paco15 gf).
Proof.
  repeat_intros 3. eapply curry_map15, _paco_mon; apply uncurry_map15; assumption.
Qed.

Theorem _paco15_acc: forall
  l r (OBG: forall rr (INC: r <15== rr) (CIH: l <15== rr), l <15== paco15 gf rr),
  l <15== paco15 gf r.
Proof.
  intros. apply uncurry_adjoint1_15.
  eapply _paco_acc. intros.
  apply uncurry_adjoint1_15 in INC. apply uncurry_adjoint1_15 in CIH.
  apply uncurry_adjoint2_15.
  eapply le15_trans. eapply (OBG _ INC CIH).
  apply curry_map15.
  apply _paco_mon; try apply le1_refl; apply curry_bij1_15.
Qed.

Theorem _paco15_mult_strong: forall r,
  paco15 gf (upaco15 gf r) <15== paco15 gf r.
Proof.
  intros. apply curry_map15.
  eapply le1_trans; [| eapply _paco_mult_strong].
  apply _paco_mon; intros []; intros H; apply H.
Qed.

Theorem _paco15_fold: forall r,
  gf (upaco15 gf r) <15== paco15 gf r.
Proof.
  intros. apply uncurry_adjoint1_15.
  eapply le1_trans; [| apply _paco_fold]. apply le1_refl.
Qed.

Theorem _paco15_unfold: forall (MON: _monotone15 gf) r,
  paco15 gf r <15== gf (upaco15 gf r).
Proof.
  intros. apply curry_adjoint2_15.
  eapply _paco_unfold; apply monotone15_map; assumption.
Qed.

Theorem paco15_acc: forall
  l r (OBG: forall rr (INC: r <15= rr) (CIH: l <15= rr), l <15= paco15 gf rr),
  l <15= paco15 gf r.
Proof.
  apply _paco15_acc.
Qed.

Theorem paco15_mon: monotone15 (paco15 gf).
Proof.
  apply monotone15_eq.
  apply _paco15_mon.
Qed.

Theorem upaco15_mon: monotone15 (upaco15 gf).
Proof.
  repeat_intros 17. intros R  LE0.
  destruct R.
  - left. eapply paco15_mon. apply H. apply LE0.
  - right. apply LE0, H.
Qed.
Theorem paco15_mult_strong: forall r,
  paco15 gf (upaco15 gf r) <15= paco15 gf r.
Proof.
  apply _paco15_mult_strong.
Qed.

Corollary paco15_mult: forall r,
  paco15 gf (paco15 gf r) <15= paco15 gf r.
Proof. intros; eapply paco15_mult_strong, paco15_mon; [apply PR|..]; intros; left; assumption. Qed.

Theorem paco15_fold: forall r,
  gf (upaco15 gf r) <15= paco15 gf r.
Proof.
  apply _paco15_fold.
Qed.

Theorem paco15_unfold: forall (MON: monotone15 gf) r,
  paco15 gf r <15= gf (upaco15 gf r).
Proof.
  repeat_intros 1. eapply _paco15_unfold; apply monotone15_eq; assumption.
Qed.

End Arg15.

Arguments paco15_acc : clear implicits.
Arguments paco15_mon : clear implicits.
Arguments upaco15_mon : clear implicits.
Arguments paco15_mult_strong : clear implicits.
Arguments paco15_mult : clear implicits.
Arguments paco15_fold : clear implicits.
Arguments paco15_unfold : clear implicits.

Global Instance paco15_inst  (gf : rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14->_) r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : paco_class (paco15 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14) :=
{ pacoacc    := paco15_acc gf;
  pacomult   := paco15_mult gf;
  pacofold   := paco15_fold gf;
  pacounfold := paco15_unfold gf }.

Lemma upaco15_clear gf x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14:
  upaco15 gf bot15 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 <-> paco15 gf bot15 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14.
Proof. split; intros; [destruct H;[apply H|destruct H]|left; apply H]. Qed.

End PACO15.

Global Opaque paco15.

Hint Unfold upaco15.
Hint Resolve paco15_fold.
Hint Unfold monotone15.

