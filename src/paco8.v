Require Export paconotation pacotacuser.
Require Import paconotation_internal pacotac pacon.
Set Implicit Arguments.

Section PACO8.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
Variable T7 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5), Type.

Record sig8T :=
  exist8T { 
      proj8T0: @T0;
      proj8T1: @T1 proj8T0;
      proj8T2: @T2 proj8T0 proj8T1;
      proj8T3: @T3 proj8T0 proj8T1 proj8T2;
      proj8T4: @T4 proj8T0 proj8T1 proj8T2 proj8T3;
      proj8T5: @T5 proj8T0 proj8T1 proj8T2 proj8T3 proj8T4;
      proj8T6: @T6 proj8T0 proj8T1 proj8T2 proj8T3 proj8T4 proj8T5;
      proj8T7: @T7 proj8T0 proj8T1 proj8T2 proj8T3 proj8T4 proj8T5 proj8T6;
    }.

Definition uncurry8 (R: rel8 T0 T1 T2 T3 T4 T5 T6 T7): rel1 sig8T := fun x => R (proj8T0 x) (proj8T1 x) (proj8T2 x) (proj8T3 x) (proj8T4 x) (proj8T5 x) (proj8T6 x) (proj8T7 x).

Definition curry8 (R: rel1 sig8T): rel8 T0 T1 T2 T3 T4 T5 T6 T7 :=
  fun x0 x1 x2 x3 x4 x5 x6 x7 => R (exist8T x7).

Lemma uncurry_map8 r0 r1 (LE : r0 <8== r1) : uncurry8 r0 <1== uncurry8 r1.
Proof. intros [] H. apply LE. apply H. Qed.

Lemma uncurry_map_rev8 r0 r1 (LE: uncurry8 r0 <1== uncurry8 r1) : r0 <8== r1.
Proof.
  repeat_intros 8. intros H. apply (LE (exist8T x7) H).
Qed.

Lemma curry_map8 r0 r1 (LE: r0 <1== r1) : curry8 r0 <8== curry8 r1.
Proof. 
  repeat_intros 8. intros H. apply (LE (exist8T x7) H).
Qed.

Lemma curry_map_rev8 r0 r1 (LE: curry8 r0 <8== curry8 r1) : r0 <1== r1.
Proof. 
  intros [] H. apply LE. apply H.
Qed.

Lemma uncurry_bij1_8 r : curry8 (uncurry8 r) <8== r.
Proof. unfold le8. repeat_intros 8. intros H. apply H. Qed.

Lemma uncurry_bij2_8 r : r <8== curry8 (uncurry8 r).
Proof. unfold le8. repeat_intros 8. intros H. apply H. Qed.

Lemma curry_bij1_8 r : uncurry8 (curry8 r) <1== r.
Proof. intros []. intro H. apply H. Qed.

Lemma curry_bij2_8 r : r <1== uncurry8 (curry8 r).
Proof. intros []. intro H. apply H. Qed.

Lemma uncurry_adjoint1_8 r0 r1 (LE: uncurry8 r0 <1== r1) : r0 <8== curry8 r1.
Proof.
  apply uncurry_map_rev8. eapply le1_trans; [apply LE|]. apply curry_bij2_8.
Qed.

Lemma uncurry_adjoint2_8 r0 r1 (LE: r0 <8== curry8 r1) : uncurry8 r0 <1== r1.
Proof.
  apply curry_map_rev8. eapply le8_trans; [|apply LE]. apply uncurry_bij2_8.
Qed.

Lemma curry_adjoint1_8 r0 r1 (LE: curry8 r0 <8== r1) : r0 <1== uncurry8 r1.
Proof.
  apply curry_map_rev8. eapply le8_trans; [apply LE|]. apply uncurry_bij2_8.
Qed.

Lemma curry_adjoint2_8 r0 r1 (LE: r0 <1== uncurry8 r1) : curry8 r0 <8== r1.
Proof.
  apply uncurry_map_rev8. eapply le1_trans; [|apply LE]. apply curry_bij1_8.
Qed.

(** ** Predicates of Arity 8
*)

Section Arg8_def.
Variable gf : rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7.
Arguments gf : clear implicits.

Definition paco8( r: rel8 T0 T1 T2 T3 T4 T5 T6 T7) : rel8 T0 T1 T2 T3 T4 T5 T6 T7 :=
  curry8 (paco (fun R0 => uncurry8 (gf (curry8 R0))) (uncurry8 r)).

Definition upaco8( r: rel8 T0 T1 T2 T3 T4 T5 T6 T7) := paco8 r \8/ r.
End Arg8_def.
Arguments paco8 : clear implicits.
Arguments upaco8 : clear implicits.
Hint Unfold upaco8.

(** 1 Mutual Coinduction *)

Section Arg8_1.

Definition monotone8 (gf: rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7) :=
  forall x0 x1 x2 x3 x4 x5 x6 x7 r r' (IN: gf r x0 x1 x2 x3 x4 x5 x6 x7) (LE: r <8= r'), gf r' x0 x1 x2 x3 x4 x5 x6 x7.

Definition _monotone8 (gf: rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7) :=
  forall r r'(LE: r <8= r'), gf r <8== gf r'.

Lemma monotone8_eq (gf: rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7) :
  monotone8 gf <-> _monotone8 gf.
Proof. unfold monotone8, _monotone8, le8. split; intros; eapply H; eassumption. Qed.

Lemma monotone8_map (gf: rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7)
      (MON: _monotone8 gf) :
  _monotone (fun R0 => uncurry8 (gf (curry8 R0))).
Proof.
  repeat_intros 3. apply uncurry_map8. apply MON; apply curry_map8; assumption.
Qed.

Variable gf : rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7.
Arguments gf : clear implicits.

Theorem _paco8_mon: _monotone8 (paco8 gf).
Proof.
  repeat_intros 3. eapply curry_map8, _paco_mon; apply uncurry_map8; assumption.
Qed.

Theorem _paco8_acc: forall
  l r (OBG: forall rr (INC: r <8== rr) (CIH: l <8== rr), l <8== paco8 gf rr),
  l <8== paco8 gf r.
Proof.
  intros. apply uncurry_adjoint1_8.
  eapply _paco_acc. intros.
  apply uncurry_adjoint1_8 in INC. apply uncurry_adjoint1_8 in CIH.
  apply uncurry_adjoint2_8.
  eapply le8_trans. eapply (OBG _ INC CIH).
  apply curry_map8.
  apply _paco_mon; try apply le1_refl; apply curry_bij1_8.
Qed.

Theorem _paco8_mult_strong: forall r,
  paco8 gf (upaco8 gf r) <8== paco8 gf r.
Proof.
  intros. apply curry_map8.
  eapply le1_trans; [| eapply _paco_mult_strong].
  apply _paco_mon; intros []; intros H; apply H.
Qed.

Theorem _paco8_fold: forall r,
  gf (upaco8 gf r) <8== paco8 gf r.
Proof.
  intros. apply uncurry_adjoint1_8.
  eapply le1_trans; [| apply _paco_fold]. apply le1_refl.
Qed.

Theorem _paco8_unfold: forall (MON: _monotone8 gf) r,
  paco8 gf r <8== gf (upaco8 gf r).
Proof.
  intros. apply curry_adjoint2_8.
  eapply _paco_unfold; apply monotone8_map; assumption.
Qed.

Theorem paco8_acc: forall
  l r (OBG: forall rr (INC: r <8= rr) (CIH: l <8= rr), l <8= paco8 gf rr),
  l <8= paco8 gf r.
Proof.
  apply _paco8_acc.
Qed.

Theorem paco8_mon: monotone8 (paco8 gf).
Proof.
  apply monotone8_eq.
  apply _paco8_mon.
Qed.

Theorem upaco8_mon: monotone8 (upaco8 gf).
Proof.
  repeat_intros 10. intros R  LE0.
  destruct R.
  - left. eapply paco8_mon. apply H. apply LE0.
  - right. apply LE0, H.
Qed.
Theorem paco8_mult_strong: forall r,
  paco8 gf (upaco8 gf r) <8= paco8 gf r.
Proof.
  apply _paco8_mult_strong.
Qed.

Corollary paco8_mult: forall r,
  paco8 gf (paco8 gf r) <8= paco8 gf r.
Proof. intros; eapply paco8_mult_strong, paco8_mon; [apply PR|..]; intros; left; assumption. Qed.

Theorem paco8_fold: forall r,
  gf (upaco8 gf r) <8= paco8 gf r.
Proof.
  apply _paco8_fold.
Qed.

Theorem paco8_unfold: forall (MON: monotone8 gf) r,
  paco8 gf r <8= gf (upaco8 gf r).
Proof.
  repeat_intros 1. eapply _paco8_unfold; apply monotone8_eq; assumption.
Qed.

End Arg8_1.

Arguments paco8_acc : clear implicits.
Arguments paco8_mon : clear implicits.
Arguments upaco8_mon : clear implicits.
Arguments paco8_mult_strong : clear implicits.
Arguments paco8_mult : clear implicits.
Arguments paco8_fold : clear implicits.
Arguments paco8_unfold : clear implicits.

Global Instance paco8_inst  (gf : rel8 T0 T1 T2 T3 T4 T5 T6 T7->_) r x0 x1 x2 x3 x4 x5 x6 x7 : paco_class (paco8 gf r x0 x1 x2 x3 x4 x5 x6 x7) :=
{ pacoacc    := paco8_acc gf;
  pacomult   := paco8_mult gf;
  pacofold   := paco8_fold gf;
  pacounfold := paco8_unfold gf }.

Lemma upaco8_clear gf x0 x1 x2 x3 x4 x5 x6 x7:
  upaco8 gf bot8 x0 x1 x2 x3 x4 x5 x6 x7 <-> paco8 gf bot8 x0 x1 x2 x3 x4 x5 x6 x7.
Proof. split; intros; [destruct H;[apply H|destruct H]|left; apply H]. Qed.

End PACO8.

Global Opaque paco8.

Hint Unfold upaco8.
Hint Resolve paco8_fold.
Hint Unfold monotone8.

