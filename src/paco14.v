Require Export Program.Basics. Open Scope program_scope.
From Paco Require Import paconotation_internal paco_internal pacotac_internal.
From Paco Require Export paconotation.
Set Implicit Arguments.

Section PACO14.

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

(** ** Predicates of Arity 14
*)

Definition paco14(gf : rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13)(r: rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13) : rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 :=
  @curry14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 (paco (fun R0 => @uncurry14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 (gf (@curry14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 R0))) (@uncurry14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 r)).

Definition upaco14(gf : rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13)(r: rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13) := paco14 gf r \14/ r.
Arguments paco14 : clear implicits.
Arguments upaco14 : clear implicits.
Hint Unfold upaco14 : core.

Definition monotone14 (gf: rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13) :=
  forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 r r' (IN: gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) (LE: r <14= r'), gf r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13.

Definition _monotone14 (gf: rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13) :=
  forall r r'(LE: r <14= r'), gf r <14== gf r'.

Lemma monotone14_eq (gf: rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13) :
  monotone14 gf <-> _monotone14 gf.
Proof. unfold monotone14, _monotone14, le14. split; intros; eapply H; eassumption. Qed.

Lemma monotone14_map (gf: rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13)
      (MON: _monotone14 gf) :
  _monotone (fun R0 => @uncurry14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 (gf (@curry14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 R0))).
Proof.
  red; intros. apply uncurry_map14. apply MON; apply curry_map14; assumption.
Qed.

Lemma monotone14_compose (gf gf': rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13)
      (MON1: monotone14 gf)
      (MON2: monotone14 gf'):
  monotone14 (compose gf gf').
Proof.
  red; intros. eapply MON1. apply IN.
  intros. eapply MON2. apply PR. apply LE.
Qed.

Lemma monotone14_union (gf gf': rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13)
      (MON1: monotone14 gf)
      (MON2: monotone14 gf'):
  monotone14 (gf \15/ gf').
Proof.
  red; intros. destruct IN.
  - left. eapply MON1. apply H. apply LE.
  - right. eapply MON2. apply H. apply LE.
Qed.

Lemma _paco14_mon_gen (gf gf': rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13) r r'
    (LEgf: gf <15= gf')
    (LEr: r <14= r'):
  paco14 gf r <14== paco14 gf' r'.
Proof.
  apply curry_map14. red; intros. eapply paco_mon_gen. apply PR.
  - intros. apply LEgf, PR0.
  - intros. apply LEr, PR0.
Qed.

Lemma paco14_mon_gen (gf gf': rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13) r r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13
    (REL: paco14 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13)
    (LEgf: gf <15= gf')
    (LEr: r <14= r'):
  paco14 gf' r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13.
Proof.
  eapply _paco14_mon_gen; [apply LEgf | apply LEr | apply REL].
Qed.

Lemma paco14_mon_bot (gf gf': rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13) r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13
    (REL: paco14 gf bot14 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13)
    (LEgf: gf <15= gf'):
  paco14 gf' r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13.
Proof.
  eapply paco14_mon_gen; [apply REL | apply LEgf | intros; contradiction PR].
Qed.

Lemma upaco14_mon_gen (gf gf': rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13) r r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13
    (REL: upaco14 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13)
    (LEgf: gf <15= gf')
    (LEr: r <14= r'):
  upaco14 gf' r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13.
Proof.
  destruct REL.
  - left. eapply paco14_mon_gen; [apply H | apply LEgf | apply LEr].
  - right. apply LEr, H.
Qed.

Lemma upaco14_mon_bot (gf gf': rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13) r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13
    (REL: upaco14 gf bot14 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13)
    (LEgf: gf <15= gf'):
  upaco14 gf' r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13.
Proof.
  eapply upaco14_mon_gen; [apply REL | apply LEgf | intros; contradiction PR].
Qed.

Section Arg14.

Variable gf : rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13.
Arguments gf : clear implicits.

Theorem _paco14_mon: _monotone14 (paco14 gf).
Proof.
  red; intros. eapply curry_map14, _paco_mon; apply uncurry_map14; assumption.
Qed.

Theorem _paco14_acc: forall
  l r (OBG: forall rr (INC: r <14== rr) (CIH: l <14== rr), l <14== paco14 gf rr),
  l <14== paco14 gf r.
Proof.
  intros. apply uncurry_adjoint1_14.
  eapply _paco_acc. intros.
  apply uncurry_adjoint1_14 in INC. apply uncurry_adjoint1_14 in CIH.
  apply uncurry_adjoint2_14.
  eapply le14_trans. eapply (OBG _ INC CIH).
  apply curry_map14.
  apply _paco_mon; try apply le1_refl; apply curry_bij1_14.
Qed.

Theorem _paco14_mult_strong: forall r,
  paco14 gf (upaco14 gf r) <14== paco14 gf r.
Proof.
  intros. apply curry_map14.
  eapply le1_trans; [| eapply _paco_mult_strong].
  apply _paco_mon; intros [] H; apply H.
Qed.

Theorem _paco14_fold: forall r,
  gf (upaco14 gf r) <14== paco14 gf r.
Proof.
  intros. apply uncurry_adjoint1_14.
  eapply le1_trans; [| apply _paco_fold]. apply le1_refl.
Qed.

Theorem _paco14_unfold: forall (MON: _monotone14 gf) r,
  paco14 gf r <14== gf (upaco14 gf r).
Proof.
  intros. apply curry_adjoint2_14.
  eapply _paco_unfold; apply monotone14_map; assumption.
Qed.

Theorem paco14_acc: forall
  l r (OBG: forall rr (INC: r <14= rr) (CIH: l <14= rr), l <14= paco14 gf rr),
  l <14= paco14 gf r.
Proof.
  apply _paco14_acc.
Qed.

Theorem paco14_mon: monotone14 (paco14 gf).
Proof.
  apply monotone14_eq.
  apply _paco14_mon.
Qed.

Theorem upaco14_mon: monotone14 (upaco14 gf).
Proof.
  red; intros.
  destruct IN.
  - left. eapply paco14_mon. apply H. apply LE.
  - right. apply LE, H.
Qed.

Theorem paco14_mult_strong: forall r,
  paco14 gf (upaco14 gf r) <14= paco14 gf r.
Proof.
  apply _paco14_mult_strong.
Qed.

Corollary paco14_mult: forall r,
  paco14 gf (paco14 gf r) <14= paco14 gf r.
Proof. intros; eapply paco14_mult_strong, paco14_mon; [apply PR|..]; intros; left; assumption. Qed.

Theorem paco14_fold: forall r,
  gf (upaco14 gf r) <14= paco14 gf r.
Proof.
  apply _paco14_fold.
Qed.

Theorem paco14_unfold: forall (MON: monotone14 gf) r,
  paco14 gf r <14= gf (upaco14 gf r).
Proof.
  intro. eapply _paco14_unfold; apply monotone14_eq; assumption.
Qed.

End Arg14.

Arguments paco14_acc : clear implicits.
Arguments paco14_mon : clear implicits.
Arguments upaco14_mon : clear implicits.
Arguments paco14_mult_strong : clear implicits.
Arguments paco14_mult : clear implicits.
Arguments paco14_fold : clear implicits.
Arguments paco14_unfold : clear implicits.

Global Instance paco14_inst  (gf : rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13->_) r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : paco_class (paco14 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) :=
{ pacoacc    := paco14_acc gf;
  pacomult   := paco14_mult gf;
  pacofold   := paco14_fold gf;
  pacounfold := paco14_unfold gf }.

End PACO14.

Global Opaque paco14.

Hint Unfold upaco14 : core.
Hint Resolve paco14_fold : core.
Hint Unfold monotone14 : core.

