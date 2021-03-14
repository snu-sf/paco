Require Export Program.Basics. Open Scope program_scope.
From Paco Require Import paconotation_internal paco_internal pacotac_internal.
From Paco Require Export paconotation.
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

(** ** Predicates of Arity 8
*)

Definition paco8(gf : rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7)(r: rel8 T0 T1 T2 T3 T4 T5 T6 T7) : rel8 T0 T1 T2 T3 T4 T5 T6 T7 :=
  @curry8 T0 T1 T2 T3 T4 T5 T6 T7 (paco (fun R0 => @uncurry8 T0 T1 T2 T3 T4 T5 T6 T7 (gf (@curry8 T0 T1 T2 T3 T4 T5 T6 T7 R0))) (@uncurry8 T0 T1 T2 T3 T4 T5 T6 T7 r)).

Definition upaco8(gf : rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7)(r: rel8 T0 T1 T2 T3 T4 T5 T6 T7) := paco8 gf r \8/ r.
Arguments paco8 : clear implicits.
Arguments upaco8 : clear implicits.
Hint Unfold upaco8 : core.

Definition monotone8 (gf: rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7) :=
  forall x0 x1 x2 x3 x4 x5 x6 x7 r r' (IN: gf r x0 x1 x2 x3 x4 x5 x6 x7) (LE: r <8= r'), gf r' x0 x1 x2 x3 x4 x5 x6 x7.

Definition _monotone8 (gf: rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7) :=
  forall r r'(LE: r <8= r'), gf r <8== gf r'.

Lemma monotone8_eq (gf: rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7) :
  monotone8 gf <-> _monotone8 gf.
Proof. unfold monotone8, _monotone8, le8. split; intros; eapply H; eassumption. Qed.

Lemma monotone8_map (gf: rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7)
      (MON: _monotone8 gf) :
  _monotone (fun R0 => @uncurry8 T0 T1 T2 T3 T4 T5 T6 T7 (gf (@curry8 T0 T1 T2 T3 T4 T5 T6 T7 R0))).
Proof.
  red; intros. apply uncurry_map8. apply MON; apply curry_map8; assumption.
Qed.

Lemma monotone8_compose (gf gf': rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7)
      (MON1: monotone8 gf)
      (MON2: monotone8 gf'):
  monotone8 (compose gf gf').
Proof.
  red; intros. eapply MON1. apply IN.
  intros. eapply MON2. apply PR. apply LE.
Qed.

Lemma monotone8_union (gf gf': rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7)
      (MON1: monotone8 gf)
      (MON2: monotone8 gf'):
  monotone8 (gf \9/ gf').
Proof.
  red; intros. destruct IN.
  - left. eapply MON1. apply H. apply LE.
  - right. eapply MON2. apply H. apply LE.
Qed.

Lemma _paco8_mon_gen (gf gf': rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7) r r'
    (LEgf: gf <9= gf')
    (LEr: r <8= r'):
  paco8 gf r <8== paco8 gf' r'.
Proof.
  apply curry_map8. red; intros. eapply paco_mon_gen. apply PR.
  - intros. apply LEgf, PR0.
  - intros. apply LEr, PR0.
Qed.

Lemma paco8_mon_gen (gf gf': rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7) r r' x0 x1 x2 x3 x4 x5 x6 x7
    (REL: paco8 gf r x0 x1 x2 x3 x4 x5 x6 x7)
    (LEgf: gf <9= gf')
    (LEr: r <8= r'):
  paco8 gf' r' x0 x1 x2 x3 x4 x5 x6 x7.
Proof.
  eapply _paco8_mon_gen; [apply LEgf | apply LEr | apply REL].
Qed.

Lemma paco8_mon_bot (gf gf': rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7) r' x0 x1 x2 x3 x4 x5 x6 x7
    (REL: paco8 gf bot8 x0 x1 x2 x3 x4 x5 x6 x7)
    (LEgf: gf <9= gf'):
  paco8 gf' r' x0 x1 x2 x3 x4 x5 x6 x7.
Proof.
  eapply paco8_mon_gen; [apply REL | apply LEgf | intros; contradiction PR].
Qed.

Lemma upaco8_mon_gen (gf gf': rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7) r r' x0 x1 x2 x3 x4 x5 x6 x7
    (REL: upaco8 gf r x0 x1 x2 x3 x4 x5 x6 x7)
    (LEgf: gf <9= gf')
    (LEr: r <8= r'):
  upaco8 gf' r' x0 x1 x2 x3 x4 x5 x6 x7.
Proof.
  destruct REL.
  - left. eapply paco8_mon_gen; [apply H | apply LEgf | apply LEr].
  - right. apply LEr, H.
Qed.

Lemma upaco8_mon_bot (gf gf': rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7) r' x0 x1 x2 x3 x4 x5 x6 x7
    (REL: upaco8 gf bot8 x0 x1 x2 x3 x4 x5 x6 x7)
    (LEgf: gf <9= gf'):
  upaco8 gf' r' x0 x1 x2 x3 x4 x5 x6 x7.
Proof.
  eapply upaco8_mon_gen; [apply REL | apply LEgf | intros; contradiction PR].
Qed.

Section Arg8.

Variable gf : rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7.
Arguments gf : clear implicits.

Theorem _paco8_mon: _monotone8 (paco8 gf).
Proof.
  red; intros. eapply curry_map8, _paco_mon; apply uncurry_map8; assumption.
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
  apply _paco_mon; intros [] H; apply H.
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
  red; intros.
  destruct IN.
  - left. eapply paco8_mon. apply H. apply LE.
  - right. apply LE, H.
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
  intro. eapply _paco8_unfold; apply monotone8_eq; assumption.
Qed.

End Arg8.

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

End PACO8.

Global Opaque paco8.

Hint Unfold upaco8 : core.
Hint Resolve paco8_fold : core.
Hint Unfold monotone8 : core.

