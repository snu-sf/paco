Require Export Program.Basics. Open Scope program_scope.
From Paco Require Import paconotation_internal paco_internal pacotac_internal.
From Paco Require Export paconotation.
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

(** ** Predicates of Arity 12
*)

Definition paco12(gf : rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11)(r: rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11) : rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 :=
  @curry12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 (paco (fun R0 => @uncurry12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 (gf (@curry12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 R0))) (@uncurry12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 r)).

Definition upaco12(gf : rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11)(r: rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11) := paco12 gf r \12/ r.
Arguments paco12 : clear implicits.
Arguments upaco12 : clear implicits.
#[local] Hint Unfold upaco12 : core.

Definition monotone12 (gf: rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11) :=
  forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 r r' (IN: gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) (LE: r <12= r'), gf r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11.

Definition _monotone12 (gf: rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11) :=
  forall r r'(LE: r <12= r'), gf r <12== gf r'.

Lemma monotone12_eq (gf: rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11) :
  monotone12 gf <-> _monotone12 gf.
Proof. unfold monotone12, _monotone12, le12. split; intros; eapply H; eassumption. Qed.

Lemma monotone12_map (gf: rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11)
      (MON: _monotone12 gf) :
  _monotone (fun R0 => @uncurry12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 (gf (@curry12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 R0))).
Proof.
  red; intros. apply uncurry_map12. apply MON; apply curry_map12; assumption.
Qed.

Lemma monotone12_compose (gf gf': rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11)
      (MON1: monotone12 gf)
      (MON2: monotone12 gf'):
  monotone12 (compose gf gf').
Proof.
  red; intros. eapply MON1. apply IN.
  intros. eapply MON2. apply PR. apply LE.
Qed.

Lemma monotone12_union (gf gf': rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11)
      (MON1: monotone12 gf)
      (MON2: monotone12 gf'):
  monotone12 (gf \13/ gf').
Proof.
  red; intros. destruct IN.
  - left. eapply MON1. apply H. apply LE.
  - right. eapply MON2. apply H. apply LE.
Qed.

Lemma _paco12_mon_gen (gf gf': rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11) r r'
    (LEgf: gf <13= gf')
    (LEr: r <12= r'):
  paco12 gf r <12== paco12 gf' r'.
Proof.
  apply curry_map12. red; intros. eapply paco_mon_gen. apply PR.
  - intros. apply LEgf, PR0.
  - intros. apply LEr, PR0.
Qed.

Lemma paco12_mon_gen (gf gf': rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11) r r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11
    (REL: paco12 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)
    (LEgf: gf <13= gf')
    (LEr: r <12= r'):
  paco12 gf' r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11.
Proof.
  eapply _paco12_mon_gen; [apply LEgf | apply LEr | apply REL].
Qed.

Lemma paco12_mon_bot (gf gf': rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11) r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11
    (REL: paco12 gf bot12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)
    (LEgf: gf <13= gf'):
  paco12 gf' r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11.
Proof.
  eapply paco12_mon_gen; [apply REL | apply LEgf | intros; contradiction PR].
Qed.

Lemma upaco12_mon_gen (gf gf': rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11) r r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11
    (REL: upaco12 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)
    (LEgf: gf <13= gf')
    (LEr: r <12= r'):
  upaco12 gf' r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11.
Proof.
  destruct REL.
  - left. eapply paco12_mon_gen; [apply H | apply LEgf | apply LEr].
  - right. apply LEr, H.
Qed.

Lemma upaco12_mon_bot (gf gf': rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11) r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11
    (REL: upaco12 gf bot12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)
    (LEgf: gf <13= gf'):
  upaco12 gf' r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11.
Proof.
  eapply upaco12_mon_gen; [apply REL | apply LEgf | intros; contradiction PR].
Qed.

Section Arg12.

Variable gf : rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11.
Arguments gf : clear implicits.

Theorem _paco12_mon: _monotone12 (paco12 gf).
Proof.
  red; intros. eapply curry_map12, _paco_mon; apply uncurry_map12; assumption.
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
  apply _paco_mon; intros [] H; apply H.
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
  eapply _paco_unfold; apply monotone12_map; assumption.
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

Theorem upaco12_mon: monotone12 (upaco12 gf).
Proof.
  red; intros.
  destruct IN.
  - left. eapply paco12_mon. apply H. apply LE.
  - right. apply LE, H.
Qed.

Theorem paco12_mult_strong: forall r,
  paco12 gf (upaco12 gf r) <12= paco12 gf r.
Proof.
  apply _paco12_mult_strong.
Qed.

Corollary paco12_mult: forall r,
  paco12 gf (paco12 gf r) <12= paco12 gf r.
Proof. intros; eapply paco12_mult_strong, paco12_mon; [apply PR|..]; intros; left; assumption. Qed.

Theorem paco12_fold: forall r,
  gf (upaco12 gf r) <12= paco12 gf r.
Proof.
  apply _paco12_fold.
Qed.

Theorem paco12_unfold: forall (MON: monotone12 gf) r,
  paco12 gf r <12= gf (upaco12 gf r).
Proof.
  intro. eapply _paco12_unfold; apply monotone12_eq; assumption.
Qed.

End Arg12.

Arguments paco12_acc : clear implicits.
Arguments paco12_mon : clear implicits.
Arguments upaco12_mon : clear implicits.
Arguments paco12_mult_strong : clear implicits.
Arguments paco12_mult : clear implicits.
Arguments paco12_fold : clear implicits.
Arguments paco12_unfold : clear implicits.

Global Instance paco12_inst  (gf : rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11->_) r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : paco_class (paco12 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) :=
{ pacoacc    := paco12_acc gf;
  pacomult   := paco12_mult gf;
  pacofold   := paco12_fold gf;
  pacounfold := paco12_unfold gf }.

End PACO12.

Global Opaque paco12.

#[export] Hint Unfold upaco12 : core.
#[export] Hint Resolve paco12_fold : core.
#[export] Hint Unfold monotone12 : core.

