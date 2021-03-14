Require Export Program.Basics. Open Scope program_scope.
From Paco Require Import paconotation_internal paco_internal pacotac_internal.
From Paco Require Export paconotation.
Set Implicit Arguments.

Section PACO9.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
Variable T7 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5), Type.
Variable T8 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6), Type.

(** ** Predicates of Arity 9
*)

Definition paco9(gf : rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8)(r: rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8) : rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 :=
  @curry9 T0 T1 T2 T3 T4 T5 T6 T7 T8 (paco (fun R0 => @uncurry9 T0 T1 T2 T3 T4 T5 T6 T7 T8 (gf (@curry9 T0 T1 T2 T3 T4 T5 T6 T7 T8 R0))) (@uncurry9 T0 T1 T2 T3 T4 T5 T6 T7 T8 r)).

Definition upaco9(gf : rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8)(r: rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8) := paco9 gf r \9/ r.
Arguments paco9 : clear implicits.
Arguments upaco9 : clear implicits.
Hint Unfold upaco9 : core.

Definition monotone9 (gf: rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8) :=
  forall x0 x1 x2 x3 x4 x5 x6 x7 x8 r r' (IN: gf r x0 x1 x2 x3 x4 x5 x6 x7 x8) (LE: r <9= r'), gf r' x0 x1 x2 x3 x4 x5 x6 x7 x8.

Definition _monotone9 (gf: rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8) :=
  forall r r'(LE: r <9= r'), gf r <9== gf r'.

Lemma monotone9_eq (gf: rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8) :
  monotone9 gf <-> _monotone9 gf.
Proof. unfold monotone9, _monotone9, le9. split; intros; eapply H; eassumption. Qed.

Lemma monotone9_map (gf: rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8)
      (MON: _monotone9 gf) :
  _monotone (fun R0 => @uncurry9 T0 T1 T2 T3 T4 T5 T6 T7 T8 (gf (@curry9 T0 T1 T2 T3 T4 T5 T6 T7 T8 R0))).
Proof.
  red; intros. apply uncurry_map9. apply MON; apply curry_map9; assumption.
Qed.

Lemma monotone9_compose (gf gf': rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8)
      (MON1: monotone9 gf)
      (MON2: monotone9 gf'):
  monotone9 (compose gf gf').
Proof.
  red; intros. eapply MON1. apply IN.
  intros. eapply MON2. apply PR. apply LE.
Qed.

Lemma monotone9_union (gf gf': rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8)
      (MON1: monotone9 gf)
      (MON2: monotone9 gf'):
  monotone9 (gf \10/ gf').
Proof.
  red; intros. destruct IN.
  - left. eapply MON1. apply H. apply LE.
  - right. eapply MON2. apply H. apply LE.
Qed.

Lemma _paco9_mon_gen (gf gf': rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8) r r'
    (LEgf: gf <10= gf')
    (LEr: r <9= r'):
  paco9 gf r <9== paco9 gf' r'.
Proof.
  apply curry_map9. red; intros. eapply paco_mon_gen. apply PR.
  - intros. apply LEgf, PR0.
  - intros. apply LEr, PR0.
Qed.

Lemma paco9_mon_gen (gf gf': rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8) r r' x0 x1 x2 x3 x4 x5 x6 x7 x8
    (REL: paco9 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8)
    (LEgf: gf <10= gf')
    (LEr: r <9= r'):
  paco9 gf' r' x0 x1 x2 x3 x4 x5 x6 x7 x8.
Proof.
  eapply _paco9_mon_gen; [apply LEgf | apply LEr | apply REL].
Qed.

Lemma paco9_mon_bot (gf gf': rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8) r' x0 x1 x2 x3 x4 x5 x6 x7 x8
    (REL: paco9 gf bot9 x0 x1 x2 x3 x4 x5 x6 x7 x8)
    (LEgf: gf <10= gf'):
  paco9 gf' r' x0 x1 x2 x3 x4 x5 x6 x7 x8.
Proof.
  eapply paco9_mon_gen; [apply REL | apply LEgf | intros; contradiction PR].
Qed.

Lemma upaco9_mon_gen (gf gf': rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8) r r' x0 x1 x2 x3 x4 x5 x6 x7 x8
    (REL: upaco9 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8)
    (LEgf: gf <10= gf')
    (LEr: r <9= r'):
  upaco9 gf' r' x0 x1 x2 x3 x4 x5 x6 x7 x8.
Proof.
  destruct REL.
  - left. eapply paco9_mon_gen; [apply H | apply LEgf | apply LEr].
  - right. apply LEr, H.
Qed.

Lemma upaco9_mon_bot (gf gf': rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8) r' x0 x1 x2 x3 x4 x5 x6 x7 x8
    (REL: upaco9 gf bot9 x0 x1 x2 x3 x4 x5 x6 x7 x8)
    (LEgf: gf <10= gf'):
  upaco9 gf' r' x0 x1 x2 x3 x4 x5 x6 x7 x8.
Proof.
  eapply upaco9_mon_gen; [apply REL | apply LEgf | intros; contradiction PR].
Qed.

Section Arg9.

Variable gf : rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8.
Arguments gf : clear implicits.

Theorem _paco9_mon: _monotone9 (paco9 gf).
Proof.
  red; intros. eapply curry_map9, _paco_mon; apply uncurry_map9; assumption.
Qed.

Theorem _paco9_acc: forall
  l r (OBG: forall rr (INC: r <9== rr) (CIH: l <9== rr), l <9== paco9 gf rr),
  l <9== paco9 gf r.
Proof.
  intros. apply uncurry_adjoint1_9.
  eapply _paco_acc. intros.
  apply uncurry_adjoint1_9 in INC. apply uncurry_adjoint1_9 in CIH.
  apply uncurry_adjoint2_9.
  eapply le9_trans. eapply (OBG _ INC CIH).
  apply curry_map9.
  apply _paco_mon; try apply le1_refl; apply curry_bij1_9.
Qed.

Theorem _paco9_mult_strong: forall r,
  paco9 gf (upaco9 gf r) <9== paco9 gf r.
Proof.
  intros. apply curry_map9.
  eapply le1_trans; [| eapply _paco_mult_strong].
  apply _paco_mon; intros [] H; apply H.
Qed.

Theorem _paco9_fold: forall r,
  gf (upaco9 gf r) <9== paco9 gf r.
Proof.
  intros. apply uncurry_adjoint1_9.
  eapply le1_trans; [| apply _paco_fold]. apply le1_refl.
Qed.

Theorem _paco9_unfold: forall (MON: _monotone9 gf) r,
  paco9 gf r <9== gf (upaco9 gf r).
Proof.
  intros. apply curry_adjoint2_9.
  eapply _paco_unfold; apply monotone9_map; assumption.
Qed.

Theorem paco9_acc: forall
  l r (OBG: forall rr (INC: r <9= rr) (CIH: l <9= rr), l <9= paco9 gf rr),
  l <9= paco9 gf r.
Proof.
  apply _paco9_acc.
Qed.

Theorem paco9_mon: monotone9 (paco9 gf).
Proof.
  apply monotone9_eq.
  apply _paco9_mon.
Qed.

Theorem upaco9_mon: monotone9 (upaco9 gf).
Proof.
  red; intros.
  destruct IN.
  - left. eapply paco9_mon. apply H. apply LE.
  - right. apply LE, H.
Qed.

Theorem paco9_mult_strong: forall r,
  paco9 gf (upaco9 gf r) <9= paco9 gf r.
Proof.
  apply _paco9_mult_strong.
Qed.

Corollary paco9_mult: forall r,
  paco9 gf (paco9 gf r) <9= paco9 gf r.
Proof. intros; eapply paco9_mult_strong, paco9_mon; [apply PR|..]; intros; left; assumption. Qed.

Theorem paco9_fold: forall r,
  gf (upaco9 gf r) <9= paco9 gf r.
Proof.
  apply _paco9_fold.
Qed.

Theorem paco9_unfold: forall (MON: monotone9 gf) r,
  paco9 gf r <9= gf (upaco9 gf r).
Proof.
  intro. eapply _paco9_unfold; apply monotone9_eq; assumption.
Qed.

End Arg9.

Arguments paco9_acc : clear implicits.
Arguments paco9_mon : clear implicits.
Arguments upaco9_mon : clear implicits.
Arguments paco9_mult_strong : clear implicits.
Arguments paco9_mult : clear implicits.
Arguments paco9_fold : clear implicits.
Arguments paco9_unfold : clear implicits.

Global Instance paco9_inst  (gf : rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8->_) r x0 x1 x2 x3 x4 x5 x6 x7 x8 : paco_class (paco9 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8) :=
{ pacoacc    := paco9_acc gf;
  pacomult   := paco9_mult gf;
  pacofold   := paco9_fold gf;
  pacounfold := paco9_unfold gf }.

End PACO9.

Global Opaque paco9.

Hint Unfold upaco9 : core.
Hint Resolve paco9_fold : core.
Hint Unfold monotone9 : core.

