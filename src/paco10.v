Require Export Program.Basics. Open Scope program_scope.
From Paco Require Import paconotation_internal paco_internal pacotac_internal.
From Paco Require Export paconotation.
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

(** ** Predicates of Arity 10
*)

Definition paco10(gf : rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9)(r: rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) : rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 :=
  @curry10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 (paco (fun R0 => @uncurry10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 (gf (@curry10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 R0))) (@uncurry10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 r)).

Definition upaco10(gf : rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9)(r: rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) := paco10 gf r \10/ r.
Arguments paco10 : clear implicits.
Arguments upaco10 : clear implicits.
#[local] Hint Unfold upaco10 : core.

Definition monotone10 (gf: rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) :=
  forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 r r' (IN: gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (LE: r <10= r'), gf r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9.

Definition _monotone10 (gf: rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) :=
  forall r r'(LE: r <10= r'), gf r <10== gf r'.

Lemma monotone10_eq (gf: rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) :
  monotone10 gf <-> _monotone10 gf.
Proof. unfold monotone10, _monotone10, le10. split; intros; eapply H; eassumption. Qed.

Lemma monotone10_map (gf: rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9)
      (MON: _monotone10 gf) :
  _monotone (fun R0 => @uncurry10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 (gf (@curry10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 R0))).
Proof.
  red; intros. apply uncurry_map10. apply MON; apply curry_map10; assumption.
Qed.

Lemma monotone10_compose (gf gf': rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9)
      (MON1: monotone10 gf)
      (MON2: monotone10 gf'):
  monotone10 (compose gf gf').
Proof.
  red; intros. eapply MON1. apply IN.
  intros. eapply MON2. apply PR. apply LE.
Qed.

Lemma monotone10_union (gf gf': rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9)
      (MON1: monotone10 gf)
      (MON2: monotone10 gf'):
  monotone10 (gf \11/ gf').
Proof.
  red; intros. destruct IN.
  - left. eapply MON1. apply H. apply LE.
  - right. eapply MON2. apply H. apply LE.
Qed.

Lemma _paco10_mon_gen (gf gf': rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) r r'
    (LEgf: gf <11= gf')
    (LEr: r <10= r'):
  paco10 gf r <10== paco10 gf' r'.
Proof.
  apply curry_map10. red; intros. eapply paco_mon_gen. apply PR.
  - intros. apply LEgf, PR0.
  - intros. apply LEr, PR0.
Qed.

Lemma paco10_mon_gen (gf gf': rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) r r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9
    (REL: paco10 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)
    (LEgf: gf <11= gf')
    (LEr: r <10= r'):
  paco10 gf' r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9.
Proof.
  eapply _paco10_mon_gen; [apply LEgf | apply LEr | apply REL].
Qed.

Lemma paco10_mon_bot (gf gf': rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9
    (REL: paco10 gf bot10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)
    (LEgf: gf <11= gf'):
  paco10 gf' r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9.
Proof.
  eapply paco10_mon_gen; [apply REL | apply LEgf | intros; contradiction PR].
Qed.

Lemma upaco10_mon_gen (gf gf': rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) r r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9
    (REL: upaco10 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)
    (LEgf: gf <11= gf')
    (LEr: r <10= r'):
  upaco10 gf' r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9.
Proof.
  destruct REL.
  - left. eapply paco10_mon_gen; [apply H | apply LEgf | apply LEr].
  - right. apply LEr, H.
Qed.

Lemma upaco10_mon_bot (gf gf': rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9
    (REL: upaco10 gf bot10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)
    (LEgf: gf <11= gf'):
  upaco10 gf' r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9.
Proof.
  eapply upaco10_mon_gen; [apply REL | apply LEgf | intros; contradiction PR].
Qed.

Section Arg10.

Variable gf : rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9.
Arguments gf : clear implicits.

Theorem _paco10_mon: _monotone10 (paco10 gf).
Proof.
  red; intros. eapply curry_map10, _paco_mon; apply uncurry_map10; assumption.
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
  apply _paco_mon; intros [] H; apply H.
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
  red; intros.
  destruct IN.
  - left. eapply paco10_mon. apply H. apply LE.
  - right. apply LE, H.
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
  intro. eapply _paco10_unfold; apply monotone10_eq; assumption.
Qed.

End Arg10.

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

End PACO10.

Global Opaque paco10.

#[export] Hint Unfold upaco10 : core.
#[export] Hint Resolve paco10_fold : core.
#[export] Hint Unfold monotone10 : core.

