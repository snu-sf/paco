Require Export Program.Basics. Open Scope program_scope.
From Paco Require Import paconotation_internal paco_internal pacotac_internal.
From Paco Require Export paconotation.
Set Implicit Arguments.

Section PACO7.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.

(** ** Predicates of Arity 7
*)

Definition paco7(gf : rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6)(r: rel7 T0 T1 T2 T3 T4 T5 T6) : rel7 T0 T1 T2 T3 T4 T5 T6 :=
  @curry7 T0 T1 T2 T3 T4 T5 T6 (paco (fun R0 => @uncurry7 T0 T1 T2 T3 T4 T5 T6 (gf (@curry7 T0 T1 T2 T3 T4 T5 T6 R0))) (@uncurry7 T0 T1 T2 T3 T4 T5 T6 r)).

Definition upaco7(gf : rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6)(r: rel7 T0 T1 T2 T3 T4 T5 T6) := paco7 gf r \7/ r.
Arguments paco7 : clear implicits.
Arguments upaco7 : clear implicits.
#[local] Hint Unfold upaco7 : core.

Definition monotone7 (gf: rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6) :=
  forall x0 x1 x2 x3 x4 x5 x6 r r' (IN: gf r x0 x1 x2 x3 x4 x5 x6) (LE: r <7= r'), gf r' x0 x1 x2 x3 x4 x5 x6.

Definition _monotone7 (gf: rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6) :=
  forall r r'(LE: r <7= r'), gf r <7== gf r'.

Lemma monotone7_eq (gf: rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6) :
  monotone7 gf <-> _monotone7 gf.
Proof. unfold monotone7, _monotone7, le7. split; intros; eapply H; eassumption. Qed.

Lemma monotone7_map (gf: rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6)
      (MON: _monotone7 gf) :
  _monotone (fun R0 => @uncurry7 T0 T1 T2 T3 T4 T5 T6 (gf (@curry7 T0 T1 T2 T3 T4 T5 T6 R0))).
Proof.
  red; intros. apply uncurry_map7. apply MON; apply curry_map7; assumption.
Qed.

Lemma monotone7_compose (gf gf': rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6)
      (MON1: monotone7 gf)
      (MON2: monotone7 gf'):
  monotone7 (compose gf gf').
Proof.
  red; intros. eapply MON1. apply IN.
  intros. eapply MON2. apply PR. apply LE.
Qed.

Lemma monotone7_union (gf gf': rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6)
      (MON1: monotone7 gf)
      (MON2: monotone7 gf'):
  monotone7 (gf \8/ gf').
Proof.
  red; intros. destruct IN.
  - left. eapply MON1. apply H. apply LE.
  - right. eapply MON2. apply H. apply LE.
Qed.

Lemma _paco7_mon_gen (gf gf': rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6) r r'
    (LEgf: gf <8= gf')
    (LEr: r <7= r'):
  paco7 gf r <7== paco7 gf' r'.
Proof.
  apply curry_map7. red; intros. eapply paco_mon_gen. apply PR.
  - intros. apply LEgf, PR0.
  - intros. apply LEr, PR0.
Qed.

Lemma paco7_mon_gen (gf gf': rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6) r r' x0 x1 x2 x3 x4 x5 x6
    (REL: paco7 gf r x0 x1 x2 x3 x4 x5 x6)
    (LEgf: gf <8= gf')
    (LEr: r <7= r'):
  paco7 gf' r' x0 x1 x2 x3 x4 x5 x6.
Proof.
  eapply _paco7_mon_gen; [apply LEgf | apply LEr | apply REL].
Qed.

Lemma paco7_mon_bot (gf gf': rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6) r' x0 x1 x2 x3 x4 x5 x6
    (REL: paco7 gf bot7 x0 x1 x2 x3 x4 x5 x6)
    (LEgf: gf <8= gf'):
  paco7 gf' r' x0 x1 x2 x3 x4 x5 x6.
Proof.
  eapply paco7_mon_gen; [apply REL | apply LEgf | intros; contradiction PR].
Qed.

Lemma upaco7_mon_gen (gf gf': rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6) r r' x0 x1 x2 x3 x4 x5 x6
    (REL: upaco7 gf r x0 x1 x2 x3 x4 x5 x6)
    (LEgf: gf <8= gf')
    (LEr: r <7= r'):
  upaco7 gf' r' x0 x1 x2 x3 x4 x5 x6.
Proof.
  destruct REL.
  - left. eapply paco7_mon_gen; [apply H | apply LEgf | apply LEr].
  - right. apply LEr, H.
Qed.

Lemma upaco7_mon_bot (gf gf': rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6) r' x0 x1 x2 x3 x4 x5 x6
    (REL: upaco7 gf bot7 x0 x1 x2 x3 x4 x5 x6)
    (LEgf: gf <8= gf'):
  upaco7 gf' r' x0 x1 x2 x3 x4 x5 x6.
Proof.
  eapply upaco7_mon_gen; [apply REL | apply LEgf | intros; contradiction PR].
Qed.

Section Arg7.

Variable gf : rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6.
Arguments gf : clear implicits.

Theorem _paco7_mon: _monotone7 (paco7 gf).
Proof.
  red; intros. eapply curry_map7, _paco_mon; apply uncurry_map7; assumption.
Qed.

Theorem _paco7_acc: forall
  l r (OBG: forall rr (INC: r <7== rr) (CIH: l <7== rr), l <7== paco7 gf rr),
  l <7== paco7 gf r.
Proof.
  intros. apply uncurry_adjoint1_7.
  eapply _paco_acc. intros.
  apply uncurry_adjoint1_7 in INC. apply uncurry_adjoint1_7 in CIH.
  apply uncurry_adjoint2_7.
  eapply le7_trans. eapply (OBG _ INC CIH).
  apply curry_map7.
  apply _paco_mon; try apply le1_refl; apply curry_bij1_7.
Qed.

Theorem _paco7_mult_strong: forall r,
  paco7 gf (upaco7 gf r) <7== paco7 gf r.
Proof.
  intros. apply curry_map7.
  eapply le1_trans; [| eapply _paco_mult_strong].
  apply _paco_mon; intros [] H; apply H.
Qed.

Theorem _paco7_fold: forall r,
  gf (upaco7 gf r) <7== paco7 gf r.
Proof.
  intros. apply uncurry_adjoint1_7.
  eapply le1_trans; [| apply _paco_fold]. apply le1_refl.
Qed.

Theorem _paco7_unfold: forall (MON: _monotone7 gf) r,
  paco7 gf r <7== gf (upaco7 gf r).
Proof.
  intros. apply curry_adjoint2_7.
  eapply _paco_unfold; apply monotone7_map; assumption.
Qed.

Theorem paco7_acc: forall
  l r (OBG: forall rr (INC: r <7= rr) (CIH: l <7= rr), l <7= paco7 gf rr),
  l <7= paco7 gf r.
Proof.
  apply _paco7_acc.
Qed.

Theorem paco7_mon: monotone7 (paco7 gf).
Proof.
  apply monotone7_eq.
  apply _paco7_mon.
Qed.

Theorem upaco7_mon: monotone7 (upaco7 gf).
Proof.
  red; intros.
  destruct IN.
  - left. eapply paco7_mon. apply H. apply LE.
  - right. apply LE, H.
Qed.

Theorem paco7_mult_strong: forall r,
  paco7 gf (upaco7 gf r) <7= paco7 gf r.
Proof.
  apply _paco7_mult_strong.
Qed.

Corollary paco7_mult: forall r,
  paco7 gf (paco7 gf r) <7= paco7 gf r.
Proof. intros; eapply paco7_mult_strong, paco7_mon; [apply PR|..]; intros; left; assumption. Qed.

Theorem paco7_fold: forall r,
  gf (upaco7 gf r) <7= paco7 gf r.
Proof.
  apply _paco7_fold.
Qed.

Theorem paco7_unfold: forall (MON: monotone7 gf) r,
  paco7 gf r <7= gf (upaco7 gf r).
Proof.
  intro. eapply _paco7_unfold; apply monotone7_eq; assumption.
Qed.

End Arg7.

Arguments paco7_acc : clear implicits.
Arguments paco7_mon : clear implicits.
Arguments upaco7_mon : clear implicits.
Arguments paco7_mult_strong : clear implicits.
Arguments paco7_mult : clear implicits.
Arguments paco7_fold : clear implicits.
Arguments paco7_unfold : clear implicits.

Global Instance paco7_inst  (gf : rel7 T0 T1 T2 T3 T4 T5 T6->_) r x0 x1 x2 x3 x4 x5 x6 : paco_class (paco7 gf r x0 x1 x2 x3 x4 x5 x6) :=
{ pacoacc    := paco7_acc gf;
  pacomult   := paco7_mult gf;
  pacofold   := paco7_fold gf;
  pacounfold := paco7_unfold gf }.

End PACO7.

Global Opaque paco7.

#[export] Hint Unfold upaco7 : core.
#[export] Hint Resolve paco7_fold : core.
#[export] Hint Unfold monotone7 : core.

