Require Export Program.Basics. Open Scope program_scope.
From Paco Require Import paconotation_internal paco_internal pacotac_internal.
From Paco Require Export paconotation.
Set Implicit Arguments.

Section PACO2.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.

(** ** Predicates of Arity 2
*)

Definition paco2(gf : rel2 T0 T1 -> rel2 T0 T1)(r: rel2 T0 T1) : rel2 T0 T1 :=
  @curry2 T0 T1 (paco (fun R0 => @uncurry2 T0 T1 (gf (@curry2 T0 T1 R0))) (@uncurry2 T0 T1 r)).

Definition upaco2(gf : rel2 T0 T1 -> rel2 T0 T1)(r: rel2 T0 T1) := paco2 gf r \2/ r.
Arguments paco2 : clear implicits.
Arguments upaco2 : clear implicits.
#[local] Hint Unfold upaco2 : core.

Definition monotone2 (gf: rel2 T0 T1 -> rel2 T0 T1) :=
  forall x0 x1 r r' (IN: gf r x0 x1) (LE: r <2= r'), gf r' x0 x1.

Definition _monotone2 (gf: rel2 T0 T1 -> rel2 T0 T1) :=
  forall r r'(LE: r <2= r'), gf r <2== gf r'.

Lemma monotone2_eq (gf: rel2 T0 T1 -> rel2 T0 T1) :
  monotone2 gf <-> _monotone2 gf.
Proof. unfold monotone2, _monotone2, le2. split; intros; eapply H; eassumption. Qed.

Lemma monotone2_map (gf: rel2 T0 T1 -> rel2 T0 T1)
      (MON: _monotone2 gf) :
  _monotone (fun R0 => @uncurry2 T0 T1 (gf (@curry2 T0 T1 R0))).
Proof.
  red; intros. apply uncurry_map2. apply MON; apply curry_map2; assumption.
Qed.

Lemma monotone2_compose (gf gf': rel2 T0 T1 -> rel2 T0 T1)
      (MON1: monotone2 gf)
      (MON2: monotone2 gf'):
  monotone2 (compose gf gf').
Proof.
  red; intros. eapply MON1. apply IN.
  intros. eapply MON2. apply PR. apply LE.
Qed.

Lemma monotone2_union (gf gf': rel2 T0 T1 -> rel2 T0 T1)
      (MON1: monotone2 gf)
      (MON2: monotone2 gf'):
  monotone2 (gf \3/ gf').
Proof.
  red; intros. destruct IN.
  - left. eapply MON1. apply H. apply LE.
  - right. eapply MON2. apply H. apply LE.
Qed.

Lemma _paco2_mon_gen (gf gf': rel2 T0 T1 -> rel2 T0 T1) r r'
    (LEgf: gf <3= gf')
    (LEr: r <2= r'):
  paco2 gf r <2== paco2 gf' r'.
Proof.
  apply curry_map2. red; intros. eapply paco_mon_gen. apply PR.
  - intros. apply LEgf, PR0.
  - intros. apply LEr, PR0.
Qed.

Lemma paco2_mon_gen (gf gf': rel2 T0 T1 -> rel2 T0 T1) r r' x0 x1
    (REL: paco2 gf r x0 x1)
    (LEgf: gf <3= gf')
    (LEr: r <2= r'):
  paco2 gf' r' x0 x1.
Proof.
  eapply _paco2_mon_gen; [apply LEgf | apply LEr | apply REL].
Qed.

Lemma paco2_mon_bot (gf gf': rel2 T0 T1 -> rel2 T0 T1) r' x0 x1
    (REL: paco2 gf bot2 x0 x1)
    (LEgf: gf <3= gf'):
  paco2 gf' r' x0 x1.
Proof.
  eapply paco2_mon_gen; [apply REL | apply LEgf | intros; contradiction PR].
Qed.

Lemma upaco2_mon_gen (gf gf': rel2 T0 T1 -> rel2 T0 T1) r r' x0 x1
    (REL: upaco2 gf r x0 x1)
    (LEgf: gf <3= gf')
    (LEr: r <2= r'):
  upaco2 gf' r' x0 x1.
Proof.
  destruct REL.
  - left. eapply paco2_mon_gen; [apply H | apply LEgf | apply LEr].
  - right. apply LEr, H.
Qed.

Lemma upaco2_mon_bot (gf gf': rel2 T0 T1 -> rel2 T0 T1) r' x0 x1
    (REL: upaco2 gf bot2 x0 x1)
    (LEgf: gf <3= gf'):
  upaco2 gf' r' x0 x1.
Proof.
  eapply upaco2_mon_gen; [apply REL | apply LEgf | intros; contradiction PR].
Qed.

Section Arg2.

Variable gf : rel2 T0 T1 -> rel2 T0 T1.
Arguments gf : clear implicits.

Theorem _paco2_mon: _monotone2 (paco2 gf).
Proof.
  red; intros. eapply curry_map2, _paco_mon; apply uncurry_map2; assumption.
Qed.

Theorem _paco2_acc: forall
  l r (OBG: forall rr (INC: r <2== rr) (CIH: l <2== rr), l <2== paco2 gf rr),
  l <2== paco2 gf r.
Proof.
  intros. apply uncurry_adjoint1_2.
  eapply _paco_acc. intros.
  apply uncurry_adjoint1_2 in INC. apply uncurry_adjoint1_2 in CIH.
  apply uncurry_adjoint2_2.
  eapply le2_trans. eapply (OBG _ INC CIH).
  apply curry_map2.
  apply _paco_mon; try apply le1_refl; apply curry_bij1_2.
Qed.

Theorem _paco2_mult_strong: forall r,
  paco2 gf (upaco2 gf r) <2== paco2 gf r.
Proof.
  intros. apply curry_map2.
  eapply le1_trans; [| eapply _paco_mult_strong].
  apply _paco_mon; intros [] H; apply H.
Qed.

Theorem _paco2_fold: forall r,
  gf (upaco2 gf r) <2== paco2 gf r.
Proof.
  intros. apply uncurry_adjoint1_2.
  eapply le1_trans; [| apply _paco_fold]. apply le1_refl.
Qed.

Theorem _paco2_unfold: forall (MON: _monotone2 gf) r,
  paco2 gf r <2== gf (upaco2 gf r).
Proof.
  intros. apply curry_adjoint2_2.
  eapply _paco_unfold; apply monotone2_map; assumption.
Qed.

Theorem paco2_acc: forall
  l r (OBG: forall rr (INC: r <2= rr) (CIH: l <2= rr), l <2= paco2 gf rr),
  l <2= paco2 gf r.
Proof.
  apply _paco2_acc.
Qed.

Theorem paco2_mon: monotone2 (paco2 gf).
Proof.
  apply monotone2_eq.
  apply _paco2_mon.
Qed.

Theorem upaco2_mon: monotone2 (upaco2 gf).
Proof.
  red; intros.
  destruct IN.
  - left. eapply paco2_mon. apply H. apply LE.
  - right. apply LE, H.
Qed.

Theorem paco2_mult_strong: forall r,
  paco2 gf (upaco2 gf r) <2= paco2 gf r.
Proof.
  apply _paco2_mult_strong.
Qed.

Corollary paco2_mult: forall r,
  paco2 gf (paco2 gf r) <2= paco2 gf r.
Proof. intros; eapply paco2_mult_strong, paco2_mon; [apply PR|..]; intros; left; assumption. Qed.

Theorem paco2_fold: forall r,
  gf (upaco2 gf r) <2= paco2 gf r.
Proof.
  apply _paco2_fold.
Qed.

Theorem paco2_unfold: forall (MON: monotone2 gf) r,
  paco2 gf r <2= gf (upaco2 gf r).
Proof.
  intro. eapply _paco2_unfold; apply monotone2_eq; assumption.
Qed.

End Arg2.

Arguments paco2_acc : clear implicits.
Arguments paco2_mon : clear implicits.
Arguments upaco2_mon : clear implicits.
Arguments paco2_mult_strong : clear implicits.
Arguments paco2_mult : clear implicits.
Arguments paco2_fold : clear implicits.
Arguments paco2_unfold : clear implicits.

Global Instance paco2_inst  (gf : rel2 T0 T1->_) r x0 x1 : paco_class (paco2 gf r x0 x1) :=
{ pacoacc    := paco2_acc gf;
  pacomult   := paco2_mult gf;
  pacofold   := paco2_fold gf;
  pacounfold := paco2_unfold gf }.

End PACO2.

Global Opaque paco2.

#[export] Hint Unfold upaco2 : core.
#[export] Hint Resolve paco2_fold : core.
#[export] Hint Unfold monotone2 : core.

