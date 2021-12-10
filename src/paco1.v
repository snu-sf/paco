Require Export Program.Basics. Open Scope program_scope.
From Paco Require Import paconotation_internal paco_internal pacotac_internal.
From Paco Require Export paconotation.
Set Implicit Arguments.

Section PACO1.

Variable T0 : Type.

(** ** Predicates of Arity 1
*)

Definition paco1(gf : rel1 T0 -> rel1 T0)(r: rel1 T0) : rel1 T0 :=
  @curry1 T0 (paco (fun R0 => @uncurry1 T0 (gf (@curry1 T0 R0))) (@uncurry1 T0 r)).

Definition upaco1(gf : rel1 T0 -> rel1 T0)(r: rel1 T0) := paco1 gf r \1/ r.
Arguments paco1 : clear implicits.
Arguments upaco1 : clear implicits.
#[local] Hint Unfold upaco1 : core.

Definition monotone1 (gf: rel1 T0 -> rel1 T0) :=
  forall x0 r r' (IN: gf r x0) (LE: r <1= r'), gf r' x0.

Definition _monotone1 (gf: rel1 T0 -> rel1 T0) :=
  forall r r'(LE: r <1= r'), gf r <1== gf r'.

Lemma monotone1_eq (gf: rel1 T0 -> rel1 T0) :
  monotone1 gf <-> _monotone1 gf.
Proof. unfold monotone1, _monotone1, le1. split; intros; eapply H; eassumption. Qed.

Lemma monotone1_map (gf: rel1 T0 -> rel1 T0)
      (MON: _monotone1 gf) :
  _monotone (fun R0 => @uncurry1 T0 (gf (@curry1 T0 R0))).
Proof.
  red; intros. apply uncurry_map1. apply MON; apply curry_map1; assumption.
Qed.

Lemma monotone1_compose (gf gf': rel1 T0 -> rel1 T0)
      (MON1: monotone1 gf)
      (MON2: monotone1 gf'):
  monotone1 (compose gf gf').
Proof.
  red; intros. eapply MON1. apply IN.
  intros. eapply MON2. apply PR. apply LE.
Qed.

Lemma monotone1_union (gf gf': rel1 T0 -> rel1 T0)
      (MON1: monotone1 gf)
      (MON2: monotone1 gf'):
  monotone1 (gf \2/ gf').
Proof.
  red; intros. destruct IN.
  - left. eapply MON1. apply H. apply LE.
  - right. eapply MON2. apply H. apply LE.
Qed.

Lemma _paco1_mon_gen (gf gf': rel1 T0 -> rel1 T0) r r'
    (LEgf: gf <2= gf')
    (LEr: r <1= r'):
  paco1 gf r <1== paco1 gf' r'.
Proof.
  apply curry_map1. red; intros. eapply paco_mon_gen. apply PR.
  - intros. apply LEgf, PR0.
  - intros. apply LEr, PR0.
Qed.

Lemma paco1_mon_gen (gf gf': rel1 T0 -> rel1 T0) r r' x0
    (REL: paco1 gf r x0)
    (LEgf: gf <2= gf')
    (LEr: r <1= r'):
  paco1 gf' r' x0.
Proof.
  eapply _paco1_mon_gen; [apply LEgf | apply LEr | apply REL].
Qed.

Lemma paco1_mon_bot (gf gf': rel1 T0 -> rel1 T0) r' x0
    (REL: paco1 gf bot1 x0)
    (LEgf: gf <2= gf'):
  paco1 gf' r' x0.
Proof.
  eapply paco1_mon_gen; [apply REL | apply LEgf | intros; contradiction PR].
Qed.

Lemma upaco1_mon_gen (gf gf': rel1 T0 -> rel1 T0) r r' x0
    (REL: upaco1 gf r x0)
    (LEgf: gf <2= gf')
    (LEr: r <1= r'):
  upaco1 gf' r' x0.
Proof.
  destruct REL.
  - left. eapply paco1_mon_gen; [apply H | apply LEgf | apply LEr].
  - right. apply LEr, H.
Qed.

Lemma upaco1_mon_bot (gf gf': rel1 T0 -> rel1 T0) r' x0
    (REL: upaco1 gf bot1 x0)
    (LEgf: gf <2= gf'):
  upaco1 gf' r' x0.
Proof.
  eapply upaco1_mon_gen; [apply REL | apply LEgf | intros; contradiction PR].
Qed.

Section Arg1.

Variable gf : rel1 T0 -> rel1 T0.
Arguments gf : clear implicits.

Theorem _paco1_mon: _monotone1 (paco1 gf).
Proof.
  red; intros. eapply curry_map1, _paco_mon; apply uncurry_map1; assumption.
Qed.

Theorem _paco1_acc: forall
  l r (OBG: forall rr (INC: r <1== rr) (CIH: l <1== rr), l <1== paco1 gf rr),
  l <1== paco1 gf r.
Proof.
  intros. apply uncurry_adjoint1_1.
  eapply _paco_acc. intros.
  apply uncurry_adjoint1_1 in INC. apply uncurry_adjoint1_1 in CIH.
  apply uncurry_adjoint2_1.
  eapply le1_trans. eapply (OBG _ INC CIH).
  apply curry_map1.
  apply _paco_mon; try apply le1_refl; apply curry_bij1_1.
Qed.

Theorem _paco1_mult_strong: forall r,
  paco1 gf (upaco1 gf r) <1== paco1 gf r.
Proof.
  intros. apply curry_map1.
  eapply le1_trans; [| eapply _paco_mult_strong].
  apply _paco_mon; intros [] H; apply H.
Qed.

Theorem _paco1_fold: forall r,
  gf (upaco1 gf r) <1== paco1 gf r.
Proof.
  intros. apply uncurry_adjoint1_1.
  eapply le1_trans; [| apply _paco_fold]. apply le1_refl.
Qed.

Theorem _paco1_unfold: forall (MON: _monotone1 gf) r,
  paco1 gf r <1== gf (upaco1 gf r).
Proof.
  intros. apply curry_adjoint2_1.
  eapply _paco_unfold; apply monotone1_map; assumption.
Qed.

Theorem paco1_acc: forall
  l r (OBG: forall rr (INC: r <1= rr) (CIH: l <1= rr), l <1= paco1 gf rr),
  l <1= paco1 gf r.
Proof.
  apply _paco1_acc.
Qed.

Theorem paco1_mon: monotone1 (paco1 gf).
Proof.
  apply monotone1_eq.
  apply _paco1_mon.
Qed.

Theorem upaco1_mon: monotone1 (upaco1 gf).
Proof.
  red; intros.
  destruct IN.
  - left. eapply paco1_mon. apply H. apply LE.
  - right. apply LE, H.
Qed.

Theorem paco1_mult_strong: forall r,
  paco1 gf (upaco1 gf r) <1= paco1 gf r.
Proof.
  apply _paco1_mult_strong.
Qed.

Corollary paco1_mult: forall r,
  paco1 gf (paco1 gf r) <1= paco1 gf r.
Proof. intros; eapply paco1_mult_strong, paco1_mon; [apply PR|..]; intros; left; assumption. Qed.

Theorem paco1_fold: forall r,
  gf (upaco1 gf r) <1= paco1 gf r.
Proof.
  apply _paco1_fold.
Qed.

Theorem paco1_unfold: forall (MON: monotone1 gf) r,
  paco1 gf r <1= gf (upaco1 gf r).
Proof.
  intro. eapply _paco1_unfold; apply monotone1_eq; assumption.
Qed.

End Arg1.

Arguments paco1_acc : clear implicits.
Arguments paco1_mon : clear implicits.
Arguments upaco1_mon : clear implicits.
Arguments paco1_mult_strong : clear implicits.
Arguments paco1_mult : clear implicits.
Arguments paco1_fold : clear implicits.
Arguments paco1_unfold : clear implicits.

Global Instance paco1_inst  (gf : rel1 T0->_) r x0 : paco_class (paco1 gf r x0) :=
{ pacoacc    := paco1_acc gf;
  pacomult   := paco1_mult gf;
  pacofold   := paco1_fold gf;
  pacounfold := paco1_unfold gf }.

End PACO1.

Global Opaque paco1.

#[export] Hint Unfold upaco1 : core.
#[export] Hint Resolve paco1_fold : core.
#[export] Hint Unfold monotone1 : core.

