Require Export Program.Basics. Open Scope program_scope.
From Paco Require Import paconotation_internal paco_internal pacotac_internal.
From Paco Require Export paconotation.
Set Implicit Arguments.

Section PACO0.


(** ** Predicates of Arity 0
*)

Definition paco0(gf : rel0 -> rel0)(r: rel0) : rel0 :=
  @curry0 (paco (fun R0 => @uncurry0 (gf (@curry0 R0))) (@uncurry0 r)).

Definition upaco0(gf : rel0 -> rel0)(r: rel0) := paco0 gf r \0/ r.
Arguments paco0 : clear implicits.
Arguments upaco0 : clear implicits.
Hint Unfold upaco0 : core.

Definition monotone0 (gf: rel0 -> rel0) :=
  forall r r' (IN: gf r) (LE: r <0= r'), gf r'.

Definition _monotone0 (gf: rel0 -> rel0) :=
  forall r r'(LE: r <0= r'), gf r <0== gf r'.

Lemma monotone0_eq (gf: rel0 -> rel0) :
  monotone0 gf <-> _monotone0 gf.
Proof. unfold monotone0, _monotone0, le0. split; intros; eapply H; eassumption. Qed.

Lemma monotone0_map (gf: rel0 -> rel0)
      (MON: _monotone0 gf) :
  _monotone (fun R0 => @uncurry0 (gf (@curry0 R0))).
Proof.
  red; intros. apply uncurry_map0. apply MON; apply curry_map0; assumption.
Qed.

Lemma monotone0_compose (gf gf': rel0 -> rel0)
      (MON1: monotone0 gf)
      (MON2: monotone0 gf'):
  monotone0 (compose gf gf').
Proof.
  red; intros. eapply MON1. apply IN.
  intros. eapply MON2. apply PR. apply LE.
Qed.

Lemma monotone0_union (gf gf': rel0 -> rel0)
      (MON1: monotone0 gf)
      (MON2: monotone0 gf'):
  monotone0 (gf \1/ gf').
Proof.
  red; intros. destruct IN.
  - left. eapply MON1. apply H. apply LE.
  - right. eapply MON2. apply H. apply LE.
Qed.

Lemma _paco0_mon_gen (gf gf': rel0 -> rel0) r r'
    (LEgf: gf <1= gf')
    (LEr: r <0= r'):
  paco0 gf r <0== paco0 gf' r'.
Proof.
  apply curry_map0. red; intros. eapply paco_mon_gen. apply PR.
  - intros. apply LEgf, PR0.
  - intros. apply LEr, PR0.
Qed.

Lemma paco0_mon_gen (gf gf': rel0 -> rel0) r r'
    (REL: paco0 gf r)
    (LEgf: gf <1= gf')
    (LEr: r <0= r'):
  paco0 gf' r'.
Proof.
  eapply _paco0_mon_gen; [apply LEgf | apply LEr | apply REL].
Qed.

Lemma paco0_mon_bot (gf gf': rel0 -> rel0) r'
    (REL: paco0 gf bot0)
    (LEgf: gf <1= gf'):
  paco0 gf' r'.
Proof.
  eapply paco0_mon_gen; [apply REL | apply LEgf | intros; contradiction PR].
Qed.

Lemma upaco0_mon_gen (gf gf': rel0 -> rel0) r r'
    (REL: upaco0 gf r)
    (LEgf: gf <1= gf')
    (LEr: r <0= r'):
  upaco0 gf' r'.
Proof.
  destruct REL.
  - left. eapply paco0_mon_gen; [apply H | apply LEgf | apply LEr].
  - right. apply LEr, H.
Qed.

Lemma upaco0_mon_bot (gf gf': rel0 -> rel0) r'
    (REL: upaco0 gf bot0)
    (LEgf: gf <1= gf'):
  upaco0 gf' r'.
Proof.
  eapply upaco0_mon_gen; [apply REL | apply LEgf | intros; contradiction PR].
Qed.

Section Arg0.

Variable gf : rel0 -> rel0.
Arguments gf : clear implicits.

Theorem _paco0_mon: _monotone0 (paco0 gf).
Proof.
  red; intros. eapply curry_map0, _paco_mon; apply uncurry_map0; assumption.
Qed.

Theorem _paco0_acc: forall
  l r (OBG: forall rr (INC: r <0== rr) (CIH: l <0== rr), l <0== paco0 gf rr),
  l <0== paco0 gf r.
Proof.
  intros. apply uncurry_adjoint1_0.
  eapply _paco_acc. intros.
  apply uncurry_adjoint1_0 in INC. apply uncurry_adjoint1_0 in CIH.
  apply uncurry_adjoint2_0.
  eapply le0_trans. eapply (OBG _ INC CIH).
  apply curry_map0.
  apply _paco_mon; try apply le1_refl; apply curry_bij1_0.
Qed.

Theorem _paco0_mult_strong: forall r,
  paco0 gf (upaco0 gf r) <0== paco0 gf r.
Proof.
  intros. apply curry_map0.
  eapply le1_trans; [| eapply _paco_mult_strong].
  apply _paco_mon; intros [] H; apply H.
Qed.

Theorem _paco0_fold: forall r,
  gf (upaco0 gf r) <0== paco0 gf r.
Proof.
  intros. apply uncurry_adjoint1_0.
  eapply le1_trans; [| apply _paco_fold]. apply le1_refl.
Qed.

Theorem _paco0_unfold: forall (MON: _monotone0 gf) r,
  paco0 gf r <0== gf (upaco0 gf r).
Proof.
  intros. apply curry_adjoint2_0.
  eapply _paco_unfold; apply monotone0_map; assumption.
Qed.

Theorem paco0_acc: forall
  l r (OBG: forall rr (INC: r <0= rr) (CIH: l <0= rr), l <0= paco0 gf rr),
  l <0= paco0 gf r.
Proof.
  apply _paco0_acc.
Qed.

Theorem paco0_mon: monotone0 (paco0 gf).
Proof.
  apply monotone0_eq.
  apply _paco0_mon.
Qed.

Theorem upaco0_mon: monotone0 (upaco0 gf).
Proof.
  red; intros.
  destruct IN.
  - left. eapply paco0_mon. apply H. apply LE.
  - right. apply LE, H.
Qed.

Theorem paco0_mult_strong: forall r,
  paco0 gf (upaco0 gf r) <0= paco0 gf r.
Proof.
  apply _paco0_mult_strong.
Qed.

Corollary paco0_mult: forall r,
  paco0 gf (paco0 gf r) <0= paco0 gf r.
Proof. intros; eapply paco0_mult_strong, paco0_mon; [apply PR|..]; intros; left; assumption. Qed.

Theorem paco0_fold: forall r,
  gf (upaco0 gf r) <0= paco0 gf r.
Proof.
  apply _paco0_fold.
Qed.

Theorem paco0_unfold: forall (MON: monotone0 gf) r,
  paco0 gf r <0= gf (upaco0 gf r).
Proof.
  intro. eapply _paco0_unfold; apply monotone0_eq; assumption.
Qed.

End Arg0.

Arguments paco0_acc : clear implicits.
Arguments paco0_mon : clear implicits.
Arguments upaco0_mon : clear implicits.
Arguments paco0_mult_strong : clear implicits.
Arguments paco0_mult : clear implicits.
Arguments paco0_fold : clear implicits.
Arguments paco0_unfold : clear implicits.

Global Instance paco0_inst  (gf : rel0->_) r : paco_class (paco0 gf r) :=
{ pacoacc    := paco0_acc gf;
  pacomult   := paco0_mult gf;
  pacofold   := paco0_fold gf;
  pacounfold := paco0_unfold gf }.

End PACO0.

Global Opaque paco0.

Hint Unfold upaco0 : core.
Hint Resolve paco0_fold : core.
Hint Unfold monotone0 : core.

