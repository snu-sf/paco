Require Export Program.Basics. Open Scope program_scope.
From Paco Require Import paconotation_internal paco_internal pacotac_internal.
From Paco Require Export paconotation.
Set Implicit Arguments.

Section PACO3.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.

(** ** Predicates of Arity 3
*)

Definition paco3(gf : rel3 T0 T1 T2 -> rel3 T0 T1 T2)(r: rel3 T0 T1 T2) : rel3 T0 T1 T2 :=
  @curry3 T0 T1 T2 (paco (fun R0 => @uncurry3 T0 T1 T2 (gf (@curry3 T0 T1 T2 R0))) (@uncurry3 T0 T1 T2 r)).

Definition upaco3(gf : rel3 T0 T1 T2 -> rel3 T0 T1 T2)(r: rel3 T0 T1 T2) := paco3 gf r \3/ r.
Arguments paco3 : clear implicits.
Arguments upaco3 : clear implicits.
#[local] Hint Unfold upaco3 : core.

Definition monotone3 (gf: rel3 T0 T1 T2 -> rel3 T0 T1 T2) :=
  forall x0 x1 x2 r r' (IN: gf r x0 x1 x2) (LE: r <3= r'), gf r' x0 x1 x2.

Definition _monotone3 (gf: rel3 T0 T1 T2 -> rel3 T0 T1 T2) :=
  forall r r'(LE: r <3= r'), gf r <3== gf r'.

Lemma monotone3_eq (gf: rel3 T0 T1 T2 -> rel3 T0 T1 T2) :
  monotone3 gf <-> _monotone3 gf.
Proof. unfold monotone3, _monotone3, le3. split; intros; eapply H; eassumption. Qed.

Lemma monotone3_map (gf: rel3 T0 T1 T2 -> rel3 T0 T1 T2)
      (MON: _monotone3 gf) :
  _monotone (fun R0 => @uncurry3 T0 T1 T2 (gf (@curry3 T0 T1 T2 R0))).
Proof.
  red; intros. apply uncurry_map3. apply MON; apply curry_map3; assumption.
Qed.

Lemma monotone3_compose (gf gf': rel3 T0 T1 T2 -> rel3 T0 T1 T2)
      (MON1: monotone3 gf)
      (MON2: monotone3 gf'):
  monotone3 (compose gf gf').
Proof.
  red; intros. eapply MON1. apply IN.
  intros. eapply MON2. apply PR. apply LE.
Qed.

Lemma monotone3_union (gf gf': rel3 T0 T1 T2 -> rel3 T0 T1 T2)
      (MON1: monotone3 gf)
      (MON2: monotone3 gf'):
  monotone3 (gf \4/ gf').
Proof.
  red; intros. destruct IN.
  - left. eapply MON1. apply H. apply LE.
  - right. eapply MON2. apply H. apply LE.
Qed.

Lemma _paco3_mon_gen (gf gf': rel3 T0 T1 T2 -> rel3 T0 T1 T2) r r'
    (LEgf: gf <4= gf')
    (LEr: r <3= r'):
  paco3 gf r <3== paco3 gf' r'.
Proof.
  apply curry_map3. red; intros. eapply paco_mon_gen. apply PR.
  - intros. apply LEgf, PR0.
  - intros. apply LEr, PR0.
Qed.

Lemma paco3_mon_gen (gf gf': rel3 T0 T1 T2 -> rel3 T0 T1 T2) r r' x0 x1 x2
    (REL: paco3 gf r x0 x1 x2)
    (LEgf: gf <4= gf')
    (LEr: r <3= r'):
  paco3 gf' r' x0 x1 x2.
Proof.
  eapply _paco3_mon_gen; [apply LEgf | apply LEr | apply REL].
Qed.

Lemma paco3_mon_bot (gf gf': rel3 T0 T1 T2 -> rel3 T0 T1 T2) r' x0 x1 x2
    (REL: paco3 gf bot3 x0 x1 x2)
    (LEgf: gf <4= gf'):
  paco3 gf' r' x0 x1 x2.
Proof.
  eapply paco3_mon_gen; [apply REL | apply LEgf | intros; contradiction PR].
Qed.

Lemma upaco3_mon_gen (gf gf': rel3 T0 T1 T2 -> rel3 T0 T1 T2) r r' x0 x1 x2
    (REL: upaco3 gf r x0 x1 x2)
    (LEgf: gf <4= gf')
    (LEr: r <3= r'):
  upaco3 gf' r' x0 x1 x2.
Proof.
  destruct REL.
  - left. eapply paco3_mon_gen; [apply H | apply LEgf | apply LEr].
  - right. apply LEr, H.
Qed.

Lemma upaco3_mon_bot (gf gf': rel3 T0 T1 T2 -> rel3 T0 T1 T2) r' x0 x1 x2
    (REL: upaco3 gf bot3 x0 x1 x2)
    (LEgf: gf <4= gf'):
  upaco3 gf' r' x0 x1 x2.
Proof.
  eapply upaco3_mon_gen; [apply REL | apply LEgf | intros; contradiction PR].
Qed.

Section Arg3.

Variable gf : rel3 T0 T1 T2 -> rel3 T0 T1 T2.
Arguments gf : clear implicits.

Theorem _paco3_mon: _monotone3 (paco3 gf).
Proof.
  red; intros. eapply curry_map3, _paco_mon; apply uncurry_map3; assumption.
Qed.

Theorem _paco3_acc: forall
  l r (OBG: forall rr (INC: r <3== rr) (CIH: l <3== rr), l <3== paco3 gf rr),
  l <3== paco3 gf r.
Proof.
  intros. apply uncurry_adjoint1_3.
  eapply _paco_acc. intros.
  apply uncurry_adjoint1_3 in INC. apply uncurry_adjoint1_3 in CIH.
  apply uncurry_adjoint2_3.
  eapply le3_trans. eapply (OBG _ INC CIH).
  apply curry_map3.
  apply _paco_mon; try apply le1_refl; apply curry_bij1_3.
Qed.

Theorem _paco3_mult_strong: forall r,
  paco3 gf (upaco3 gf r) <3== paco3 gf r.
Proof.
  intros. apply curry_map3.
  eapply le1_trans; [| eapply _paco_mult_strong].
  apply _paco_mon; intros [] H; apply H.
Qed.

Theorem _paco3_fold: forall r,
  gf (upaco3 gf r) <3== paco3 gf r.
Proof.
  intros. apply uncurry_adjoint1_3.
  eapply le1_trans; [| apply _paco_fold]. apply le1_refl.
Qed.

Theorem _paco3_unfold: forall (MON: _monotone3 gf) r,
  paco3 gf r <3== gf (upaco3 gf r).
Proof.
  intros. apply curry_adjoint2_3.
  eapply _paco_unfold; apply monotone3_map; assumption.
Qed.

Theorem paco3_acc: forall
  l r (OBG: forall rr (INC: r <3= rr) (CIH: l <3= rr), l <3= paco3 gf rr),
  l <3= paco3 gf r.
Proof.
  apply _paco3_acc.
Qed.

Theorem paco3_mon: monotone3 (paco3 gf).
Proof.
  apply monotone3_eq.
  apply _paco3_mon.
Qed.

Theorem upaco3_mon: monotone3 (upaco3 gf).
Proof.
  red; intros.
  destruct IN.
  - left. eapply paco3_mon. apply H. apply LE.
  - right. apply LE, H.
Qed.

Theorem paco3_mult_strong: forall r,
  paco3 gf (upaco3 gf r) <3= paco3 gf r.
Proof.
  apply _paco3_mult_strong.
Qed.

Corollary paco3_mult: forall r,
  paco3 gf (paco3 gf r) <3= paco3 gf r.
Proof. intros; eapply paco3_mult_strong, paco3_mon; [apply PR|..]; intros; left; assumption. Qed.

Theorem paco3_fold: forall r,
  gf (upaco3 gf r) <3= paco3 gf r.
Proof.
  apply _paco3_fold.
Qed.

Theorem paco3_unfold: forall (MON: monotone3 gf) r,
  paco3 gf r <3= gf (upaco3 gf r).
Proof.
  intro. eapply _paco3_unfold; apply monotone3_eq; assumption.
Qed.

End Arg3.

Arguments paco3_acc : clear implicits.
Arguments paco3_mon : clear implicits.
Arguments upaco3_mon : clear implicits.
Arguments paco3_mult_strong : clear implicits.
Arguments paco3_mult : clear implicits.
Arguments paco3_fold : clear implicits.
Arguments paco3_unfold : clear implicits.

Global Instance paco3_inst  (gf : rel3 T0 T1 T2->_) r x0 x1 x2 : paco_class (paco3 gf r x0 x1 x2) :=
{ pacoacc    := paco3_acc gf;
  pacomult   := paco3_mult gf;
  pacofold   := paco3_fold gf;
  pacounfold := paco3_unfold gf }.

End PACO3.

Global Opaque paco3.

#[export] Hint Unfold upaco3 : core.
#[export] Hint Resolve paco3_fold : core.
#[export] Hint Unfold monotone3 : core.

