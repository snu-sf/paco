Require Export paconotation.
Require Import paconotation_internal pacotac_internal paco_internal.
Set Implicit Arguments.

Section PACO5.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.

Local Notation curry5 := (@curry5 T0 T1 T2 T3 T4).
Local Notation uncurry5 := (@uncurry5 T0 T1 T2 T3 T4).

Lemma uncurry_map5 r0 r1 (LE : r0 <5== r1) : uncurry5 r0 <1== uncurry5 r1.
Proof. intros [] H. apply LE. apply H. Qed.

Lemma uncurry_map_rev5 r0 r1 (LE: uncurry5 r0 <1== uncurry5 r1) : r0 <5== r1.
Proof.
  repeat_intros 5. intros H. apply (LE (exist5T x4) H).
Qed.

Lemma curry_map5 r0 r1 (LE: r0 <1== r1) : curry5 r0 <5== curry5 r1.
Proof. 
  repeat_intros 5. intros H. apply (LE (exist5T x4) H).
Qed.

Lemma curry_map_rev5 r0 r1 (LE: curry5 r0 <5== curry5 r1) : r0 <1== r1.
Proof. 
  intros [] H. apply LE. apply H.
Qed.

Lemma uncurry_bij1_5 r : curry5 (uncurry5 r) <5== r.
Proof. unfold le5. repeat_intros 5. intros H. apply H. Qed.

Lemma uncurry_bij2_5 r : r <5== curry5 (uncurry5 r).
Proof. unfold le5. repeat_intros 5. intros H. apply H. Qed.

Lemma curry_bij1_5 r : uncurry5 (curry5 r) <1== r.
Proof. intros []. intro H. apply H. Qed.

Lemma curry_bij2_5 r : r <1== uncurry5 (curry5 r).
Proof. intros []. intro H. apply H. Qed.

Lemma uncurry_adjoint1_5 r0 r1 (LE: uncurry5 r0 <1== r1) : r0 <5== curry5 r1.
Proof.
  apply uncurry_map_rev5. eapply le1_trans; [apply LE|]. apply curry_bij2_5.
Qed.

Lemma uncurry_adjoint2_5 r0 r1 (LE: r0 <5== curry5 r1) : uncurry5 r0 <1== r1.
Proof.
  apply curry_map_rev5. eapply le5_trans; [|apply LE]. apply uncurry_bij2_5.
Qed.

Lemma curry_adjoint1_5 r0 r1 (LE: curry5 r0 <5== r1) : r0 <1== uncurry5 r1.
Proof.
  apply curry_map_rev5. eapply le5_trans; [apply LE|]. apply uncurry_bij2_5.
Qed.

Lemma curry_adjoint2_5 r0 r1 (LE: r0 <1== uncurry5 r1) : curry5 r0 <5== r1.
Proof.
  apply uncurry_map_rev5. eapply le1_trans; [|apply LE]. apply curry_bij1_5.
Qed.

(** ** Predicates of Arity 5
*)

Definition paco5(gf : rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4)(r: rel5 T0 T1 T2 T3 T4) : rel5 T0 T1 T2 T3 T4 :=
  curry5 (paco (fun R0 => uncurry5 (gf (curry5 R0))) (uncurry5 r)).

Definition upaco5(gf : rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4)(r: rel5 T0 T1 T2 T3 T4) := paco5 gf r \5/ r.
Arguments paco5 : clear implicits.
Arguments upaco5 : clear implicits.
Hint Unfold upaco5.

Definition monotone5 (gf: rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4) :=
  forall x0 x1 x2 x3 x4 r r' (IN: gf r x0 x1 x2 x3 x4) (LE: r <5= r'), gf r' x0 x1 x2 x3 x4.

Definition _monotone5 (gf: rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4) :=
  forall r r'(LE: r <5= r'), gf r <5== gf r'.

Lemma monotone5_eq (gf: rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4) :
  monotone5 gf <-> _monotone5 gf.
Proof. unfold monotone5, _monotone5, le5. split; intros; eapply H; eassumption. Qed.

Lemma monotone5_map (gf: rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4)
      (MON: _monotone5 gf) :
  _monotone (fun R0 => uncurry5 (gf (curry5 R0))).
Proof.
  repeat_intros 3. apply uncurry_map5. apply MON; apply curry_map5; assumption.
Qed.

Lemma _paco5_mon_gen (gf gf': rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4) r r'
    (LEgf: gf <6= gf')
    (LEr: r <5= r'):
  paco5 gf r <5== paco5 gf' r'.
Proof.
  apply curry_map5. red; intros. eapply paco_mon_gen. apply PR.
  - intros. apply LEgf, PR0.
  - intros. apply LEr, PR0.
Qed.

Lemma paco5_mon_gen (gf gf': rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4) r r' x0 x1 x2 x3 x4
    (REL: paco5 gf r x0 x1 x2 x3 x4)
    (LEgf: gf <6= gf')
    (LEr: r <5= r'):
  paco5 gf' r' x0 x1 x2 x3 x4.
Proof.
  eapply _paco5_mon_gen; [apply LEgf | apply LEr | apply REL].
Qed.

Lemma paco5_mon_bot (gf gf': rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4) r' x0 x1 x2 x3 x4
    (REL: paco5 gf bot5 x0 x1 x2 x3 x4)
    (LEgf: gf <6= gf'):
  paco5 gf' r' x0 x1 x2 x3 x4.
Proof.
  eapply paco5_mon_gen; [apply REL | apply LEgf | intros; contradiction PR].
Qed.

Lemma upaco5_mon_gen (gf gf': rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4) r r' x0 x1 x2 x3 x4
    (REL: upaco5 gf r x0 x1 x2 x3 x4)
    (LEgf: gf <6= gf')
    (LEr: r <5= r'):
  upaco5 gf' r' x0 x1 x2 x3 x4.
Proof.
  destruct REL.
  - left. eapply paco5_mon_gen; [apply H | apply LEgf | apply LEr].
  - right. apply LEr, H.
Qed.

Lemma upaco5_mon_bot (gf gf': rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4) r' x0 x1 x2 x3 x4
    (REL: upaco5 gf bot5 x0 x1 x2 x3 x4)
    (LEgf: gf <6= gf'):
  upaco5 gf' r' x0 x1 x2 x3 x4.
Proof.
  eapply upaco5_mon_gen; [apply REL | apply LEgf | intros; contradiction PR].
Qed.

Section Arg5.

Variable gf : rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4.
Arguments gf : clear implicits.

Theorem _paco5_mon: _monotone5 (paco5 gf).
Proof.
  repeat_intros 3. eapply curry_map5, _paco_mon; apply uncurry_map5; assumption.
Qed.

Theorem _paco5_acc: forall
  l r (OBG: forall rr (INC: r <5== rr) (CIH: l <5== rr), l <5== paco5 gf rr),
  l <5== paco5 gf r.
Proof.
  intros. apply uncurry_adjoint1_5.
  eapply _paco_acc. intros.
  apply uncurry_adjoint1_5 in INC. apply uncurry_adjoint1_5 in CIH.
  apply uncurry_adjoint2_5.
  eapply le5_trans. eapply (OBG _ INC CIH).
  apply curry_map5.
  apply _paco_mon; try apply le1_refl; apply curry_bij1_5.
Qed.

Theorem _paco5_mult_strong: forall r,
  paco5 gf (upaco5 gf r) <5== paco5 gf r.
Proof.
  intros. apply curry_map5.
  eapply le1_trans; [| eapply _paco_mult_strong].
  apply _paco_mon; intros []; intros H; apply H.
Qed.

Theorem _paco5_fold: forall r,
  gf (upaco5 gf r) <5== paco5 gf r.
Proof.
  intros. apply uncurry_adjoint1_5.
  eapply le1_trans; [| apply _paco_fold]. apply le1_refl.
Qed.

Theorem _paco5_unfold: forall (MON: _monotone5 gf) r,
  paco5 gf r <5== gf (upaco5 gf r).
Proof.
  intros. apply curry_adjoint2_5.
  eapply _paco_unfold; apply monotone5_map; assumption.
Qed.

Theorem paco5_acc: forall
  l r (OBG: forall rr (INC: r <5= rr) (CIH: l <5= rr), l <5= paco5 gf rr),
  l <5= paco5 gf r.
Proof.
  apply _paco5_acc.
Qed.

Theorem paco5_mon: monotone5 (paco5 gf).
Proof.
  apply monotone5_eq.
  apply _paco5_mon.
Qed.

Theorem upaco5_mon: monotone5 (upaco5 gf).
Proof.
  repeat_intros 7. intros R  LE0.
  destruct R.
  - left. eapply paco5_mon. apply H. apply LE0.
  - right. apply LE0, H.
Qed.

Theorem paco5_mult_strong: forall r,
  paco5 gf (upaco5 gf r) <5= paco5 gf r.
Proof.
  apply _paco5_mult_strong.
Qed.

Corollary paco5_mult: forall r,
  paco5 gf (paco5 gf r) <5= paco5 gf r.
Proof. intros; eapply paco5_mult_strong, paco5_mon; [apply PR|..]; intros; left; assumption. Qed.

Theorem paco5_fold: forall r,
  gf (upaco5 gf r) <5= paco5 gf r.
Proof.
  apply _paco5_fold.
Qed.

Theorem paco5_unfold: forall (MON: monotone5 gf) r,
  paco5 gf r <5= gf (upaco5 gf r).
Proof.
  repeat_intros 1. eapply _paco5_unfold; apply monotone5_eq; assumption.
Qed.

End Arg5.

Arguments paco5_acc : clear implicits.
Arguments paco5_mon : clear implicits.
Arguments upaco5_mon : clear implicits.
Arguments paco5_mult_strong : clear implicits.
Arguments paco5_mult : clear implicits.
Arguments paco5_fold : clear implicits.
Arguments paco5_unfold : clear implicits.

Global Instance paco5_inst  (gf : rel5 T0 T1 T2 T3 T4->_) r x0 x1 x2 x3 x4 : paco_class (paco5 gf r x0 x1 x2 x3 x4) :=
{ pacoacc    := paco5_acc gf;
  pacomult   := paco5_mult gf;
  pacofold   := paco5_fold gf;
  pacounfold := paco5_unfold gf }.

End PACO5.

Global Opaque paco5.

Hint Unfold upaco5.
Hint Resolve paco5_fold.
Hint Unfold monotone5.

