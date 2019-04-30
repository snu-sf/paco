Require Export Program.Basics. Open Scope program_scope.
Require Import paconotation_internal paco_internal pacotac_internal.
Require Export paconotation.
Set Implicit Arguments.

Section PACO11.

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

(** ** Signatures *)

Record sig11T  :=
  exist11T {
      proj11T0: @T0;
      proj11T1: @T1 proj11T0;
      proj11T2: @T2 proj11T0 proj11T1;
      proj11T3: @T3 proj11T0 proj11T1 proj11T2;
      proj11T4: @T4 proj11T0 proj11T1 proj11T2 proj11T3;
      proj11T5: @T5 proj11T0 proj11T1 proj11T2 proj11T3 proj11T4;
      proj11T6: @T6 proj11T0 proj11T1 proj11T2 proj11T3 proj11T4 proj11T5;
      proj11T7: @T7 proj11T0 proj11T1 proj11T2 proj11T3 proj11T4 proj11T5 proj11T6;
      proj11T8: @T8 proj11T0 proj11T1 proj11T2 proj11T3 proj11T4 proj11T5 proj11T6 proj11T7;
      proj11T9: @T9 proj11T0 proj11T1 proj11T2 proj11T3 proj11T4 proj11T5 proj11T6 proj11T7 proj11T8;
      proj11T10: @T10 proj11T0 proj11T1 proj11T2 proj11T3 proj11T4 proj11T5 proj11T6 proj11T7 proj11T8 proj11T9;
    }.
Definition uncurry11  (R: rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10): rel1 sig11T :=
  fun x => R (proj11T0 x) (proj11T1 x) (proj11T2 x) (proj11T3 x) (proj11T4 x) (proj11T5 x) (proj11T6 x) (proj11T7 x) (proj11T8 x) (proj11T9 x) (proj11T10 x).
Definition curry11  (R: rel1 sig11T): rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 :=
  fun x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 => R (@exist11T x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10).

Lemma uncurry_map11 r0 r1 (LE : r0 <11== r1) : uncurry11 r0 <1== uncurry11 r1.
Proof. intros [] H. apply LE. apply H. Qed.

Lemma uncurry_map_rev11 r0 r1 (LE: uncurry11 r0 <1== uncurry11 r1) : r0 <11== r1.
Proof.
  red; intros. apply (LE (@exist11T x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) PR).
Qed.

Lemma curry_map11 r0 r1 (LE: r0 <1== r1) : curry11 r0 <11== curry11 r1.
Proof. 
  red; intros. apply (LE (@exist11T x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) PR).
Qed.

Lemma curry_map_rev11 r0 r1 (LE: curry11 r0 <11== curry11 r1) : r0 <1== r1.
Proof. 
  intros [] H. apply LE. apply H.
Qed.

Lemma uncurry_bij1_11 r : curry11 (uncurry11 r) <11== r.
Proof. unfold le11. intros. apply PR. Qed.

Lemma uncurry_bij2_11 r : r <11== curry11 (uncurry11 r).
Proof. unfold le11. intros. apply PR. Qed.

Lemma curry_bij1_11 r : uncurry11 (curry11 r) <1== r.
Proof. intros []. intro H. apply H. Qed.

Lemma curry_bij2_11 r : r <1== uncurry11 (curry11 r).
Proof. intros []. intro H. apply H. Qed.

Lemma uncurry_adjoint1_11 r0 r1 (LE: uncurry11 r0 <1== r1) : r0 <11== curry11 r1.
Proof.
  apply uncurry_map_rev11. eapply le1_trans; [apply LE|]. apply curry_bij2_11.
Qed.

Lemma uncurry_adjoint2_11 r0 r1 (LE: r0 <11== curry11 r1) : uncurry11 r0 <1== r1.
Proof.
  apply curry_map_rev11. eapply le11_trans; [|apply LE]. apply uncurry_bij2_11.
Qed.

Lemma curry_adjoint1_11 r0 r1 (LE: curry11 r0 <11== r1) : r0 <1== uncurry11 r1.
Proof.
  apply curry_map_rev11. eapply le11_trans; [apply LE|]. apply uncurry_bij2_11.
Qed.

Lemma curry_adjoint2_11 r0 r1 (LE: r0 <1== uncurry11 r1) : curry11 r0 <11== r1.
Proof.
  apply uncurry_map_rev11. eapply le1_trans; [|apply LE]. apply curry_bij1_11.
Qed.

(** ** Predicates of Arity 11
*)

Definition paco11(gf : rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10)(r: rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10) : rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 :=
  curry11 (paco (fun R0 => uncurry11 (gf (curry11 R0))) (uncurry11 r)).

Definition upaco11(gf : rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10)(r: rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10) := paco11 gf r \11/ r.
Arguments paco11 : clear implicits.
Arguments upaco11 : clear implicits.
Hint Unfold upaco11.

Definition monotone11 (gf: rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10) :=
  forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 r r' (IN: gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) (LE: r <11= r'), gf r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10.

Definition _monotone11 (gf: rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10) :=
  forall r r'(LE: r <11= r'), gf r <11== gf r'.

Lemma monotone11_eq (gf: rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10) :
  monotone11 gf <-> _monotone11 gf.
Proof. unfold monotone11, _monotone11, le11. split; intros; eapply H; eassumption. Qed.

Lemma monotone11_map (gf: rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10)
      (MON: _monotone11 gf) :
  _monotone (fun R0 => uncurry11 (gf (curry11 R0))).
Proof.
  red; intros. apply uncurry_map11. apply MON; apply curry_map11; assumption.
Qed.

Lemma monotone11_compose (gf gf': rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10)
      (MON1: monotone11 gf)
      (MON2: monotone11 gf'):
  monotone11 (compose gf gf').
Proof.
  red; intros. eapply MON1. apply IN.
  intros. eapply MON2. apply PR. apply LE.
Qed.

Lemma monotone11_union (gf gf': rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10)
      (MON1: monotone11 gf)
      (MON2: monotone11 gf'):
  monotone11 (gf \12/ gf').
Proof.
  red; intros. destruct IN.
  - left. eapply MON1. apply H. apply LE.
  - right. eapply MON2. apply H. apply LE.
Qed.

Lemma _paco11_mon_gen (gf gf': rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10) r r'
    (LEgf: gf <12= gf')
    (LEr: r <11= r'):
  paco11 gf r <11== paco11 gf' r'.
Proof.
  apply curry_map11. red; intros. eapply paco_mon_gen. apply PR.
  - intros. apply LEgf, PR0.
  - intros. apply LEr, PR0.
Qed.

Lemma paco11_mon_gen (gf gf': rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10) r r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
    (REL: paco11 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
    (LEgf: gf <12= gf')
    (LEr: r <11= r'):
  paco11 gf' r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10.
Proof.
  eapply _paco11_mon_gen; [apply LEgf | apply LEr | apply REL].
Qed.

Lemma paco11_mon_bot (gf gf': rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10) r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
    (REL: paco11 gf bot11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
    (LEgf: gf <12= gf'):
  paco11 gf' r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10.
Proof.
  eapply paco11_mon_gen; [apply REL | apply LEgf | intros; contradiction PR].
Qed.

Lemma upaco11_mon_gen (gf gf': rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10) r r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
    (REL: upaco11 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
    (LEgf: gf <12= gf')
    (LEr: r <11= r'):
  upaco11 gf' r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10.
Proof.
  destruct REL.
  - left. eapply paco11_mon_gen; [apply H | apply LEgf | apply LEr].
  - right. apply LEr, H.
Qed.

Lemma upaco11_mon_bot (gf gf': rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10) r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
    (REL: upaco11 gf bot11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
    (LEgf: gf <12= gf'):
  upaco11 gf' r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10.
Proof.
  eapply upaco11_mon_gen; [apply REL | apply LEgf | intros; contradiction PR].
Qed.

Section Arg11.

Variable gf : rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10.
Arguments gf : clear implicits.

Theorem _paco11_mon: _monotone11 (paco11 gf).
Proof.
  red; intros. eapply curry_map11, _paco_mon; apply uncurry_map11; assumption.
Qed.

Theorem _paco11_acc: forall
  l r (OBG: forall rr (INC: r <11== rr) (CIH: l <11== rr), l <11== paco11 gf rr),
  l <11== paco11 gf r.
Proof.
  intros. apply uncurry_adjoint1_11.
  eapply _paco_acc. intros.
  apply uncurry_adjoint1_11 in INC. apply uncurry_adjoint1_11 in CIH.
  apply uncurry_adjoint2_11.
  eapply le11_trans. eapply (OBG _ INC CIH).
  apply curry_map11.
  apply _paco_mon; try apply le1_refl; apply curry_bij1_11.
Qed.

Theorem _paco11_mult_strong: forall r,
  paco11 gf (upaco11 gf r) <11== paco11 gf r.
Proof.
  intros. apply curry_map11.
  eapply le1_trans; [| eapply _paco_mult_strong].
  apply _paco_mon; intros []; intros H; apply H.
Qed.

Theorem _paco11_fold: forall r,
  gf (upaco11 gf r) <11== paco11 gf r.
Proof.
  intros. apply uncurry_adjoint1_11.
  eapply le1_trans; [| apply _paco_fold]. apply le1_refl.
Qed.

Theorem _paco11_unfold: forall (MON: _monotone11 gf) r,
  paco11 gf r <11== gf (upaco11 gf r).
Proof.
  intros. apply curry_adjoint2_11.
  eapply _paco_unfold; apply monotone11_map; assumption.
Qed.

Theorem paco11_acc: forall
  l r (OBG: forall rr (INC: r <11= rr) (CIH: l <11= rr), l <11= paco11 gf rr),
  l <11= paco11 gf r.
Proof.
  apply _paco11_acc.
Qed.

Theorem paco11_mon: monotone11 (paco11 gf).
Proof.
  apply monotone11_eq.
  apply _paco11_mon.
Qed.

Theorem upaco11_mon: monotone11 (upaco11 gf).
Proof.
  red; intros.
  destruct IN.
  - left. eapply paco11_mon. apply H. apply LE.
  - right. apply LE, H.
Qed.

Theorem paco11_mult_strong: forall r,
  paco11 gf (upaco11 gf r) <11= paco11 gf r.
Proof.
  apply _paco11_mult_strong.
Qed.

Corollary paco11_mult: forall r,
  paco11 gf (paco11 gf r) <11= paco11 gf r.
Proof. intros; eapply paco11_mult_strong, paco11_mon; [apply PR|..]; intros; left; assumption. Qed.

Theorem paco11_fold: forall r,
  gf (upaco11 gf r) <11= paco11 gf r.
Proof.
  apply _paco11_fold.
Qed.

Theorem paco11_unfold: forall (MON: monotone11 gf) r,
  paco11 gf r <11= gf (upaco11 gf r).
Proof.
  intro. eapply _paco11_unfold; apply monotone11_eq; assumption.
Qed.

End Arg11.

Arguments paco11_acc : clear implicits.
Arguments paco11_mon : clear implicits.
Arguments upaco11_mon : clear implicits.
Arguments paco11_mult_strong : clear implicits.
Arguments paco11_mult : clear implicits.
Arguments paco11_fold : clear implicits.
Arguments paco11_unfold : clear implicits.

Global Instance paco11_inst  (gf : rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10->_) r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : paco_class (paco11 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) :=
{ pacoacc    := paco11_acc gf;
  pacomult   := paco11_mult gf;
  pacofold   := paco11_fold gf;
  pacounfold := paco11_unfold gf }.

End PACO11.

Global Opaque paco11.

Hint Unfold upaco11.
Hint Resolve paco11_fold.
Hint Unfold monotone11.

