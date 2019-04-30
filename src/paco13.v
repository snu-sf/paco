Require Export Program.Basics. Open Scope program_scope.
Require Import paconotation_internal paco_internal pacotac_internal.
Require Export paconotation.
Set Implicit Arguments.

Section PACO13.

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
Variable T12 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10), Type.

(** ** Signatures *)

Record sig13T  :=
  exist13T {
      proj13T0: @T0;
      proj13T1: @T1 proj13T0;
      proj13T2: @T2 proj13T0 proj13T1;
      proj13T3: @T3 proj13T0 proj13T1 proj13T2;
      proj13T4: @T4 proj13T0 proj13T1 proj13T2 proj13T3;
      proj13T5: @T5 proj13T0 proj13T1 proj13T2 proj13T3 proj13T4;
      proj13T6: @T6 proj13T0 proj13T1 proj13T2 proj13T3 proj13T4 proj13T5;
      proj13T7: @T7 proj13T0 proj13T1 proj13T2 proj13T3 proj13T4 proj13T5 proj13T6;
      proj13T8: @T8 proj13T0 proj13T1 proj13T2 proj13T3 proj13T4 proj13T5 proj13T6 proj13T7;
      proj13T9: @T9 proj13T0 proj13T1 proj13T2 proj13T3 proj13T4 proj13T5 proj13T6 proj13T7 proj13T8;
      proj13T10: @T10 proj13T0 proj13T1 proj13T2 proj13T3 proj13T4 proj13T5 proj13T6 proj13T7 proj13T8 proj13T9;
      proj13T11: @T11 proj13T0 proj13T1 proj13T2 proj13T3 proj13T4 proj13T5 proj13T6 proj13T7 proj13T8 proj13T9 proj13T10;
      proj13T12: @T12 proj13T0 proj13T1 proj13T2 proj13T3 proj13T4 proj13T5 proj13T6 proj13T7 proj13T8 proj13T9 proj13T10 proj13T11;
    }.
Definition uncurry13  (R: rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12): rel1 sig13T :=
  fun x => R (proj13T0 x) (proj13T1 x) (proj13T2 x) (proj13T3 x) (proj13T4 x) (proj13T5 x) (proj13T6 x) (proj13T7 x) (proj13T8 x) (proj13T9 x) (proj13T10 x) (proj13T11 x) (proj13T12 x).
Definition curry13  (R: rel1 sig13T): rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 :=
  fun x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 => R (@exist13T x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12).

Lemma uncurry_map13 r0 r1 (LE : r0 <13== r1) : uncurry13 r0 <1== uncurry13 r1.
Proof. intros [] H. apply LE. apply H. Qed.

Lemma uncurry_map_rev13 r0 r1 (LE: uncurry13 r0 <1== uncurry13 r1) : r0 <13== r1.
Proof.
  red; intros. apply (LE (@exist13T x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) PR).
Qed.

Lemma curry_map13 r0 r1 (LE: r0 <1== r1) : curry13 r0 <13== curry13 r1.
Proof. 
  red; intros. apply (LE (@exist13T x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) PR).
Qed.

Lemma curry_map_rev13 r0 r1 (LE: curry13 r0 <13== curry13 r1) : r0 <1== r1.
Proof. 
  intros [] H. apply LE. apply H.
Qed.

Lemma uncurry_bij1_13 r : curry13 (uncurry13 r) <13== r.
Proof. unfold le13. intros. apply PR. Qed.

Lemma uncurry_bij2_13 r : r <13== curry13 (uncurry13 r).
Proof. unfold le13. intros. apply PR. Qed.

Lemma curry_bij1_13 r : uncurry13 (curry13 r) <1== r.
Proof. intros []. intro H. apply H. Qed.

Lemma curry_bij2_13 r : r <1== uncurry13 (curry13 r).
Proof. intros []. intro H. apply H. Qed.

Lemma uncurry_adjoint1_13 r0 r1 (LE: uncurry13 r0 <1== r1) : r0 <13== curry13 r1.
Proof.
  apply uncurry_map_rev13. eapply le1_trans; [apply LE|]. apply curry_bij2_13.
Qed.

Lemma uncurry_adjoint2_13 r0 r1 (LE: r0 <13== curry13 r1) : uncurry13 r0 <1== r1.
Proof.
  apply curry_map_rev13. eapply le13_trans; [|apply LE]. apply uncurry_bij2_13.
Qed.

Lemma curry_adjoint1_13 r0 r1 (LE: curry13 r0 <13== r1) : r0 <1== uncurry13 r1.
Proof.
  apply curry_map_rev13. eapply le13_trans; [apply LE|]. apply uncurry_bij2_13.
Qed.

Lemma curry_adjoint2_13 r0 r1 (LE: r0 <1== uncurry13 r1) : curry13 r0 <13== r1.
Proof.
  apply uncurry_map_rev13. eapply le1_trans; [|apply LE]. apply curry_bij1_13.
Qed.

(** ** Predicates of Arity 13
*)

Definition paco13(gf : rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12)(r: rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12) : rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 :=
  curry13 (paco (fun R0 => uncurry13 (gf (curry13 R0))) (uncurry13 r)).

Definition upaco13(gf : rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12)(r: rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12) := paco13 gf r \13/ r.
Arguments paco13 : clear implicits.
Arguments upaco13 : clear implicits.
Hint Unfold upaco13.

Definition monotone13 (gf: rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12) :=
  forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 r r' (IN: gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) (LE: r <13= r'), gf r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12.

Definition _monotone13 (gf: rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12) :=
  forall r r'(LE: r <13= r'), gf r <13== gf r'.

Lemma monotone13_eq (gf: rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12) :
  monotone13 gf <-> _monotone13 gf.
Proof. unfold monotone13, _monotone13, le13. split; intros; eapply H; eassumption. Qed.

Lemma monotone13_map (gf: rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12)
      (MON: _monotone13 gf) :
  _monotone (fun R0 => uncurry13 (gf (curry13 R0))).
Proof.
  red; intros. apply uncurry_map13. apply MON; apply curry_map13; assumption.
Qed.

Lemma monotone13_compose (gf gf': rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12)
      (MON1: monotone13 gf)
      (MON2: monotone13 gf'):
  monotone13 (compose gf gf').
Proof.
  red; intros. eapply MON1. apply IN.
  intros. eapply MON2. apply PR. apply LE.
Qed.

Lemma monotone13_union (gf gf': rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12)
      (MON1: monotone13 gf)
      (MON2: monotone13 gf'):
  monotone13 (gf \14/ gf').
Proof.
  red; intros. destruct IN.
  - left. eapply MON1. apply H. apply LE.
  - right. eapply MON2. apply H. apply LE.
Qed.

Lemma _paco13_mon_gen (gf gf': rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12) r r'
    (LEgf: gf <14= gf')
    (LEr: r <13= r'):
  paco13 gf r <13== paco13 gf' r'.
Proof.
  apply curry_map13. red; intros. eapply paco_mon_gen. apply PR.
  - intros. apply LEgf, PR0.
  - intros. apply LEr, PR0.
Qed.

Lemma paco13_mon_gen (gf gf': rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12) r r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12
    (REL: paco13 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)
    (LEgf: gf <14= gf')
    (LEr: r <13= r'):
  paco13 gf' r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12.
Proof.
  eapply _paco13_mon_gen; [apply LEgf | apply LEr | apply REL].
Qed.

Lemma paco13_mon_bot (gf gf': rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12) r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12
    (REL: paco13 gf bot13 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)
    (LEgf: gf <14= gf'):
  paco13 gf' r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12.
Proof.
  eapply paco13_mon_gen; [apply REL | apply LEgf | intros; contradiction PR].
Qed.

Lemma upaco13_mon_gen (gf gf': rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12) r r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12
    (REL: upaco13 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)
    (LEgf: gf <14= gf')
    (LEr: r <13= r'):
  upaco13 gf' r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12.
Proof.
  destruct REL.
  - left. eapply paco13_mon_gen; [apply H | apply LEgf | apply LEr].
  - right. apply LEr, H.
Qed.

Lemma upaco13_mon_bot (gf gf': rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12) r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12
    (REL: upaco13 gf bot13 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)
    (LEgf: gf <14= gf'):
  upaco13 gf' r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12.
Proof.
  eapply upaco13_mon_gen; [apply REL | apply LEgf | intros; contradiction PR].
Qed.

Section Arg13.

Variable gf : rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12.
Arguments gf : clear implicits.

Theorem _paco13_mon: _monotone13 (paco13 gf).
Proof.
  red; intros. eapply curry_map13, _paco_mon; apply uncurry_map13; assumption.
Qed.

Theorem _paco13_acc: forall
  l r (OBG: forall rr (INC: r <13== rr) (CIH: l <13== rr), l <13== paco13 gf rr),
  l <13== paco13 gf r.
Proof.
  intros. apply uncurry_adjoint1_13.
  eapply _paco_acc. intros.
  apply uncurry_adjoint1_13 in INC. apply uncurry_adjoint1_13 in CIH.
  apply uncurry_adjoint2_13.
  eapply le13_trans. eapply (OBG _ INC CIH).
  apply curry_map13.
  apply _paco_mon; try apply le1_refl; apply curry_bij1_13.
Qed.

Theorem _paco13_mult_strong: forall r,
  paco13 gf (upaco13 gf r) <13== paco13 gf r.
Proof.
  intros. apply curry_map13.
  eapply le1_trans; [| eapply _paco_mult_strong].
  apply _paco_mon; intros []; intros H; apply H.
Qed.

Theorem _paco13_fold: forall r,
  gf (upaco13 gf r) <13== paco13 gf r.
Proof.
  intros. apply uncurry_adjoint1_13.
  eapply le1_trans; [| apply _paco_fold]. apply le1_refl.
Qed.

Theorem _paco13_unfold: forall (MON: _monotone13 gf) r,
  paco13 gf r <13== gf (upaco13 gf r).
Proof.
  intros. apply curry_adjoint2_13.
  eapply _paco_unfold; apply monotone13_map; assumption.
Qed.

Theorem paco13_acc: forall
  l r (OBG: forall rr (INC: r <13= rr) (CIH: l <13= rr), l <13= paco13 gf rr),
  l <13= paco13 gf r.
Proof.
  apply _paco13_acc.
Qed.

Theorem paco13_mon: monotone13 (paco13 gf).
Proof.
  apply monotone13_eq.
  apply _paco13_mon.
Qed.

Theorem upaco13_mon: monotone13 (upaco13 gf).
Proof.
  red; intros.
  destruct IN.
  - left. eapply paco13_mon. apply H. apply LE.
  - right. apply LE, H.
Qed.

Theorem paco13_mult_strong: forall r,
  paco13 gf (upaco13 gf r) <13= paco13 gf r.
Proof.
  apply _paco13_mult_strong.
Qed.

Corollary paco13_mult: forall r,
  paco13 gf (paco13 gf r) <13= paco13 gf r.
Proof. intros; eapply paco13_mult_strong, paco13_mon; [apply PR|..]; intros; left; assumption. Qed.

Theorem paco13_fold: forall r,
  gf (upaco13 gf r) <13= paco13 gf r.
Proof.
  apply _paco13_fold.
Qed.

Theorem paco13_unfold: forall (MON: monotone13 gf) r,
  paco13 gf r <13= gf (upaco13 gf r).
Proof.
  intro. eapply _paco13_unfold; apply monotone13_eq; assumption.
Qed.

End Arg13.

Arguments paco13_acc : clear implicits.
Arguments paco13_mon : clear implicits.
Arguments upaco13_mon : clear implicits.
Arguments paco13_mult_strong : clear implicits.
Arguments paco13_mult : clear implicits.
Arguments paco13_fold : clear implicits.
Arguments paco13_unfold : clear implicits.

Global Instance paco13_inst  (gf : rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12->_) r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : paco_class (paco13 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) :=
{ pacoacc    := paco13_acc gf;
  pacomult   := paco13_mult gf;
  pacofold   := paco13_fold gf;
  pacounfold := paco13_unfold gf }.

End PACO13.

Global Opaque paco13.

Hint Unfold upaco13.
Hint Resolve paco13_fold.
Hint Unfold monotone13.

