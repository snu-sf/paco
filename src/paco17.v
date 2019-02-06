Require Export paconotation pacotacuser.
Require Import paconotation_internal pacotac pacon.
Set Implicit Arguments.

Section PACO17.

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
Variable T13 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) (x12: @T12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11), Type.
Variable T14 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) (x12: @T12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) (x13: @T13 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12), Type.
Variable T15 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) (x12: @T12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) (x13: @T13 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) (x14: @T14 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13), Type.
Variable T16 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) (x12: @T12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) (x13: @T13 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) (x14: @T14 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) (x15: @T15 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14), Type.

Record sig17T :=
  exist17T { 
      proj17T0: @T0;
      proj17T1: @T1 proj17T0;
      proj17T2: @T2 proj17T0 proj17T1;
      proj17T3: @T3 proj17T0 proj17T1 proj17T2;
      proj17T4: @T4 proj17T0 proj17T1 proj17T2 proj17T3;
      proj17T5: @T5 proj17T0 proj17T1 proj17T2 proj17T3 proj17T4;
      proj17T6: @T6 proj17T0 proj17T1 proj17T2 proj17T3 proj17T4 proj17T5;
      proj17T7: @T7 proj17T0 proj17T1 proj17T2 proj17T3 proj17T4 proj17T5 proj17T6;
      proj17T8: @T8 proj17T0 proj17T1 proj17T2 proj17T3 proj17T4 proj17T5 proj17T6 proj17T7;
      proj17T9: @T9 proj17T0 proj17T1 proj17T2 proj17T3 proj17T4 proj17T5 proj17T6 proj17T7 proj17T8;
      proj17T10: @T10 proj17T0 proj17T1 proj17T2 proj17T3 proj17T4 proj17T5 proj17T6 proj17T7 proj17T8 proj17T9;
      proj17T11: @T11 proj17T0 proj17T1 proj17T2 proj17T3 proj17T4 proj17T5 proj17T6 proj17T7 proj17T8 proj17T9 proj17T10;
      proj17T12: @T12 proj17T0 proj17T1 proj17T2 proj17T3 proj17T4 proj17T5 proj17T6 proj17T7 proj17T8 proj17T9 proj17T10 proj17T11;
      proj17T13: @T13 proj17T0 proj17T1 proj17T2 proj17T3 proj17T4 proj17T5 proj17T6 proj17T7 proj17T8 proj17T9 proj17T10 proj17T11 proj17T12;
      proj17T14: @T14 proj17T0 proj17T1 proj17T2 proj17T3 proj17T4 proj17T5 proj17T6 proj17T7 proj17T8 proj17T9 proj17T10 proj17T11 proj17T12 proj17T13;
      proj17T15: @T15 proj17T0 proj17T1 proj17T2 proj17T3 proj17T4 proj17T5 proj17T6 proj17T7 proj17T8 proj17T9 proj17T10 proj17T11 proj17T12 proj17T13 proj17T14;
      proj17T16: @T16 proj17T0 proj17T1 proj17T2 proj17T3 proj17T4 proj17T5 proj17T6 proj17T7 proj17T8 proj17T9 proj17T10 proj17T11 proj17T12 proj17T13 proj17T14 proj17T15;
    }.

Definition uncurry17 (R: rel17 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16): rel1 sig17T := fun x => R (proj17T0 x) (proj17T1 x) (proj17T2 x) (proj17T3 x) (proj17T4 x) (proj17T5 x) (proj17T6 x) (proj17T7 x) (proj17T8 x) (proj17T9 x) (proj17T10 x) (proj17T11 x) (proj17T12 x) (proj17T13 x) (proj17T14 x) (proj17T15 x) (proj17T16 x).

Definition curry17 (R: rel1 sig17T): rel17 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 :=
  fun x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 => R (exist17T x16).

Lemma uncurry_map17 r0 r1 (LE : r0 <17== r1) : uncurry17 r0 <1== uncurry17 r1.
Proof. intros [] H. apply LE. apply H. Qed.

Lemma uncurry_map_rev17 r0 r1 (LE: uncurry17 r0 <1== uncurry17 r1) : r0 <17== r1.
Proof.
  repeat_intros 17. intros H. apply (LE (exist17T x16) H).
Qed.

Lemma curry_map17 r0 r1 (LE: r0 <1== r1) : curry17 r0 <17== curry17 r1.
Proof. 
  repeat_intros 17. intros H. apply (LE (exist17T x16) H).
Qed.

Lemma curry_map_rev17 r0 r1 (LE: curry17 r0 <17== curry17 r1) : r0 <1== r1.
Proof. 
  intros [] H. apply LE. apply H.
Qed.

Lemma uncurry_bij1_17 r : curry17 (uncurry17 r) <17== r.
Proof. unfold le17. repeat_intros 17. intros H. apply H. Qed.

Lemma uncurry_bij2_17 r : r <17== curry17 (uncurry17 r).
Proof. unfold le17. repeat_intros 17. intros H. apply H. Qed.

Lemma curry_bij1_17 r : uncurry17 (curry17 r) <1== r.
Proof. intros []. intro H. apply H. Qed.

Lemma curry_bij2_17 r : r <1== uncurry17 (curry17 r).
Proof. intros []. intro H. apply H. Qed.

Lemma uncurry_adjoint1_17 r0 r1 (LE: uncurry17 r0 <1== r1) : r0 <17== curry17 r1.
Proof.
  apply uncurry_map_rev17. eapply le1_trans; [apply LE|]. apply curry_bij2_17.
Qed.

Lemma uncurry_adjoint2_17 r0 r1 (LE: r0 <17== curry17 r1) : uncurry17 r0 <1== r1.
Proof.
  apply curry_map_rev17. eapply le17_trans; [|apply LE]. apply uncurry_bij2_17.
Qed.

Lemma curry_adjoint1_17 r0 r1 (LE: curry17 r0 <17== r1) : r0 <1== uncurry17 r1.
Proof.
  apply curry_map_rev17. eapply le17_trans; [apply LE|]. apply uncurry_bij2_17.
Qed.

Lemma curry_adjoint2_17 r0 r1 (LE: r0 <1== uncurry17 r1) : curry17 r0 <17== r1.
Proof.
  apply uncurry_map_rev17. eapply le1_trans; [|apply LE]. apply curry_bij1_17.
Qed.

(** ** Predicates of Arity 17
*)

Definition paco17(gf : rel17 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 -> rel17 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16)(r: rel17 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16) : rel17 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 :=
  curry17 (paco (fun R0 => uncurry17 (gf (curry17 R0))) (uncurry17 r)).

Definition upaco17(gf : rel17 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 -> rel17 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16)(r: rel17 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16) := paco17 gf r \17/ r.
Arguments paco17 : clear implicits.
Arguments upaco17 : clear implicits.
Hint Unfold upaco17.

Definition monotone17 (gf: rel17 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 -> rel17 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16) :=
  forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 r r' (IN: gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16) (LE: r <17= r'), gf r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16.

Definition _monotone17 (gf: rel17 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 -> rel17 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16) :=
  forall r r'(LE: r <17= r'), gf r <17== gf r'.

Lemma monotone17_eq (gf: rel17 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 -> rel17 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16) :
  monotone17 gf <-> _monotone17 gf.
Proof. unfold monotone17, _monotone17, le17. split; intros; eapply H; eassumption. Qed.

Lemma monotone17_map (gf: rel17 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 -> rel17 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16)
      (MON: _monotone17 gf) :
  _monotone (fun R0 => uncurry17 (gf (curry17 R0))).
Proof.
  repeat_intros 3. apply uncurry_map17. apply MON; apply curry_map17; assumption.
Qed.

Lemma _paco17_mon_gen (gf gf': rel17 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 -> rel17 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16) r r'
    (LEgf: gf <18= gf')
    (LEr: r <17= r'):
  paco17 gf r <17== paco17 gf' r'.
Proof.
  apply curry_map17. red; intros. eapply paco_mon_gen. apply PR.
  - intros. apply LEgf, PR0.
  - intros. apply LEr, PR0.
Qed.

Lemma paco17_mon_gen (gf gf': rel17 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 -> rel17 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16) r r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16
    (REL: paco17 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16)
    (LEgf: gf <18= gf')
    (LEr: r <17= r'):
  paco17 gf' r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16.
Proof.
  eapply _paco17_mon_gen; [apply LEgf | apply LEr | apply REL].
Qed.

Lemma upaco17_mon_gen (gf gf': rel17 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 -> rel17 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16) r r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16
    (REL: upaco17 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16)
    (LEgf: gf <18= gf')
    (LEr: r <17= r'):
  upaco17 gf' r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16.
Proof.
  destruct REL.
  - left. eapply paco17_mon_gen; [apply H | apply LEgf | apply LEr].
  - right. apply LEr, H.
Qed.

Section Arg17.

Variable gf : rel17 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 -> rel17 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16.
Arguments gf : clear implicits.

Theorem _paco17_mon: _monotone17 (paco17 gf).
Proof.
  repeat_intros 3. eapply curry_map17, _paco_mon; apply uncurry_map17; assumption.
Qed.

Theorem _paco17_acc: forall
  l r (OBG: forall rr (INC: r <17== rr) (CIH: l <17== rr), l <17== paco17 gf rr),
  l <17== paco17 gf r.
Proof.
  intros. apply uncurry_adjoint1_17.
  eapply _paco_acc. intros.
  apply uncurry_adjoint1_17 in INC. apply uncurry_adjoint1_17 in CIH.
  apply uncurry_adjoint2_17.
  eapply le17_trans. eapply (OBG _ INC CIH).
  apply curry_map17.
  apply _paco_mon; try apply le1_refl; apply curry_bij1_17.
Qed.

Theorem _paco17_mult_strong: forall r,
  paco17 gf (upaco17 gf r) <17== paco17 gf r.
Proof.
  intros. apply curry_map17.
  eapply le1_trans; [| eapply _paco_mult_strong].
  apply _paco_mon; intros []; intros H; apply H.
Qed.

Theorem _paco17_fold: forall r,
  gf (upaco17 gf r) <17== paco17 gf r.
Proof.
  intros. apply uncurry_adjoint1_17.
  eapply le1_trans; [| apply _paco_fold]. apply le1_refl.
Qed.

Theorem _paco17_unfold: forall (MON: _monotone17 gf) r,
  paco17 gf r <17== gf (upaco17 gf r).
Proof.
  intros. apply curry_adjoint2_17.
  eapply _paco_unfold; apply monotone17_map; assumption.
Qed.

Theorem paco17_acc: forall
  l r (OBG: forall rr (INC: r <17= rr) (CIH: l <17= rr), l <17= paco17 gf rr),
  l <17= paco17 gf r.
Proof.
  apply _paco17_acc.
Qed.

Theorem paco17_mon: monotone17 (paco17 gf).
Proof.
  apply monotone17_eq.
  apply _paco17_mon.
Qed.

Theorem upaco17_mon: monotone17 (upaco17 gf).
Proof.
  repeat_intros 19. intros R  LE0.
  destruct R.
  - left. eapply paco17_mon. apply H. apply LE0.
  - right. apply LE0, H.
Qed.

Theorem paco17_mult_strong: forall r,
  paco17 gf (upaco17 gf r) <17= paco17 gf r.
Proof.
  apply _paco17_mult_strong.
Qed.

Corollary paco17_mult: forall r,
  paco17 gf (paco17 gf r) <17= paco17 gf r.
Proof. intros; eapply paco17_mult_strong, paco17_mon; [apply PR|..]; intros; left; assumption. Qed.

Theorem paco17_fold: forall r,
  gf (upaco17 gf r) <17= paco17 gf r.
Proof.
  apply _paco17_fold.
Qed.

Theorem paco17_unfold: forall (MON: monotone17 gf) r,
  paco17 gf r <17= gf (upaco17 gf r).
Proof.
  repeat_intros 1. eapply _paco17_unfold; apply monotone17_eq; assumption.
Qed.

End Arg17.

Arguments paco17_acc : clear implicits.
Arguments paco17_mon : clear implicits.
Arguments upaco17_mon : clear implicits.
Arguments paco17_mult_strong : clear implicits.
Arguments paco17_mult : clear implicits.
Arguments paco17_fold : clear implicits.
Arguments paco17_unfold : clear implicits.

Global Instance paco17_inst  (gf : rel17 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16->_) r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : paco_class (paco17 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16) :=
{ pacoacc    := paco17_acc gf;
  pacomult   := paco17_mult gf;
  pacofold   := paco17_fold gf;
  pacounfold := paco17_unfold gf }.

End PACO17.

Global Opaque paco17.

Hint Unfold upaco17.
Hint Resolve paco17_fold.
Hint Unfold monotone17.

