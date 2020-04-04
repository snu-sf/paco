Require Export Program.Basics. Open Scope program_scope.
From Paco Require Import paconotation_internal paco_internal pacotac_internal paco_currying.
From Paco Require Export paconotation.
Set Implicit Arguments.

Section PACO14.

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

(** ** Predicates of Arity 14
*)

Definition t : arityn 14 := Eval compute in (
    aritynS (@T0) (fun x0 =>
    aritynS (@T1 x0) (fun x1 =>
    aritynS (@T2 x0 x1) (fun x2 =>
    aritynS (@T3 x0 x1 x2) (fun x3 =>
    aritynS (@T4 x0 x1 x2 x3) (fun x4 =>
    aritynS (@T5 x0 x1 x2 x3 x4) (fun x5 =>
    aritynS (@T6 x0 x1 x2 x3 x4 x5) (fun x6 =>
    aritynS (@T7 x0 x1 x2 x3 x4 x5 x6) (fun x7 =>
    aritynS (@T8 x0 x1 x2 x3 x4 x5 x6 x7) (fun x8 =>
    aritynS (@T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (fun x9 =>
    aritynS (@T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (fun x10 =>
    aritynS (@T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) (fun x11 =>
    aritynS (@T12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) (fun x12 =>
    aritynS (@T13 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) (fun x13 =>
    arityn0))))))))))))))).

Definition paco14(gf : rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13)(r: rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13) : rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 :=
  _paco (t := t) gf r.

Definition upaco14(gf : rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13)(r: rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13) := paco14 gf r \14/ r.
Arguments paco14 : clear implicits.
Arguments upaco14 : clear implicits.
Hint Unfold upaco14 : core.

Definition monotone14 (gf: rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13) :=
  forall r r' (LE: r <14= r'), gf r <14= gf r'.

Lemma monotone14_compose : forall (gf gf': rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13)
      (MON1: monotone14 gf)
      (MON2: monotone14 gf'),
  monotone14 (compose gf gf').
Proof.
  exact (_monotone_compose (t := t)).
Qed.

Lemma monotone14_union : forall (gf gf': rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13)
      (MON1: monotone14 gf)
      (MON2: monotone14 gf'),
  monotone14 (gf \15/ gf').
Proof.
  exact (_monotone_union (t := t)).
Qed.

Lemma paco14_mon_gen : forall (gf gf': rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13)
    (LEgf: gf <15= gf')
    r r' (LEr: r <14= r'),
  paco14 gf r <14= paco14 gf' r'.
Proof.
  exact (_paco_mon_gen (t := t)).
Qed.

Lemma paco14_mon_bot : forall (gf gf': rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13) r'
    (LEgf: gf <15= gf'),
  paco14 gf bot14 <14= paco14 gf' r'.
Proof.
  exact (_paco_mon_bot (t := t)).
Qed.

Lemma upaco14_mon_gen : forall (gf gf': rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13)
    (LEgf: gf <15= gf')
    r r' (LEr: r <14= r'),
  upaco14 gf r <14= upaco14 gf' r'.
Proof.
  exact (_upaco_mon_gen (t := t)).
Qed.

Lemma upaco14_mon_bot : forall (gf gf': rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13) r'
    (LEgf: gf <15= gf'),
  upaco14 gf bot14 <14= upaco14 gf' r'.
Proof.
  exact (_upaco_mon_bot (t := t)).
Qed.

Section Arg14.

Variable gf : rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 -> rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13.
Arguments gf : clear implicits.

Theorem paco14_acc: forall
  l r (OBG: forall rr (INC: r <14= rr) (CIH: l <14= rr), l <14= paco14 gf rr),
  l <14= paco14 gf r.
Proof.
  exact (_paco_acc (t := t) gf).
Qed.

Theorem paco14_mon: monotone14 (paco14 gf).
Proof.
  exact (_paco_mon (t := t) gf).
Qed.

Theorem upaco14_mon: monotone14 (upaco14 gf).
Proof.
  exact (_upaco_mon (t := t) gf).
Qed.

Theorem paco14_mult_strong: forall r,
  paco14 gf (upaco14 gf r) <14= paco14 gf r.
Proof.
  exact (_paco_mult_strong (t := t) gf).
Qed.

Corollary paco14_mult: forall r,
  paco14 gf (paco14 gf r) <14= paco14 gf r.
Proof.
  exact (_paco_mult (t := t) gf).
Qed.

Theorem paco14_fold: forall r,
  gf (upaco14 gf r) <14= paco14 gf r.
Proof.
  exact (_paco_fold (t := t) (upaco_spec t) gf).
Qed.

Theorem paco14_unfold: forall (MON: monotone14 gf) r,
  paco14 gf r <14= gf (upaco14 gf r).
Proof.
  exact (_paco_unfold (t := t) gf).
Qed.

End Arg14.

Arguments paco14_acc : clear implicits.
Arguments paco14_mon : clear implicits.
Arguments upaco14_mon : clear implicits.
Arguments paco14_mult_strong : clear implicits.
Arguments paco14_mult : clear implicits.
Arguments paco14_fold : clear implicits.
Arguments paco14_unfold : clear implicits.

Global Instance paco14_inst  (gf : rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13->_) r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : paco_class (paco14 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) :=
{ pacoacc    := paco14_acc gf;
  pacomult   := paco14_mult gf;
  pacofold   := paco14_fold gf;
  pacounfold := paco14_unfold gf }.

End PACO14.

Global Opaque paco14.

Hint Unfold upaco14 : core.
Hint Resolve paco14_fold : core.
Hint Unfold monotone14 : core.

