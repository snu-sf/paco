Require Export Program.Basics. Open Scope program_scope.
From Paco Require Import paconotation_internal paco_internal pacotac_internal paco_currying.
From Paco Require Export paconotation.
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

(** ** Predicates of Arity 13
*)

Notation t := (
    arityS (@T0) (fun x0 =>
    arityS (@T1 x0) (fun x1 =>
    arityS (@T2 x0 x1) (fun x2 =>
    arityS (@T3 x0 x1 x2) (fun x3 =>
    arityS (@T4 x0 x1 x2 x3) (fun x4 =>
    arityS (@T5 x0 x1 x2 x3 x4) (fun x5 =>
    arityS (@T6 x0 x1 x2 x3 x4 x5) (fun x6 =>
    arityS (@T7 x0 x1 x2 x3 x4 x5 x6) (fun x7 =>
    arityS (@T8 x0 x1 x2 x3 x4 x5 x6 x7) (fun x8 =>
    arityS (@T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (fun x9 =>
    arityS (@T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (fun x10 =>
    arityS (@T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) (fun x11 =>
    arityS (@T12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) (fun x12 =>
    arity0)))))))))))))).

Definition paco13(gf : rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12)(r: rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12) : rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 :=
  _paco (t := t) gf r.

Definition upaco13(gf : rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12)(r: rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12) := paco13 gf r \13/ r.
Arguments paco13 : clear implicits.
Arguments upaco13 : clear implicits.
Hint Unfold upaco13 : core.

Definition monotone13 (gf: rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12) :=
  forall r r' (LE: r <13= r'), gf r <13= gf r'.

Lemma monotone13_compose : forall (gf gf': rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12)
      (MON1: monotone13 gf)
      (MON2: monotone13 gf'),
  monotone13 (compose gf gf').
Proof.
  exact (_monotone_compose (t := t)).
Qed.

Lemma monotone13_union : forall (gf gf': rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12)
      (MON1: monotone13 gf)
      (MON2: monotone13 gf'),
  monotone13 (gf \14/ gf').
Proof.
  exact (_monotone_union (t := t)).
Qed.

Lemma paco13_mon_gen : forall (gf gf': rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12)
    (LEgf: gf <14= gf')
    r r' (LEr: r <13= r'),
  paco13 gf r <13= paco13 gf' r'.
Proof.
  exact (_paco_mon_gen (t := t)).
Qed.

Lemma paco13_mon_bot : forall (gf gf': rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12) r'
    (LEgf: gf <14= gf'),
  paco13 gf bot13 <13= paco13 gf' r'.
Proof.
  exact (_paco_mon_bot (t := t)).
Qed.

Lemma upaco13_mon_gen : forall (gf gf': rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12)
    (LEgf: gf <14= gf')
    r r' (LEr: r <13= r'),
  upaco13 gf r <13= upaco13 gf' r'.
Proof.
  exact (_upaco_mon_gen (t := t)).
Qed.

Lemma upaco13_mon_bot : forall (gf gf': rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12) r'
    (LEgf: gf <14= gf'),
  upaco13 gf bot13 <13= upaco13 gf' r'.
Proof.
  exact (_upaco_mon_bot (t := t)).
Qed.

Section Arg13.

Variable gf : rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 -> rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12.
Arguments gf : clear implicits.

Theorem paco13_acc: forall
  l r (OBG: forall rr (INC: r <13= rr) (CIH: l <13= rr), l <13= paco13 gf rr),
  l <13= paco13 gf r.
Proof.
  exact (_paco_acc (t := t) gf).
Qed.

Theorem paco13_mon: monotone13 (paco13 gf).
Proof.
  exact (_paco_mon (t := t) gf).
Qed.

Theorem upaco13_mon: monotone13 (upaco13 gf).
Proof.
  exact (_upaco_mon (t := t) gf).
Qed.

Theorem paco13_mult_strong: forall r,
  paco13 gf (upaco13 gf r) <13= paco13 gf r.
Proof.
  exact (_paco_mult_strong (t := t) gf).
Qed.

Corollary paco13_mult: forall r,
  paco13 gf (paco13 gf r) <13= paco13 gf r.
Proof.
  exact (_paco_mult (t := t) gf).
Qed.

Theorem paco13_fold: forall r,
  gf (upaco13 gf r) <13= paco13 gf r.
Proof.
  exact (_paco_fold (t := t) gf).
Qed.

Theorem paco13_unfold: forall (MON: monotone13 gf) r,
  paco13 gf r <13= gf (upaco13 gf r).
Proof.
  exact (_paco_unfold (t := t) gf).
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

Hint Unfold upaco13 : core.
Hint Resolve paco13_fold : core.
Hint Unfold monotone13 : core.

