Require Export Program.Basics. Open Scope program_scope.
From Paco Require Import paconotation_internal paco_internal pacotac_internal paco_currying.
From Paco Require Export paconotation.
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

(** ** Predicates of Arity 11
*)

Definition t : arityn 11 := Eval compute in (
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
    arityn0)))))))))))).

Definition paco11(gf : rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10)(r: rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10) : rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 :=
  _paco (t := t) gf r.

Definition upaco11(gf : rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10)(r: rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10) := paco11 gf r \11/ r.
Arguments paco11 : clear implicits.
Arguments upaco11 : clear implicits.
Hint Unfold upaco11 : core.

Definition monotone11 (gf: rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10) :=
  forall r r' (LE: r <11= r'), gf r <11= gf r'.

Lemma monotone11_compose : forall (gf gf': rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10)
      (MON1: monotone11 gf)
      (MON2: monotone11 gf'),
  monotone11 (compose gf gf').
Proof.
  exact (_monotone_compose (t := t)).
Qed.

Lemma monotone11_union : forall (gf gf': rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10)
      (MON1: monotone11 gf)
      (MON2: monotone11 gf'),
  monotone11 (gf \12/ gf').
Proof.
  exact (_monotone_union (t := t)).
Qed.

Lemma paco11_mon_gen : forall (gf gf': rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10)
    (LEgf: gf <12= gf')
    r r' (LEr: r <11= r'),
  paco11 gf r <11= paco11 gf' r'.
Proof.
  exact (_paco_mon_gen (t := t)).
Qed.

Lemma paco11_mon_bot : forall (gf gf': rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10) r'
    (LEgf: gf <12= gf'),
  paco11 gf bot11 <11= paco11 gf' r'.
Proof.
  exact (_paco_mon_bot (t := t)).
Qed.

Lemma upaco11_mon_gen : forall (gf gf': rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10)
    (LEgf: gf <12= gf')
    r r' (LEr: r <11= r'),
  upaco11 gf r <11= upaco11 gf' r'.
Proof.
  exact (_upaco_mon_gen (t := t)).
Qed.

Lemma upaco11_mon_bot : forall (gf gf': rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10) r'
    (LEgf: gf <12= gf'),
  upaco11 gf bot11 <11= upaco11 gf' r'.
Proof.
  exact (_upaco_mon_bot (t := t)).
Qed.

Section Arg11.

Variable gf : rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 -> rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10.
Arguments gf : clear implicits.

Theorem paco11_acc: forall
  l r (OBG: forall rr (INC: r <11= rr) (CIH: l <11= rr), l <11= paco11 gf rr),
  l <11= paco11 gf r.
Proof.
  exact (_paco_acc (t := t) gf).
Qed.

Theorem paco11_mon: monotone11 (paco11 gf).
Proof.
  exact (_paco_mon (t := t) gf).
Qed.

Theorem upaco11_mon: monotone11 (upaco11 gf).
Proof.
  exact (_upaco_mon (t := t) gf).
Qed.

Theorem paco11_mult_strong: forall r,
  paco11 gf (upaco11 gf r) <11= paco11 gf r.
Proof.
  exact (_paco_mult_strong (t := t) gf).
Qed.

Corollary paco11_mult: forall r,
  paco11 gf (paco11 gf r) <11= paco11 gf r.
Proof.
  exact (_paco_mult (t := t) gf).
Qed.

Theorem paco11_fold: forall r,
  gf (upaco11 gf r) <11= paco11 gf r.
Proof.
  exact (_paco_fold (t := t) (upaco_spec t) gf).
Qed.

Theorem paco11_unfold: forall (MON: monotone11 gf) r,
  paco11 gf r <11= gf (upaco11 gf r).
Proof.
  exact (_paco_unfold (t := t) gf).
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

Hint Unfold upaco11 : core.
Hint Resolve paco11_fold : core.
Hint Unfold monotone11 : core.

