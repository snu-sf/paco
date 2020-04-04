Require Export Program.Basics. Open Scope program_scope.
From Paco Require Import paconotation_internal paco_internal pacotac_internal paco_currying.
From Paco Require Export paconotation.
Set Implicit Arguments.

Section PACO9.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
Variable T7 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5), Type.
Variable T8 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6), Type.

(** ** Predicates of Arity 9
*)

Definition t : arityn 9 := Eval compute in (
    aritynS (@T0) (fun x0 =>
    aritynS (@T1 x0) (fun x1 =>
    aritynS (@T2 x0 x1) (fun x2 =>
    aritynS (@T3 x0 x1 x2) (fun x3 =>
    aritynS (@T4 x0 x1 x2 x3) (fun x4 =>
    aritynS (@T5 x0 x1 x2 x3 x4) (fun x5 =>
    aritynS (@T6 x0 x1 x2 x3 x4 x5) (fun x6 =>
    aritynS (@T7 x0 x1 x2 x3 x4 x5 x6) (fun x7 =>
    aritynS (@T8 x0 x1 x2 x3 x4 x5 x6 x7) (fun x8 =>
    arityn0)))))))))).

Definition paco9(gf : rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8)(r: rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8) : rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 :=
  _paco (t := t) gf r.

Definition upaco9(gf : rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8)(r: rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8) := paco9 gf r \9/ r.
Arguments paco9 : clear implicits.
Arguments upaco9 : clear implicits.
Hint Unfold upaco9 : core.

Definition monotone9 (gf: rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8) :=
  forall r r' (LE: r <9= r'), gf r <9= gf r'.

Lemma monotone9_compose : forall (gf gf': rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8)
      (MON1: monotone9 gf)
      (MON2: monotone9 gf'),
  monotone9 (compose gf gf').
Proof.
  exact (_monotone_compose (t := t)).
Qed.

Lemma monotone9_union : forall (gf gf': rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8)
      (MON1: monotone9 gf)
      (MON2: monotone9 gf'),
  monotone9 (gf \10/ gf').
Proof.
  exact (_monotone_union (t := t)).
Qed.

Lemma paco9_mon_gen : forall (gf gf': rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8)
    (LEgf: gf <10= gf')
    r r' (LEr: r <9= r'),
  paco9 gf r <9= paco9 gf' r'.
Proof.
  exact (_paco_mon_gen (t := t)).
Qed.

Lemma paco9_mon_bot : forall (gf gf': rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8) r'
    (LEgf: gf <10= gf'),
  paco9 gf bot9 <9= paco9 gf' r'.
Proof.
  exact (_paco_mon_bot (t := t)).
Qed.

Lemma upaco9_mon_gen : forall (gf gf': rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8)
    (LEgf: gf <10= gf')
    r r' (LEr: r <9= r'),
  upaco9 gf r <9= upaco9 gf' r'.
Proof.
  exact (_upaco_mon_gen (t := t)).
Qed.

Lemma upaco9_mon_bot : forall (gf gf': rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8) r'
    (LEgf: gf <10= gf'),
  upaco9 gf bot9 <9= upaco9 gf' r'.
Proof.
  exact (_upaco_mon_bot (t := t)).
Qed.

Section Arg9.

Variable gf : rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 -> rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8.
Arguments gf : clear implicits.

Theorem paco9_acc: forall
  l r (OBG: forall rr (INC: r <9= rr) (CIH: l <9= rr), l <9= paco9 gf rr),
  l <9= paco9 gf r.
Proof.
  exact (_paco_acc (t := t) gf).
Qed.

Theorem paco9_mon: monotone9 (paco9 gf).
Proof.
  exact (_paco_mon (t := t) gf).
Qed.

Theorem upaco9_mon: monotone9 (upaco9 gf).
Proof.
  exact (_upaco_mon (t := t) gf).
Qed.

Theorem paco9_mult_strong: forall r,
  paco9 gf (upaco9 gf r) <9= paco9 gf r.
Proof.
  exact (_paco_mult_strong (t := t) gf).
Qed.

Corollary paco9_mult: forall r,
  paco9 gf (paco9 gf r) <9= paco9 gf r.
Proof.
  exact (_paco_mult (t := t) gf).
Qed.

Theorem paco9_fold: forall r,
  gf (upaco9 gf r) <9= paco9 gf r.
Proof.
  exact (_paco_fold (t := t) (upaco_spec t) gf).
Qed.

Theorem paco9_unfold: forall (MON: monotone9 gf) r,
  paco9 gf r <9= gf (upaco9 gf r).
Proof.
  exact (_paco_unfold (t := t) gf).
Qed.

End Arg9.

Arguments paco9_acc : clear implicits.
Arguments paco9_mon : clear implicits.
Arguments upaco9_mon : clear implicits.
Arguments paco9_mult_strong : clear implicits.
Arguments paco9_mult : clear implicits.
Arguments paco9_fold : clear implicits.
Arguments paco9_unfold : clear implicits.

Global Instance paco9_inst  (gf : rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8->_) r x0 x1 x2 x3 x4 x5 x6 x7 x8 : paco_class (paco9 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8) :=
{ pacoacc    := paco9_acc gf;
  pacomult   := paco9_mult gf;
  pacofold   := paco9_fold gf;
  pacounfold := paco9_unfold gf }.

End PACO9.

Global Opaque paco9.

Hint Unfold upaco9 : core.
Hint Resolve paco9_fold : core.
Hint Unfold monotone9 : core.

