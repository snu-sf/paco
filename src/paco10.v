Require Export Program.Basics. Open Scope program_scope.
From Paco Require Import paconotation_internal paco_internal pacotac_internal paco_currying.
From Paco Require Export paconotation.
Set Implicit Arguments.

Section PACO10.

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

(** ** Predicates of Arity 10
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
    arity0))))))))))).

Definition paco10(gf : rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9)(r: rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) : rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 :=
  _paco (t := t) gf r.

Definition upaco10(gf : rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9)(r: rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) := paco10 gf r \10/ r.
Arguments paco10 : clear implicits.
Arguments upaco10 : clear implicits.
Hint Unfold upaco10 : core.

Definition monotone10 (gf: rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) :=
  forall r r' (LE: r <10= r'), gf r <10= gf r'.

Lemma monotone10_compose : forall (gf gf': rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9)
      (MON1: monotone10 gf)
      (MON2: monotone10 gf'),
  monotone10 (compose gf gf').
Proof.
  exact (_monotone_compose (t := t)).
Qed.

Lemma monotone10_union : forall (gf gf': rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9)
      (MON1: monotone10 gf)
      (MON2: monotone10 gf'),
  monotone10 (gf \11/ gf').
Proof.
  exact (_monotone_union (t := t)).
Qed.

Lemma paco10_mon_gen : forall (gf gf': rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9)
    (LEgf: gf <11= gf')
    r r' (LEr: r <10= r'),
  paco10 gf r <10= paco10 gf' r'.
Proof.
  exact (_paco_mon_gen (t := t)).
Qed.

Lemma paco10_mon_bot : forall (gf gf': rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) r'
    (LEgf: gf <11= gf'),
  paco10 gf bot10 <10= paco10 gf' r'.
Proof.
  exact (_paco_mon_bot (t := t)).
Qed.

Lemma upaco10_mon_gen : forall (gf gf': rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9)
    (LEgf: gf <11= gf')
    r r' (LEr: r <10= r'),
  upaco10 gf r <10= upaco10 gf' r'.
Proof.
  exact (_upaco_mon_gen (t := t)).
Qed.

Lemma upaco10_mon_bot : forall (gf gf': rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) r'
    (LEgf: gf <11= gf'),
  upaco10 gf bot10 <10= upaco10 gf' r'.
Proof.
  exact (_upaco_mon_bot (t := t)).
Qed.

Section Arg10.

Variable gf : rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9.
Arguments gf : clear implicits.

Theorem paco10_acc: forall
  l r (OBG: forall rr (INC: r <10= rr) (CIH: l <10= rr), l <10= paco10 gf rr),
  l <10= paco10 gf r.
Proof.
  exact (_paco_acc (t := t) gf).
Qed.

Theorem paco10_mon: monotone10 (paco10 gf).
Proof.
  exact (_paco_mon (t := t) gf).
Qed.

Theorem upaco10_mon: monotone10 (upaco10 gf).
Proof.
  exact (_upaco_mon (t := t) gf).
Qed.

Theorem paco10_mult_strong: forall r,
  paco10 gf (upaco10 gf r) <10= paco10 gf r.
Proof.
  exact (_paco_mult_strong (t := t) gf).
Qed.

Corollary paco10_mult: forall r,
  paco10 gf (paco10 gf r) <10= paco10 gf r.
Proof.
  exact (_paco_mult (t := t) gf).
Qed.

Theorem paco10_fold: forall r,
  gf (upaco10 gf r) <10= paco10 gf r.
Proof.
  exact (_paco_fold (t := t) gf).
Qed.

Theorem paco10_unfold: forall (MON: monotone10 gf) r,
  paco10 gf r <10= gf (upaco10 gf r).
Proof.
  exact (_paco_unfold (t := t) gf).
Qed.

End Arg10.

Arguments paco10_acc : clear implicits.
Arguments paco10_mon : clear implicits.
Arguments upaco10_mon : clear implicits.
Arguments paco10_mult_strong : clear implicits.
Arguments paco10_mult : clear implicits.
Arguments paco10_fold : clear implicits.
Arguments paco10_unfold : clear implicits.

Global Instance paco10_inst  (gf : rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9->_) r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : paco_class (paco10 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) :=
{ pacoacc    := paco10_acc gf;
  pacomult   := paco10_mult gf;
  pacofold   := paco10_fold gf;
  pacounfold := paco10_unfold gf }.

End PACO10.

Global Opaque paco10.

Hint Unfold upaco10 : core.
Hint Resolve paco10_fold : core.
Hint Unfold monotone10 : core.

