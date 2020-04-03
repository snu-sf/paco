Require Export Program.Basics. Open Scope program_scope.
From Paco Require Import paconotation_internal paco_internal pacotac_internal paco_currying.
From Paco Require Export paconotation.
Set Implicit Arguments.

Section PACO8.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
Variable T7 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5), Type.

(** ** Predicates of Arity 8
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
    arity0))))))))).

Definition paco8(gf : rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7)(r: rel8 T0 T1 T2 T3 T4 T5 T6 T7) : rel8 T0 T1 T2 T3 T4 T5 T6 T7 :=
  _paco (t := t) gf r.

Definition upaco8(gf : rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7)(r: rel8 T0 T1 T2 T3 T4 T5 T6 T7) := paco8 gf r \8/ r.
Arguments paco8 : clear implicits.
Arguments upaco8 : clear implicits.
Hint Unfold upaco8 : core.

Definition monotone8 (gf: rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7) :=
  forall r r' (LE: r <8= r'), gf r <8= gf r'.

Lemma monotone8_compose : forall (gf gf': rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7)
      (MON1: monotone8 gf)
      (MON2: monotone8 gf'),
  monotone8 (compose gf gf').
Proof.
  exact (_monotone_compose (t := t)).
Qed.

Lemma monotone8_union : forall (gf gf': rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7)
      (MON1: monotone8 gf)
      (MON2: monotone8 gf'),
  monotone8 (gf \9/ gf').
Proof.
  exact (_monotone_union (t := t)).
Qed.

Lemma paco8_mon_gen : forall (gf gf': rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7)
    (LEgf: gf <9= gf')
    r r' (LEr: r <8= r'),
  paco8 gf r <8= paco8 gf' r'.
Proof.
  exact (_paco_mon_gen (t := t)).
Qed.

Lemma paco8_mon_bot : forall (gf gf': rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7) r'
    (LEgf: gf <9= gf'),
  paco8 gf bot8 <8= paco8 gf' r'.
Proof.
  exact (_paco_mon_bot (t := t)).
Qed.

Lemma upaco8_mon_gen : forall (gf gf': rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7)
    (LEgf: gf <9= gf')
    r r' (LEr: r <8= r'),
  upaco8 gf r <8= upaco8 gf' r'.
Proof.
  exact (_upaco_mon_gen (t := t)).
Qed.

Lemma upaco8_mon_bot : forall (gf gf': rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7) r'
    (LEgf: gf <9= gf'),
  upaco8 gf bot8 <8= upaco8 gf' r'.
Proof.
  exact (_upaco_mon_bot (t := t)).
Qed.

Section Arg8.

Variable gf : rel8 T0 T1 T2 T3 T4 T5 T6 T7 -> rel8 T0 T1 T2 T3 T4 T5 T6 T7.
Arguments gf : clear implicits.

Theorem paco8_acc: forall
  l r (OBG: forall rr (INC: r <8= rr) (CIH: l <8= rr), l <8= paco8 gf rr),
  l <8= paco8 gf r.
Proof.
  exact (_paco_acc (t := t) gf).
Qed.

Theorem paco8_mon: monotone8 (paco8 gf).
Proof.
  exact (_paco_mon (t := t) gf).
Qed.

Theorem upaco8_mon: monotone8 (upaco8 gf).
Proof.
  exact (_upaco_mon (t := t) gf).
Qed.

Theorem paco8_mult_strong: forall r,
  paco8 gf (upaco8 gf r) <8= paco8 gf r.
Proof.
  exact (_paco_mult_strong (t := t) gf).
Qed.

Corollary paco8_mult: forall r,
  paco8 gf (paco8 gf r) <8= paco8 gf r.
Proof.
  exact (_paco_mult (t := t) gf).
Qed.

Theorem paco8_fold: forall r,
  gf (upaco8 gf r) <8= paco8 gf r.
Proof.
  exact (_paco_fold (t := t) gf).
Qed.

Theorem paco8_unfold: forall (MON: monotone8 gf) r,
  paco8 gf r <8= gf (upaco8 gf r).
Proof.
  exact (_paco_unfold (t := t) gf).
Qed.

End Arg8.

Arguments paco8_acc : clear implicits.
Arguments paco8_mon : clear implicits.
Arguments upaco8_mon : clear implicits.
Arguments paco8_mult_strong : clear implicits.
Arguments paco8_mult : clear implicits.
Arguments paco8_fold : clear implicits.
Arguments paco8_unfold : clear implicits.

Global Instance paco8_inst  (gf : rel8 T0 T1 T2 T3 T4 T5 T6 T7->_) r x0 x1 x2 x3 x4 x5 x6 x7 : paco_class (paco8 gf r x0 x1 x2 x3 x4 x5 x6 x7) :=
{ pacoacc    := paco8_acc gf;
  pacomult   := paco8_mult gf;
  pacofold   := paco8_fold gf;
  pacounfold := paco8_unfold gf }.

End PACO8.

Global Opaque paco8.

Hint Unfold upaco8 : core.
Hint Resolve paco8_fold : core.
Hint Unfold monotone8 : core.

