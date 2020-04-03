Require Export Program.Basics. Open Scope program_scope.
From Paco Require Import paconotation_internal paco_internal pacotac_internal paco_currying.
From Paco Require Export paconotation.
Set Implicit Arguments.

Section PACO4.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.

(** ** Predicates of Arity 4
*)

Notation t := (
    arityS (@T0) (fun x0 =>
    arityS (@T1 x0) (fun x1 =>
    arityS (@T2 x0 x1) (fun x2 =>
    arityS (@T3 x0 x1 x2) (fun x3 =>
    arity0))))).

Definition paco4(gf : rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3)(r: rel4 T0 T1 T2 T3) : rel4 T0 T1 T2 T3 :=
  _paco (t := t) gf r.

Definition upaco4(gf : rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3)(r: rel4 T0 T1 T2 T3) := paco4 gf r \4/ r.
Arguments paco4 : clear implicits.
Arguments upaco4 : clear implicits.
Hint Unfold upaco4 : core.

Definition monotone4 (gf: rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3) :=
  forall r r' (LE: r <4= r'), gf r <4= gf r'.

Lemma monotone4_compose : forall (gf gf': rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3)
      (MON1: monotone4 gf)
      (MON2: monotone4 gf'),
  monotone4 (compose gf gf').
Proof.
  exact (_monotone_compose (t := t)).
Qed.

Lemma monotone4_union : forall (gf gf': rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3)
      (MON1: monotone4 gf)
      (MON2: monotone4 gf'),
  monotone4 (gf \5/ gf').
Proof.
  exact (_monotone_union (t := t)).
Qed.

Lemma paco4_mon_gen : forall (gf gf': rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3)
    (LEgf: gf <5= gf')
    r r' (LEr: r <4= r'),
  paco4 gf r <4= paco4 gf' r'.
Proof.
  exact (_paco_mon_gen (t := t)).
Qed.

Lemma paco4_mon_bot : forall (gf gf': rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3) r'
    (LEgf: gf <5= gf'),
  paco4 gf bot4 <4= paco4 gf' r'.
Proof.
  exact (_paco_mon_bot (t := t)).
Qed.

Lemma upaco4_mon_gen : forall (gf gf': rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3)
    (LEgf: gf <5= gf')
    r r' (LEr: r <4= r'),
  upaco4 gf r <4= upaco4 gf' r'.
Proof.
  exact (_upaco_mon_gen (t := t)).
Qed.

Lemma upaco4_mon_bot : forall (gf gf': rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3) r'
    (LEgf: gf <5= gf'),
  upaco4 gf bot4 <4= upaco4 gf' r'.
Proof.
  exact (_upaco_mon_bot (t := t)).
Qed.

Section Arg4.

Variable gf : rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3.
Arguments gf : clear implicits.

Theorem paco4_acc: forall
  l r (OBG: forall rr (INC: r <4= rr) (CIH: l <4= rr), l <4= paco4 gf rr),
  l <4= paco4 gf r.
Proof.
  exact (_paco_acc (t := t) gf).
Qed.

Theorem paco4_mon: monotone4 (paco4 gf).
Proof.
  exact (_paco_mon (t := t) gf).
Qed.

Theorem upaco4_mon: monotone4 (upaco4 gf).
Proof.
  exact (_upaco_mon (t := t) gf).
Qed.

Theorem paco4_mult_strong: forall r,
  paco4 gf (upaco4 gf r) <4= paco4 gf r.
Proof.
  exact (_paco_mult_strong (t := t) gf).
Qed.

Corollary paco4_mult: forall r,
  paco4 gf (paco4 gf r) <4= paco4 gf r.
Proof.
  exact (_paco_mult (t := t) gf).
Qed.

Theorem paco4_fold: forall (MON: monotone4 gf) r,
  gf (upaco4 gf r) <4= paco4 gf r.
Proof.
  exact (_paco_fold (t := t) gf).
Qed.

Theorem paco4_unfold: forall (MON: monotone4 gf) r,
  paco4 gf r <4= gf (upaco4 gf r).
Proof.
  exact (_paco_unfold (t := t) gf).
Qed.

End Arg4.

Arguments paco4_acc : clear implicits.
Arguments paco4_mon : clear implicits.
Arguments upaco4_mon : clear implicits.
Arguments paco4_mult_strong : clear implicits.
Arguments paco4_mult : clear implicits.
Arguments paco4_fold : clear implicits.
Arguments paco4_unfold : clear implicits.

Global Instance paco4_inst  (gf : rel4 T0 T1 T2 T3->_) r x0 x1 x2 x3 : paco_class (paco4 gf r x0 x1 x2 x3) :=
{ pacoacc    := paco4_acc gf;
  pacomult   := paco4_mult gf;
  pacofold   := paco4_fold gf;
  pacounfold := paco4_unfold gf }.

End PACO4.

Global Opaque paco4.

Hint Unfold upaco4 : core.
Hint Resolve paco4_fold : core.
Hint Unfold monotone4 : core.

