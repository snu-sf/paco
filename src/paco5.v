Require Export Program.Basics. Open Scope program_scope.
From Paco Require Import paconotation_internal paco_internal pacotac_internal paco_currying.
From Paco Require Export paconotation.
Set Implicit Arguments.

Section PACO5.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.

(** ** Predicates of Arity 5
*)

Notation t := (
    arityS (@T0) (fun x0 =>
    arityS (@T1 x0) (fun x1 =>
    arityS (@T2 x0 x1) (fun x2 =>
    arityS (@T3 x0 x1 x2) (fun x3 =>
    arityS (@T4 x0 x1 x2 x3) (fun x4 =>
    arity0)))))).

Definition paco5(gf : rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4)(r: rel5 T0 T1 T2 T3 T4) : rel5 T0 T1 T2 T3 T4 :=
  _paco (t := t) gf r.

Definition upaco5(gf : rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4)(r: rel5 T0 T1 T2 T3 T4) := paco5 gf r \5/ r.
Arguments paco5 : clear implicits.
Arguments upaco5 : clear implicits.
Hint Unfold upaco5 : core.

Definition monotone5 (gf: rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4) :=
  forall r r' (LE: r <5= r'), gf r <5= gf r'.

Lemma monotone5_compose : forall (gf gf': rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4)
      (MON1: monotone5 gf)
      (MON2: monotone5 gf'),
  monotone5 (compose gf gf').
Proof.
  exact (_monotone_compose (t := t)).
Qed.

Lemma monotone5_union : forall (gf gf': rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4)
      (MON1: monotone5 gf)
      (MON2: monotone5 gf'),
  monotone5 (gf \6/ gf').
Proof.
  exact (_monotone_union (t := t)).
Qed.

Lemma paco5_mon_gen : forall (gf gf': rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4)
    (LEgf: gf <6= gf')
    r r' (LEr: r <5= r'),
  paco5 gf r <5= paco5 gf' r'.
Proof.
  exact (_paco_mon_gen (t := t)).
Qed.

Lemma paco5_mon_bot : forall (gf gf': rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4) r'
    (LEgf: gf <6= gf'),
  paco5 gf bot5 <5= paco5 gf' r'.
Proof.
  exact (_paco_mon_bot (t := t)).
Qed.

Lemma upaco5_mon_gen : forall (gf gf': rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4)
    (LEgf: gf <6= gf')
    r r' (LEr: r <5= r'),
  upaco5 gf r <5= upaco5 gf' r'.
Proof.
  exact (_upaco_mon_gen (t := t)).
Qed.

Lemma upaco5_mon_bot : forall (gf gf': rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4) r'
    (LEgf: gf <6= gf'),
  upaco5 gf bot5 <5= upaco5 gf' r'.
Proof.
  exact (_upaco_mon_bot (t := t)).
Qed.

Section Arg5.

Variable gf : rel5 T0 T1 T2 T3 T4 -> rel5 T0 T1 T2 T3 T4.
Arguments gf : clear implicits.

Theorem paco5_acc: forall
  l r (OBG: forall rr (INC: r <5= rr) (CIH: l <5= rr), l <5= paco5 gf rr),
  l <5= paco5 gf r.
Proof.
  exact (_paco_acc (t := t) gf).
Qed.

Theorem paco5_mon: monotone5 (paco5 gf).
Proof.
  exact (_paco_mon (t := t) gf).
Qed.

Theorem upaco5_mon: monotone5 (upaco5 gf).
Proof.
  exact (_upaco_mon (t := t) gf).
Qed.

Theorem paco5_mult_strong: forall r,
  paco5 gf (upaco5 gf r) <5= paco5 gf r.
Proof.
  exact (_paco_mult_strong (t := t) gf).
Qed.

Corollary paco5_mult: forall r,
  paco5 gf (paco5 gf r) <5= paco5 gf r.
Proof.
  exact (_paco_mult (t := t) gf).
Qed.

Theorem paco5_fold: forall (MON: monotone5 gf) r,
  gf (upaco5 gf r) <5= paco5 gf r.
Proof.
  exact (_paco_fold (t := t) gf).
Qed.

Theorem paco5_unfold: forall (MON: monotone5 gf) r,
  paco5 gf r <5= gf (upaco5 gf r).
Proof.
  exact (_paco_unfold (t := t) gf).
Qed.

End Arg5.

Arguments paco5_acc : clear implicits.
Arguments paco5_mon : clear implicits.
Arguments upaco5_mon : clear implicits.
Arguments paco5_mult_strong : clear implicits.
Arguments paco5_mult : clear implicits.
Arguments paco5_fold : clear implicits.
Arguments paco5_unfold : clear implicits.

Global Instance paco5_inst  (gf : rel5 T0 T1 T2 T3 T4->_) r x0 x1 x2 x3 x4 : paco_class (paco5 gf r x0 x1 x2 x3 x4) :=
{ pacoacc    := paco5_acc gf;
  pacomult   := paco5_mult gf;
  pacofold   := paco5_fold gf;
  pacounfold := paco5_unfold gf }.

End PACO5.

Global Opaque paco5.

Hint Unfold upaco5 : core.
Hint Resolve paco5_fold : core.
Hint Unfold monotone5 : core.

