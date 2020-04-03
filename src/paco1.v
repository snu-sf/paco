Require Export Program.Basics. Open Scope program_scope.
From Paco Require Import paconotation_internal paco_internal pacotac_internal paco_currying.
From Paco Require Export paconotation.
Set Implicit Arguments.

Section PACO1.

Variable T0 : Type.

(** ** Predicates of Arity 1
*)

Notation t := (
    arityS (@T0) (fun x0 =>
    arity0)).

Definition paco1(gf : rel1 T0 -> rel1 T0)(r: rel1 T0) : rel1 T0 :=
  _paco (t := t) gf r.

Definition upaco1(gf : rel1 T0 -> rel1 T0)(r: rel1 T0) := paco1 gf r \1/ r.
Arguments paco1 : clear implicits.
Arguments upaco1 : clear implicits.
Hint Unfold upaco1 : core.

Definition monotone1 (gf: rel1 T0 -> rel1 T0) :=
  forall r r' (LE: r <1= r'), gf r <1= gf r'.

Lemma monotone1_compose : forall (gf gf': rel1 T0 -> rel1 T0)
      (MON1: monotone1 gf)
      (MON2: monotone1 gf'),
  monotone1 (compose gf gf').
Proof.
  exact (_monotone_compose (t := t)).
Qed.

Lemma monotone1_union : forall (gf gf': rel1 T0 -> rel1 T0)
      (MON1: monotone1 gf)
      (MON2: monotone1 gf'),
  monotone1 (gf \2/ gf').
Proof.
  exact (_monotone_union (t := t)).
Qed.

Lemma paco1_mon_gen : forall (gf gf': rel1 T0 -> rel1 T0)
    (LEgf: gf <2= gf')
    r r' (LEr: r <1= r'),
  paco1 gf r <1= paco1 gf' r'.
Proof.
  exact (_paco_mon_gen (t := t)).
Qed.

Lemma paco1_mon_bot : forall (gf gf': rel1 T0 -> rel1 T0) r'
    (LEgf: gf <2= gf'),
  paco1 gf bot1 <1= paco1 gf' r'.
Proof.
  exact (_paco_mon_bot (t := t)).
Qed.

Lemma upaco1_mon_gen : forall (gf gf': rel1 T0 -> rel1 T0)
    (LEgf: gf <2= gf')
    r r' (LEr: r <1= r'),
  upaco1 gf r <1= upaco1 gf' r'.
Proof.
  exact (_upaco_mon_gen (t := t)).
Qed.

Lemma upaco1_mon_bot : forall (gf gf': rel1 T0 -> rel1 T0) r'
    (LEgf: gf <2= gf'),
  upaco1 gf bot1 <1= upaco1 gf' r'.
Proof.
  exact (_upaco_mon_bot (t := t)).
Qed.

Section Arg1.

Variable gf : rel1 T0 -> rel1 T0.
Arguments gf : clear implicits.

Theorem paco1_acc: forall
  l r (OBG: forall rr (INC: r <1= rr) (CIH: l <1= rr), l <1= paco1 gf rr),
  l <1= paco1 gf r.
Proof.
  exact (_paco_acc (t := t) gf).
Qed.

Theorem paco1_mon: monotone1 (paco1 gf).
Proof.
  exact (_paco_mon (t := t) gf).
Qed.

Theorem upaco1_mon: monotone1 (upaco1 gf).
Proof.
  exact (_upaco_mon (t := t) gf).
Qed.

Theorem paco1_mult_strong: forall r,
  paco1 gf (upaco1 gf r) <1= paco1 gf r.
Proof.
  exact (_paco_mult_strong (t := t) gf).
Qed.

Corollary paco1_mult: forall r,
  paco1 gf (paco1 gf r) <1= paco1 gf r.
Proof.
  exact (_paco_mult (t := t) gf).
Qed.

Theorem paco1_fold: forall (MON: monotone1 gf) r,
  gf (upaco1 gf r) <1= paco1 gf r.
Proof.
  exact (_paco_fold (t := t) gf).
Qed.

Theorem paco1_unfold: forall (MON: monotone1 gf) r,
  paco1 gf r <1= gf (upaco1 gf r).
Proof.
  exact (_paco_unfold (t := t) gf).
Qed.

End Arg1.

Arguments paco1_acc : clear implicits.
Arguments paco1_mon : clear implicits.
Arguments upaco1_mon : clear implicits.
Arguments paco1_mult_strong : clear implicits.
Arguments paco1_mult : clear implicits.
Arguments paco1_fold : clear implicits.
Arguments paco1_unfold : clear implicits.

Global Instance paco1_inst  (gf : rel1 T0->_) r x0 : paco_class (paco1 gf r x0) :=
{ pacoacc    := paco1_acc gf;
  pacomult   := paco1_mult gf;
  pacofold   := paco1_fold gf;
  pacounfold := paco1_unfold gf }.

End PACO1.

Global Opaque paco1.

Hint Unfold upaco1 : core.
Hint Resolve paco1_fold : core.
Hint Unfold monotone1 : core.

