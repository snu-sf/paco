Require Export Program.Basics. Open Scope program_scope.
From Paco Require Import paconotation_internal paco_internal pacotac_internal paco_currying.
From Paco Require Export paconotation.
Set Implicit Arguments.

Section PACO0.


(** ** Predicates of Arity 0
*)

Definition t : arityn 0 := Eval compute in (
    arityn0).

Definition paco0(gf : rel0 -> rel0)(r: rel0) : rel0 :=
  _paco (t := t) gf r.

Definition upaco0(gf : rel0 -> rel0)(r: rel0) := paco0 gf r \0/ r.
Arguments paco0 : clear implicits.
Arguments upaco0 : clear implicits.
Hint Unfold upaco0 : core.

Definition monotone0 (gf: rel0 -> rel0) :=
  forall r r' (LE: r <0= r'), gf r <0= gf r'.

Lemma monotone0_compose : forall (gf gf': rel0 -> rel0)
      (MON1: monotone0 gf)
      (MON2: monotone0 gf'),
  monotone0 (compose gf gf').
Proof.
  exact (_monotone_compose (t := t)).
Qed.

Lemma monotone0_union : forall (gf gf': rel0 -> rel0)
      (MON1: monotone0 gf)
      (MON2: monotone0 gf'),
  monotone0 (gf \1/ gf').
Proof.
  exact (_monotone_union (t := t)).
Qed.

Lemma paco0_mon_gen : forall (gf gf': rel0 -> rel0)
    (LEgf: gf <1= gf')
    r r' (LEr: r <0= r'),
  paco0 gf r <0= paco0 gf' r'.
Proof.
  exact (_paco_mon_gen (t := t)).
Qed.

Lemma paco0_mon_bot : forall (gf gf': rel0 -> rel0) r'
    (LEgf: gf <1= gf'),
  paco0 gf bot0 <0= paco0 gf' r'.
Proof.
  exact (_paco_mon_bot (t := t)).
Qed.

Lemma upaco0_mon_gen : forall (gf gf': rel0 -> rel0)
    (LEgf: gf <1= gf')
    r r' (LEr: r <0= r'),
  upaco0 gf r <0= upaco0 gf' r'.
Proof.
  exact (_upaco_mon_gen (t := t)).
Qed.

Lemma upaco0_mon_bot : forall (gf gf': rel0 -> rel0) r'
    (LEgf: gf <1= gf'),
  upaco0 gf bot0 <0= upaco0 gf' r'.
Proof.
  exact (_upaco_mon_bot (t := t)).
Qed.

Section Arg0.

Variable gf : rel0 -> rel0.
Arguments gf : clear implicits.

Theorem paco0_acc: forall
  l r (OBG: forall rr (INC: r <0= rr) (CIH: l <0= rr), l <0= paco0 gf rr),
  l <0= paco0 gf r.
Proof.
  exact (_paco_acc (t := t) gf).
Qed.

Theorem paco0_mon: monotone0 (paco0 gf).
Proof.
  exact (_paco_mon (t := t) gf).
Qed.

Theorem upaco0_mon: monotone0 (upaco0 gf).
Proof.
  exact (_upaco_mon (t := t) gf).
Qed.

Theorem paco0_mult_strong: forall r,
  paco0 gf (upaco0 gf r) <0= paco0 gf r.
Proof.
  exact (_paco_mult_strong (t := t) gf).
Qed.

Corollary paco0_mult: forall r,
  paco0 gf (paco0 gf r) <0= paco0 gf r.
Proof.
  exact (_paco_mult (t := t) gf).
Qed.

Theorem paco0_fold: forall r,
  gf (upaco0 gf r) <0= paco0 gf r.
Proof.
  exact (_paco_fold (t := t) (upaco_spec t) gf).
Qed.

Theorem paco0_unfold: forall (MON: monotone0 gf) r,
  paco0 gf r <0= gf (upaco0 gf r).
Proof.
  exact (_paco_unfold (t := t) gf).
Qed.

End Arg0.

Arguments paco0_acc : clear implicits.
Arguments paco0_mon : clear implicits.
Arguments upaco0_mon : clear implicits.
Arguments paco0_mult_strong : clear implicits.
Arguments paco0_mult : clear implicits.
Arguments paco0_fold : clear implicits.
Arguments paco0_unfold : clear implicits.

Global Instance paco0_inst  (gf : rel0->_) r : paco_class (paco0 gf r) :=
{ pacoacc    := paco0_acc gf;
  pacomult   := paco0_mult gf;
  pacofold   := paco0_fold gf;
  pacounfold := paco0_unfold gf }.

End PACO0.

Global Opaque paco0.

Hint Unfold upaco0 : core.
Hint Resolve paco0_fold : core.
Hint Unfold monotone0 : core.

