Require Export Program.Basics. Open Scope program_scope.
From Paco Require Import paconotation_internal paco_internal pacotac_internal paco_currying.
From Paco Require Export paconotation.
Set Implicit Arguments.

Section PACO2.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.

(** ** Predicates of Arity 2
*)

Notation t := (
    arityS (@T0) (fun x0 =>
    arityS (@T1 x0) (fun x1 =>
    arity0))).

Definition paco2(gf : rel2 T0 T1 -> rel2 T0 T1)(r: rel2 T0 T1) : rel2 T0 T1 :=
  _paco (t := t) gf r.

Definition upaco2(gf : rel2 T0 T1 -> rel2 T0 T1)(r: rel2 T0 T1) := paco2 gf r \2/ r.
Arguments paco2 : clear implicits.
Arguments upaco2 : clear implicits.
Hint Unfold upaco2 : core.

Definition monotone2 (gf: rel2 T0 T1 -> rel2 T0 T1) :=
  forall r r' (LE: r <2= r'), gf r <2= gf r'.

Lemma monotone2_compose : forall (gf gf': rel2 T0 T1 -> rel2 T0 T1)
      (MON1: monotone2 gf)
      (MON2: monotone2 gf'),
  monotone2 (compose gf gf').
Proof.
  exact (_monotone_compose (t := t)).
Qed.

Lemma monotone2_union : forall (gf gf': rel2 T0 T1 -> rel2 T0 T1)
      (MON1: monotone2 gf)
      (MON2: monotone2 gf'),
  monotone2 (gf \3/ gf').
Proof.
  exact (_monotone_union (t := t)).
Qed.

Lemma paco2_mon_gen : forall (gf gf': rel2 T0 T1 -> rel2 T0 T1)
    (LEgf: gf <3= gf')
    r r' (LEr: r <2= r'),
  paco2 gf r <2= paco2 gf' r'.
Proof.
  exact (_paco_mon_gen (t := t)).
Qed.

Lemma paco2_mon_bot : forall (gf gf': rel2 T0 T1 -> rel2 T0 T1) r'
    (LEgf: gf <3= gf'),
  paco2 gf bot2 <2= paco2 gf' r'.
Proof.
  exact (_paco_mon_bot (t := t)).
Qed.

Lemma upaco2_mon_gen : forall (gf gf': rel2 T0 T1 -> rel2 T0 T1)
    (LEgf: gf <3= gf')
    r r' (LEr: r <2= r'),
  upaco2 gf r <2= upaco2 gf' r'.
Proof.
  exact (_upaco_mon_gen (t := t)).
Qed.

Lemma upaco2_mon_bot : forall (gf gf': rel2 T0 T1 -> rel2 T0 T1) r'
    (LEgf: gf <3= gf'),
  upaco2 gf bot2 <2= upaco2 gf' r'.
Proof.
  exact (_upaco_mon_bot (t := t)).
Qed.

Section Arg2.

Variable gf : rel2 T0 T1 -> rel2 T0 T1.
Arguments gf : clear implicits.

Theorem paco2_acc: forall
  l r (OBG: forall rr (INC: r <2= rr) (CIH: l <2= rr), l <2= paco2 gf rr),
  l <2= paco2 gf r.
Proof.
  exact (_paco_acc (t := t) gf).
Qed.

Theorem paco2_mon: monotone2 (paco2 gf).
Proof.
  exact (_paco_mon (t := t) gf).
Qed.

Theorem upaco2_mon: monotone2 (upaco2 gf).
Proof.
  exact (_upaco_mon (t := t) gf).
Qed.

Theorem paco2_mult_strong: forall r,
  paco2 gf (upaco2 gf r) <2= paco2 gf r.
Proof.
  exact (_paco_mult_strong (t := t) gf).
Qed.

Corollary paco2_mult: forall r,
  paco2 gf (paco2 gf r) <2= paco2 gf r.
Proof.
  exact (_paco_mult (t := t) gf).
Qed.

Theorem paco2_fold: forall r,
  gf (upaco2 gf r) <2= paco2 gf r.
Proof.
  exact (_paco_fold (t := t) gf).
Qed.

Theorem paco2_unfold: forall (MON: monotone2 gf) r,
  paco2 gf r <2= gf (upaco2 gf r).
Proof.
  exact (_paco_unfold (t := t) gf).
Qed.

End Arg2.

Arguments paco2_acc : clear implicits.
Arguments paco2_mon : clear implicits.
Arguments upaco2_mon : clear implicits.
Arguments paco2_mult_strong : clear implicits.
Arguments paco2_mult : clear implicits.
Arguments paco2_fold : clear implicits.
Arguments paco2_unfold : clear implicits.

Global Instance paco2_inst  (gf : rel2 T0 T1->_) r x0 x1 : paco_class (paco2 gf r x0 x1) :=
{ pacoacc    := paco2_acc gf;
  pacomult   := paco2_mult gf;
  pacofold   := paco2_fold gf;
  pacounfold := paco2_unfold gf }.

End PACO2.

Global Opaque paco2.

Hint Unfold upaco2 : core.
Hint Resolve paco2_fold : core.
Hint Unfold monotone2 : core.

