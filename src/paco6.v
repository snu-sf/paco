Require Export Program.Basics. Open Scope program_scope.
From Paco Require Import paconotation_internal paco_internal pacotac_internal paco_currying.
From Paco Require Export paconotation.
Set Implicit Arguments.

Section PACO6.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.

(** ** Predicates of Arity 6
*)

Notation t := (
    arityS (@T0) (fun x0 =>
    arityS (@T1 x0) (fun x1 =>
    arityS (@T2 x0 x1) (fun x2 =>
    arityS (@T3 x0 x1 x2) (fun x3 =>
    arityS (@T4 x0 x1 x2 x3) (fun x4 =>
    arityS (@T5 x0 x1 x2 x3 x4) (fun x5 =>
    arity0))))))).

Definition paco6(gf : rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5)(r: rel6 T0 T1 T2 T3 T4 T5) : rel6 T0 T1 T2 T3 T4 T5 :=
  _paco (t := t) gf r.

Definition upaco6(gf : rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5)(r: rel6 T0 T1 T2 T3 T4 T5) := paco6 gf r \6/ r.
Arguments paco6 : clear implicits.
Arguments upaco6 : clear implicits.
Hint Unfold upaco6 : core.

Definition monotone6 (gf: rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5) :=
  forall r r' (LE: r <6= r'), gf r <6= gf r'.

Lemma monotone6_compose : forall (gf gf': rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5)
      (MON1: monotone6 gf)
      (MON2: monotone6 gf'),
  monotone6 (compose gf gf').
Proof.
  exact (_monotone_compose (t := t)).
Qed.

Lemma monotone6_union : forall (gf gf': rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5)
      (MON1: monotone6 gf)
      (MON2: monotone6 gf'),
  monotone6 (gf \7/ gf').
Proof.
  exact (_monotone_union (t := t)).
Qed.

Lemma paco6_mon_gen : forall (gf gf': rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5)
    (LEgf: gf <7= gf')
    r r' (LEr: r <6= r'),
  paco6 gf r <6= paco6 gf' r'.
Proof.
  exact (_paco_mon_gen (t := t)).
Qed.

Lemma paco6_mon_bot : forall (gf gf': rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5) r'
    (LEgf: gf <7= gf'),
  paco6 gf bot6 <6= paco6 gf' r'.
Proof.
  exact (_paco_mon_bot (t := t)).
Qed.

Lemma upaco6_mon_gen : forall (gf gf': rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5)
    (LEgf: gf <7= gf')
    r r' (LEr: r <6= r'),
  upaco6 gf r <6= upaco6 gf' r'.
Proof.
  exact (_upaco_mon_gen (t := t)).
Qed.

Lemma upaco6_mon_bot : forall (gf gf': rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5) r'
    (LEgf: gf <7= gf'),
  upaco6 gf bot6 <6= upaco6 gf' r'.
Proof.
  exact (_upaco_mon_bot (t := t)).
Qed.

Section Arg6.

Variable gf : rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5.
Arguments gf : clear implicits.

Theorem paco6_acc: forall
  l r (OBG: forall rr (INC: r <6= rr) (CIH: l <6= rr), l <6= paco6 gf rr),
  l <6= paco6 gf r.
Proof.
  exact (_paco_acc (t := t) gf).
Qed.

Theorem paco6_mon: monotone6 (paco6 gf).
Proof.
  exact (_paco_mon (t := t) gf).
Qed.

Theorem upaco6_mon: monotone6 (upaco6 gf).
Proof.
  exact (_upaco_mon (t := t) gf).
Qed.

Theorem paco6_mult_strong: forall r,
  paco6 gf (upaco6 gf r) <6= paco6 gf r.
Proof.
  exact (_paco_mult_strong (t := t) gf).
Qed.

Corollary paco6_mult: forall r,
  paco6 gf (paco6 gf r) <6= paco6 gf r.
Proof.
  exact (_paco_mult (t := t) gf).
Qed.

Theorem paco6_fold: forall (MON: monotone6 gf) r,
  gf (upaco6 gf r) <6= paco6 gf r.
Proof.
  exact (_paco_fold (t := t) gf).
Qed.

Theorem paco6_unfold: forall (MON: monotone6 gf) r,
  paco6 gf r <6= gf (upaco6 gf r).
Proof.
  exact (_paco_unfold (t := t) gf).
Qed.

End Arg6.

Arguments paco6_acc : clear implicits.
Arguments paco6_mon : clear implicits.
Arguments upaco6_mon : clear implicits.
Arguments paco6_mult_strong : clear implicits.
Arguments paco6_mult : clear implicits.
Arguments paco6_fold : clear implicits.
Arguments paco6_unfold : clear implicits.

Global Instance paco6_inst  (gf : rel6 T0 T1 T2 T3 T4 T5->_) r x0 x1 x2 x3 x4 x5 : paco_class (paco6 gf r x0 x1 x2 x3 x4 x5) :=
{ pacoacc    := paco6_acc gf;
  pacomult   := paco6_mult gf;
  pacofold   := paco6_fold gf;
  pacounfold := paco6_unfold gf }.

End PACO6.

Global Opaque paco6.

Hint Unfold upaco6 : core.
Hint Resolve paco6_fold : core.
Hint Unfold monotone6 : core.

