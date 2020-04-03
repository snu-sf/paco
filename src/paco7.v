Require Export Program.Basics. Open Scope program_scope.
From Paco Require Import paconotation_internal paco_internal pacotac_internal paco_currying.
From Paco Require Export paconotation.
Set Implicit Arguments.

Section PACO7.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.

(** ** Predicates of Arity 7
*)

Notation t := (
    arityS (@T0) (fun x0 =>
    arityS (@T1 x0) (fun x1 =>
    arityS (@T2 x0 x1) (fun x2 =>
    arityS (@T3 x0 x1 x2) (fun x3 =>
    arityS (@T4 x0 x1 x2 x3) (fun x4 =>
    arityS (@T5 x0 x1 x2 x3 x4) (fun x5 =>
    arityS (@T6 x0 x1 x2 x3 x4 x5) (fun x6 =>
    arity0)))))))).

Definition paco7(gf : rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6)(r: rel7 T0 T1 T2 T3 T4 T5 T6) : rel7 T0 T1 T2 T3 T4 T5 T6 :=
  _paco (t := t) gf r.

Definition upaco7(gf : rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6)(r: rel7 T0 T1 T2 T3 T4 T5 T6) := paco7 gf r \7/ r.
Arguments paco7 : clear implicits.
Arguments upaco7 : clear implicits.
Hint Unfold upaco7 : core.

Definition monotone7 (gf: rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6) :=
  forall r r' (LE: r <7= r'), gf r <7= gf r'.

Lemma monotone7_compose : forall (gf gf': rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6)
      (MON1: monotone7 gf)
      (MON2: monotone7 gf'),
  monotone7 (compose gf gf').
Proof.
  exact (_monotone_compose (t := t)).
Qed.

Lemma monotone7_union : forall (gf gf': rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6)
      (MON1: monotone7 gf)
      (MON2: monotone7 gf'),
  monotone7 (gf \8/ gf').
Proof.
  exact (_monotone_union (t := t)).
Qed.

Lemma paco7_mon_gen : forall (gf gf': rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6)
    (LEgf: gf <8= gf')
    r r' (LEr: r <7= r'),
  paco7 gf r <7= paco7 gf' r'.
Proof.
  exact (_paco_mon_gen (t := t)).
Qed.

Lemma paco7_mon_bot : forall (gf gf': rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6) r'
    (LEgf: gf <8= gf'),
  paco7 gf bot7 <7= paco7 gf' r'.
Proof.
  exact (_paco_mon_bot (t := t)).
Qed.

Lemma upaco7_mon_gen : forall (gf gf': rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6)
    (LEgf: gf <8= gf')
    r r' (LEr: r <7= r'),
  upaco7 gf r <7= upaco7 gf' r'.
Proof.
  exact (_upaco_mon_gen (t := t)).
Qed.

Lemma upaco7_mon_bot : forall (gf gf': rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6) r'
    (LEgf: gf <8= gf'),
  upaco7 gf bot7 <7= upaco7 gf' r'.
Proof.
  exact (_upaco_mon_bot (t := t)).
Qed.

Section Arg7.

Variable gf : rel7 T0 T1 T2 T3 T4 T5 T6 -> rel7 T0 T1 T2 T3 T4 T5 T6.
Arguments gf : clear implicits.

Theorem paco7_acc: forall
  l r (OBG: forall rr (INC: r <7= rr) (CIH: l <7= rr), l <7= paco7 gf rr),
  l <7= paco7 gf r.
Proof.
  exact (_paco_acc (t := t) gf).
Qed.

Theorem paco7_mon: monotone7 (paco7 gf).
Proof.
  exact (_paco_mon (t := t) gf).
Qed.

Theorem upaco7_mon: monotone7 (upaco7 gf).
Proof.
  exact (_upaco_mon (t := t) gf).
Qed.

Theorem paco7_mult_strong: forall r,
  paco7 gf (upaco7 gf r) <7= paco7 gf r.
Proof.
  exact (_paco_mult_strong (t := t) gf).
Qed.

Corollary paco7_mult: forall r,
  paco7 gf (paco7 gf r) <7= paco7 gf r.
Proof.
  exact (_paco_mult (t := t) gf).
Qed.

Theorem paco7_fold: forall (MON: monotone7 gf) r,
  gf (upaco7 gf r) <7= paco7 gf r.
Proof.
  exact (_paco_fold (t := t) gf).
Qed.

Theorem paco7_unfold: forall (MON: monotone7 gf) r,
  paco7 gf r <7= gf (upaco7 gf r).
Proof.
  exact (_paco_unfold (t := t) gf).
Qed.

End Arg7.

Arguments paco7_acc : clear implicits.
Arguments paco7_mon : clear implicits.
Arguments upaco7_mon : clear implicits.
Arguments paco7_mult_strong : clear implicits.
Arguments paco7_mult : clear implicits.
Arguments paco7_fold : clear implicits.
Arguments paco7_unfold : clear implicits.

Global Instance paco7_inst  (gf : rel7 T0 T1 T2 T3 T4 T5 T6->_) r x0 x1 x2 x3 x4 x5 x6 : paco_class (paco7 gf r x0 x1 x2 x3 x4 x5 x6) :=
{ pacoacc    := paco7_acc gf;
  pacomult   := paco7_mult gf;
  pacofold   := paco7_fold gf;
  pacounfold := paco7_unfold gf }.

End PACO7.

Global Opaque paco7.

Hint Unfold upaco7 : core.
Hint Resolve paco7_fold : core.
Hint Unfold monotone7 : core.

