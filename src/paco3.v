Require Export Program.Basics. Open Scope program_scope.
From Paco Require Import paconotation_internal paco_internal pacotac_internal paco_currying.
From Paco Require Export paconotation.
Set Implicit Arguments.

Section PACO3.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.

(** ** Predicates of Arity 3
*)

Definition t : arityn 3 := Eval compute in (
    aritynS (@T0) (fun x0 =>
    aritynS (@T1 x0) (fun x1 =>
    aritynS (@T2 x0 x1) (fun x2 =>
    arityn0)))).

Definition paco3(gf : rel3 T0 T1 T2 -> rel3 T0 T1 T2)(r: rel3 T0 T1 T2) : rel3 T0 T1 T2 :=
  _paco (t := t) gf r.

Definition upaco3(gf : rel3 T0 T1 T2 -> rel3 T0 T1 T2)(r: rel3 T0 T1 T2) := paco3 gf r \3/ r.
Arguments paco3 : clear implicits.
Arguments upaco3 : clear implicits.
Hint Unfold upaco3 : core.

Definition monotone3 (gf: rel3 T0 T1 T2 -> rel3 T0 T1 T2) :=
  forall r r' (LE: r <3= r'), gf r <3= gf r'.

Lemma monotone3_compose : forall (gf gf': rel3 T0 T1 T2 -> rel3 T0 T1 T2)
      (MON1: monotone3 gf)
      (MON2: monotone3 gf'),
  monotone3 (compose gf gf').
Proof.
  exact (_monotone_compose (t := t)).
Qed.

Lemma monotone3_union : forall (gf gf': rel3 T0 T1 T2 -> rel3 T0 T1 T2)
      (MON1: monotone3 gf)
      (MON2: monotone3 gf'),
  monotone3 (gf \4/ gf').
Proof.
  exact (_monotone_union (t := t)).
Qed.

Lemma paco3_mon_gen : forall (gf gf': rel3 T0 T1 T2 -> rel3 T0 T1 T2)
    (LEgf: gf <4= gf')
    r r' (LEr: r <3= r'),
  paco3 gf r <3= paco3 gf' r'.
Proof.
  exact (_paco_mon_gen (t := t)).
Qed.

Lemma paco3_mon_bot : forall (gf gf': rel3 T0 T1 T2 -> rel3 T0 T1 T2) r'
    (LEgf: gf <4= gf'),
  paco3 gf bot3 <3= paco3 gf' r'.
Proof.
  exact (_paco_mon_bot (t := t)).
Qed.

Lemma upaco3_mon_gen : forall (gf gf': rel3 T0 T1 T2 -> rel3 T0 T1 T2)
    (LEgf: gf <4= gf')
    r r' (LEr: r <3= r'),
  upaco3 gf r <3= upaco3 gf' r'.
Proof.
  exact (_upaco_mon_gen (t := t)).
Qed.

Lemma upaco3_mon_bot : forall (gf gf': rel3 T0 T1 T2 -> rel3 T0 T1 T2) r'
    (LEgf: gf <4= gf'),
  upaco3 gf bot3 <3= upaco3 gf' r'.
Proof.
  exact (_upaco_mon_bot (t := t)).
Qed.

Section Arg3.

Variable gf : rel3 T0 T1 T2 -> rel3 T0 T1 T2.
Arguments gf : clear implicits.

Theorem paco3_acc: forall
  l r (OBG: forall rr (INC: r <3= rr) (CIH: l <3= rr), l <3= paco3 gf rr),
  l <3= paco3 gf r.
Proof.
  exact (_paco_acc (t := t) gf).
Qed.

Theorem paco3_mon: monotone3 (paco3 gf).
Proof.
  exact (_paco_mon (t := t) gf).
Qed.

Theorem upaco3_mon: monotone3 (upaco3 gf).
Proof.
  exact (_upaco_mon (t := t) gf).
Qed.

Theorem paco3_mult_strong: forall r,
  paco3 gf (upaco3 gf r) <3= paco3 gf r.
Proof.
  exact (_paco_mult_strong (t := t) gf).
Qed.

Corollary paco3_mult: forall r,
  paco3 gf (paco3 gf r) <3= paco3 gf r.
Proof.
  exact (_paco_mult (t := t) gf).
Qed.

Theorem paco3_fold: forall r,
  gf (upaco3 gf r) <3= paco3 gf r.
Proof.
  exact (_paco_fold (t := t) (upaco_spec t) gf).
Qed.

Theorem paco3_unfold: forall (MON: monotone3 gf) r,
  paco3 gf r <3= gf (upaco3 gf r).
Proof.
  exact (_paco_unfold (t := t) gf).
Qed.

End Arg3.

Arguments paco3_acc : clear implicits.
Arguments paco3_mon : clear implicits.
Arguments upaco3_mon : clear implicits.
Arguments paco3_mult_strong : clear implicits.
Arguments paco3_mult : clear implicits.
Arguments paco3_fold : clear implicits.
Arguments paco3_unfold : clear implicits.

Global Instance paco3_inst  (gf : rel3 T0 T1 T2->_) r x0 x1 x2 : paco_class (paco3 gf r x0 x1 x2) :=
{ pacoacc    := paco3_acc gf;
  pacomult   := paco3_mult gf;
  pacofold   := paco3_fold gf;
  pacounfold := paco3_unfold gf }.

End PACO3.

Global Opaque paco3.

Hint Unfold upaco3 : core.
Hint Resolve paco3_fold : core.
Hint Unfold monotone3 : core.

