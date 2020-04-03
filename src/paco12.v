Require Export Program.Basics. Open Scope program_scope.
From Paco Require Import paconotation_internal paco_internal pacotac_internal paco_currying.
From Paco Require Export paconotation.
Set Implicit Arguments.

Section PACO12.

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
Variable T10 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8), Type.
Variable T11 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9), Type.

(** ** Predicates of Arity 12
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
    arityS (@T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (fun x10 =>
    arityS (@T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) (fun x11 =>
    arity0))))))))))))).

Definition paco12(gf : rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11)(r: rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11) : rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 :=
  _paco (t := t) gf r.

Definition upaco12(gf : rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11)(r: rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11) := paco12 gf r \12/ r.
Arguments paco12 : clear implicits.
Arguments upaco12 : clear implicits.
Hint Unfold upaco12 : core.

Definition monotone12 (gf: rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11) :=
  forall r r' (LE: r <12= r'), gf r <12= gf r'.

Lemma monotone12_compose : forall (gf gf': rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11)
      (MON1: monotone12 gf)
      (MON2: monotone12 gf'),
  monotone12 (compose gf gf').
Proof.
  exact (_monotone_compose (t := t)).
Qed.

Lemma monotone12_union : forall (gf gf': rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11)
      (MON1: monotone12 gf)
      (MON2: monotone12 gf'),
  monotone12 (gf \13/ gf').
Proof.
  exact (_monotone_union (t := t)).
Qed.

Lemma paco12_mon_gen : forall (gf gf': rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11)
    (LEgf: gf <13= gf')
    r r' (LEr: r <12= r'),
  paco12 gf r <12= paco12 gf' r'.
Proof.
  exact (_paco_mon_gen (t := t)).
Qed.

Lemma paco12_mon_bot : forall (gf gf': rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11) r'
    (LEgf: gf <13= gf'),
  paco12 gf bot12 <12= paco12 gf' r'.
Proof.
  exact (_paco_mon_bot (t := t)).
Qed.

Lemma upaco12_mon_gen : forall (gf gf': rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11)
    (LEgf: gf <13= gf')
    r r' (LEr: r <12= r'),
  upaco12 gf r <12= upaco12 gf' r'.
Proof.
  exact (_upaco_mon_gen (t := t)).
Qed.

Lemma upaco12_mon_bot : forall (gf gf': rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11) r'
    (LEgf: gf <13= gf'),
  upaco12 gf bot12 <12= upaco12 gf' r'.
Proof.
  exact (_upaco_mon_bot (t := t)).
Qed.

Section Arg12.

Variable gf : rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 -> rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11.
Arguments gf : clear implicits.

Theorem paco12_acc: forall
  l r (OBG: forall rr (INC: r <12= rr) (CIH: l <12= rr), l <12= paco12 gf rr),
  l <12= paco12 gf r.
Proof.
  exact (_paco_acc (t := t) gf).
Qed.

Theorem paco12_mon: monotone12 (paco12 gf).
Proof.
  exact (_paco_mon (t := t) gf).
Qed.

Theorem upaco12_mon: monotone12 (upaco12 gf).
Proof.
  exact (_upaco_mon (t := t) gf).
Qed.

Theorem paco12_mult_strong: forall r,
  paco12 gf (upaco12 gf r) <12= paco12 gf r.
Proof.
  exact (_paco_mult_strong (t := t) gf).
Qed.

Corollary paco12_mult: forall r,
  paco12 gf (paco12 gf r) <12= paco12 gf r.
Proof.
  exact (_paco_mult (t := t) gf).
Qed.

Theorem paco12_fold: forall (MON: monotone12 gf) r,
  gf (upaco12 gf r) <12= paco12 gf r.
Proof.
  exact (_paco_fold (t := t) gf).
Qed.

Theorem paco12_unfold: forall (MON: monotone12 gf) r,
  paco12 gf r <12= gf (upaco12 gf r).
Proof.
  exact (_paco_unfold (t := t) gf).
Qed.

End Arg12.

Arguments paco12_acc : clear implicits.
Arguments paco12_mon : clear implicits.
Arguments upaco12_mon : clear implicits.
Arguments paco12_mult_strong : clear implicits.
Arguments paco12_mult : clear implicits.
Arguments paco12_fold : clear implicits.
Arguments paco12_unfold : clear implicits.

Global Instance paco12_inst  (gf : rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11->_) r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : paco_class (paco12 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) :=
{ pacoacc    := paco12_acc gf;
  pacomult   := paco12_mult gf;
  pacofold   := paco12_fold gf;
  pacounfold := paco12_unfold gf }.

End PACO12.

Global Opaque paco12.

Hint Unfold upaco12 : core.
Hint Resolve paco12_fold : core.
Hint Unfold monotone12 : core.

