
Require Export Program.Basics. Open Scope program_scope.
From Paco Require Import paconotation_internal paco_internal pacotac_internal paco_currying.
From Paco Require Export paconotation.
Set Implicit Arguments.

Generalizable Variables T.

Module Import paco10.
Section PACO.

Context `{T9 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7), Type}.

Local Open Scope paco_scope.
Local Notation rel := (rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9).
Local Notation "r <= r'" := (r <10= r') : paco_scope.
Local Notation "r <1= r'" := (r <11= r') : paco_scope.
Local Notation "r \/ r'" := (r \10/ r') : paco_scope.
Local Notation "r \1/ r'" := (r \11/ r') : paco_scope.

(** ** Predicates of Arity 10 *)

Let t : arityn 10 := Eval compute in (
    aritynS (@T0) (fun x0 =>
    aritynS (@T1 x0) (fun x1 =>
    aritynS (@T2 x0 x1) (fun x2 =>
    aritynS (@T3 x0 x1 x2) (fun x3 =>
    aritynS (@T4 x0 x1 x2 x3) (fun x4 =>
    aritynS (@T5 x0 x1 x2 x3 x4) (fun x5 =>
    aritynS (@T6 x0 x1 x2 x3 x4 x5) (fun x6 =>
    aritynS (@T7 x0 x1 x2 x3 x4 x5 x6) (fun x7 =>
    aritynS (@T8 x0 x1 x2 x3 x4 x5 x6 x7) (fun x8 =>
    aritynS (@T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (fun x9 =>
    arityn0))))))))))).


Definition _paco (gf : rel -> rel) (r : rel) : rel :=
  _paco (t := t) gf r.
Arguments _paco : clear implicits.

Inductive paco10 (gf : rel -> rel) (r : rel)  x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Prop :=
  internal_mk_paco (_ : _paco gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9).

Definition upaco10 (gf : rel -> rel) (r : rel) : rel := paco10 gf r \/ r.
Arguments paco10 : clear implicits.
Arguments upaco10 : clear implicits.
Hint Unfold upaco10 : core.

Local Notation bot := bot10.
Local Notation paco := paco10.
Local Notation upaco := upaco10.

Let unpaco gf r :
  (paco gf r) <= (_paco gf r).
Proof. destruct 1; assumption. Qed.

Lemma spec_proof :
  let le (r r' : rel) : Prop := r <= r' in
  paco_spec (rel_ := rel) le bot paco upaco.
Proof. Time apply (paco_spec_proof t); [ exact internal_mk_paco | exact unpaco ]. Time Qed.

Definition monotone (gf: rel -> rel) :=
  forall r r' (LE: r <= r'), gf r <= gf r'.

Lemma monotone_compose : forall (gf gf': rel -> rel)
      (MON1: monotone gf)
      (MON2: monotone gf'),
  monotone (compose gf gf').
Proof. exact (_monotone_compose (t := t)). Qed.

Lemma monotone_union : forall (gf gf': rel -> rel)
      (MON1: monotone gf)
      (MON2: monotone gf'),
  monotone (gf \1/ gf').
Proof. exact (_monotone_union (t := t)). Qed.

Lemma mon_gen : forall (gf gf': rel -> rel)
    (LEgf: gf <1= gf')
    r r' (LEr: r <= r'),
  paco gf r <= paco gf' r'.
Proof. exact (_paco_mon_gen spec_proof). Qed.

Lemma mon_bot : forall (gf gf': rel -> rel) r'
    (LEgf: gf <1= gf'),
  paco gf bot <= paco gf' r'.
Proof. exact (_paco_mon_bot spec_proof). Qed.

Lemma u_mon_gen : forall (gf gf': rel -> rel)
    (LEgf: gf <1= gf')
    r r' (LEr: r <= r'),
  upaco gf r <= upaco gf' r'.
Proof. exact (_upaco_mon_gen spec_proof). Qed.

Lemma u_mon_bot : forall (gf gf': rel -> rel) r'
    (LEgf: gf <1= gf'),
  upaco gf bot <= upaco gf' r'.
Proof. exact (_upaco_mon_bot spec_proof). Qed.

Section Arg.

Variable gf : rel -> rel.
Arguments gf : clear implicits.

Theorem acc: forall
  l r (OBG: forall rr (INC: r <= rr) (CIH: l <= rr), l <= paco gf rr),
  l <= paco gf r.
Proof. exact (_paco_acc spec_proof gf). Qed.

Theorem mon: monotone (paco gf).
Proof. exact (_paco_mon spec_proof gf). Qed.

Theorem u_mon: monotone (upaco gf).
Proof. exact (_upaco_mon spec_proof gf). Qed.

Theorem mult_strong: forall r,
  paco gf (upaco gf r) <= paco gf r.
Proof. exact (_paco_mult_strong spec_proof gf). Qed.

Corollary mult: forall r,
  paco gf (paco gf r) <= paco gf r.
Proof. exact (_paco_mult spec_proof gf). Qed.

Theorem fold: forall r,
  gf (upaco gf r) <= paco gf r.
Proof. exact (_paco_fold spec_proof gf). Qed.

Theorem unfold: forall (MON: monotone gf) r,
  paco gf r <= gf (upaco gf r).
Proof. exact (_paco_unfold spec_proof gf). Qed.

End Arg.


Definition inst (gf : rel->_) r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : paco_class (paco gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) := {|

  pacoacc    := @acc gf;
  pacomult   := @mult gf;
  pacofold   := @fold gf;
  pacounfold := @unfold gf |}.

End PACO.

End paco10.

Hint Unfold upaco10 : core.
Hint Resolve fold : core.
Hint Unfold monotone : core.
Existing Instance inst.

Notation paco10 := paco10.paco10.
Notation upaco10 := paco10.upaco10.
Notation monotone10 := paco10.monotone.
