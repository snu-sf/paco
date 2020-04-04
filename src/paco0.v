
Require Export Program.Basics. Open Scope program_scope.
From Paco Require Import paconotation_internal paco_internal pacotac_internal paco_currying.
From Paco Require Export paconotation.
Set Implicit Arguments.

Generalizable Variables T.

Module Import paco0.
Section PACO.

Local Open Scope paco_scope.
Local Notation rel := (rel0).
Local Notation "r <= r'" := (r <0= r') : paco_scope.
Local Notation "r <1= r'" := (r <1= r') : paco_scope.
Local Notation "r \/ r'" := (r \0/ r') : paco_scope.
Local Notation "r \1/ r'" := (r \1/ r') : paco_scope.

(** ** Predicates of Arity 0 *)

Let t : arityn 0 := Eval compute in (
    arityn0).


Definition _paco (gf : rel -> rel) (r : rel) : rel :=
  _paco (t := t) gf r.
Arguments _paco : clear implicits.

Inductive paco0 (gf : rel -> rel) (r : rel)  : Prop :=
  internal_mk_paco (_ : _paco gf r).

Definition upaco0 (gf : rel -> rel) (r : rel) : rel := paco0 gf r \/ r.
Arguments paco0 : clear implicits.
Arguments upaco0 : clear implicits.
Hint Unfold upaco0 : core.

Local Notation bot := bot0.
Local Notation paco := paco0.
Local Notation upaco := upaco0.

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


Definition inst (gf : rel->_) r : paco_class (paco gf r) := {|

  pacoacc    := @acc gf;
  pacomult   := @mult gf;
  pacofold   := @fold gf;
  pacounfold := @unfold gf |}.

End PACO.

End paco0.

Hint Unfold upaco0 : core.
Hint Resolve fold : core.
Hint Unfold monotone : core.
Existing Instance inst.

Notation paco0 := paco0.paco0.
Notation upaco0 := paco0.upaco0.
Notation monotone0 := paco0.monotone.
