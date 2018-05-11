Require Export paconotation pacotacuser.
Require Import pacotac.
Set Implicit Arguments.

(** ** Predicates of Arity 10
*)

Section Arg10_def.
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
Variable gf : rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9.
Arguments gf : clear implicits.

CoInductive paco10( r: rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Prop :=
| paco10_pfold pco
    (LE : pco <10= (paco10 r \10/ r))
    (SIM: gf pco x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)
.
Definition upaco10( r: rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) := paco10 r \10/ r.
End Arg10_def.
Arguments paco10 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 ].
Arguments upaco10 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 ].
Hint Unfold upaco10.

Section Arg10_2_def.
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
Variable gf_0 gf_1 : rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.

CoInductive paco10_2_0( r_0 r_1: rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Prop :=
| paco10_2_0_pfold pco_0 pco_1
    (LE : pco_0 <10= (paco10_2_0 r_0 r_1 \10/ r_0))
    (LE : pco_1 <10= (paco10_2_1 r_0 r_1 \10/ r_1))
    (SIM: gf_0 pco_0 pco_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)
with paco10_2_1( r_0 r_1: rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Prop :=
| paco10_2_1_pfold pco_0 pco_1
    (LE : pco_0 <10= (paco10_2_0 r_0 r_1 \10/ r_0))
    (LE : pco_1 <10= (paco10_2_1 r_0 r_1 \10/ r_1))
    (SIM: gf_1 pco_0 pco_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)
.
Definition upaco10_2_0( r_0 r_1: rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) := paco10_2_0 r_0 r_1 \10/ r_0.
Definition upaco10_2_1( r_0 r_1: rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) := paco10_2_1 r_0 r_1 \10/ r_1.
End Arg10_2_def.
Arguments paco10_2_0 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 ].
Arguments upaco10_2_0 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 ].
Hint Unfold upaco10_2_0.
Arguments paco10_2_1 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 ].
Arguments upaco10_2_1 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 ].
Hint Unfold upaco10_2_1.

Section Arg10_3_def.
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
Variable gf_0 gf_1 gf_2 : rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.
Arguments gf_2 : clear implicits.

CoInductive paco10_3_0( r_0 r_1 r_2: rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Prop :=
| paco10_3_0_pfold pco_0 pco_1 pco_2
    (LE : pco_0 <10= (paco10_3_0 r_0 r_1 r_2 \10/ r_0))
    (LE : pco_1 <10= (paco10_3_1 r_0 r_1 r_2 \10/ r_1))
    (LE : pco_2 <10= (paco10_3_2 r_0 r_1 r_2 \10/ r_2))
    (SIM: gf_0 pco_0 pco_1 pco_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)
with paco10_3_1( r_0 r_1 r_2: rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Prop :=
| paco10_3_1_pfold pco_0 pco_1 pco_2
    (LE : pco_0 <10= (paco10_3_0 r_0 r_1 r_2 \10/ r_0))
    (LE : pco_1 <10= (paco10_3_1 r_0 r_1 r_2 \10/ r_1))
    (LE : pco_2 <10= (paco10_3_2 r_0 r_1 r_2 \10/ r_2))
    (SIM: gf_1 pco_0 pco_1 pco_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)
with paco10_3_2( r_0 r_1 r_2: rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Prop :=
| paco10_3_2_pfold pco_0 pco_1 pco_2
    (LE : pco_0 <10= (paco10_3_0 r_0 r_1 r_2 \10/ r_0))
    (LE : pco_1 <10= (paco10_3_1 r_0 r_1 r_2 \10/ r_1))
    (LE : pco_2 <10= (paco10_3_2 r_0 r_1 r_2 \10/ r_2))
    (SIM: gf_2 pco_0 pco_1 pco_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)
.
Definition upaco10_3_0( r_0 r_1 r_2: rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) := paco10_3_0 r_0 r_1 r_2 \10/ r_0.
Definition upaco10_3_1( r_0 r_1 r_2: rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) := paco10_3_1 r_0 r_1 r_2 \10/ r_1.
Definition upaco10_3_2( r_0 r_1 r_2: rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) := paco10_3_2 r_0 r_1 r_2 \10/ r_2.
End Arg10_3_def.
Arguments paco10_3_0 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 ].
Arguments upaco10_3_0 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 ].
Hint Unfold upaco10_3_0.
Arguments paco10_3_1 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 ].
Arguments upaco10_3_1 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 ].
Hint Unfold upaco10_3_1.
Arguments paco10_3_2 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 ].
Arguments upaco10_3_2 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 ].
Hint Unfold upaco10_3_2.

(* Less than or equal - internal use only *)
Notation "p <_paco_10= q" :=
  (forall _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 _paco_x5 _paco_x6 _paco_x7 _paco_x8 _paco_x9 (PR: p _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 _paco_x5 _paco_x6 _paco_x7 _paco_x8 _paco_x9 : Prop), q _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 _paco_x5 _paco_x6 _paco_x7 _paco_x8 _paco_x9 : Prop)
  (at level 50, no associativity).

(** 1 Mutual Coinduction *)

Section Arg10_1.

Definition monotone10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 (gf: rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) :=
  forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 r r' (IN: gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (LE: r <10= r'), gf r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9.

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
Variable gf : rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9.
Arguments gf : clear implicits.

Theorem paco10_acc: forall
  l r (OBG: forall rr (INC: r <10= rr) (CIH: l <_paco_10= rr), l <_paco_10= paco10 gf rr),
  l <10= paco10 gf r.
Proof.
  intros; assert (SIM: paco10 gf (r \10/ l) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) by eauto.
  clear PR; repeat (try left; do 11 paco_revert; paco_cofix_auto).
Qed.

Theorem paco10_mon: monotone10 (paco10 gf).
Proof. paco_cofix_auto; repeat (left; do 11 paco_revert; paco_cofix_auto). Qed.

Theorem paco10_mult_strong: forall r,
  paco10 gf (upaco10 gf r) <10= paco10 gf r.
Proof. paco_cofix_auto; repeat (left; do 11 paco_revert; paco_cofix_auto). Qed.

Corollary paco10_mult: forall r,
  paco10 gf (paco10 gf r) <10= paco10 gf r.
Proof. intros; eapply paco10_mult_strong, paco10_mon; eauto. Qed.

Theorem paco10_fold: forall r,
  gf (upaco10 gf r) <10= paco10 gf r.
Proof. intros; econstructor; [ |eauto]; eauto. Qed.

Theorem paco10_unfold: forall (MON: monotone10 gf) r,
  paco10 gf r <10= gf (upaco10 gf r).
Proof. unfold monotone10; intros; destruct PR; eauto. Qed.

End Arg10_1.

Hint Unfold monotone10.
Hint Resolve paco10_fold.

Arguments paco10_acc            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 ].
Arguments paco10_mon            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 ].
Arguments paco10_mult_strong    [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 ].
Arguments paco10_mult           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 ].
Arguments paco10_fold           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 ].
Arguments paco10_unfold         [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 ].

Instance paco10_inst  T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 (gf : rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9->_) r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : paco_class (paco10 gf r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) :=
{ pacoacc    := paco10_acc gf;
  pacomult   := paco10_mult gf;
  pacofold   := paco10_fold gf;
  pacounfold := paco10_unfold gf }.

(** 2 Mutual Coinduction *)

Section Arg10_2.

Definition monotone10_2 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 (gf: rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) :=
  forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 r_0 r_1 r'_0 r'_1 (IN: gf r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (LE_0: r_0 <10= r'_0)(LE_1: r_1 <10= r'_1), gf r'_0 r'_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9.

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
Variable gf_0 gf_1 : rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.

Theorem paco10_2_0_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_0 <10= rr) (CIH: l <_paco_10= rr), l <_paco_10= paco10_2_0 gf_0 gf_1 rr r_1),
  l <10= paco10_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  intros; assert (SIM: paco10_2_0 gf_0 gf_1 (r_0 \10/ l) r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) by eauto.
  clear PR; repeat (try left; do 11 paco_revert; paco_cofix_auto).
Qed.

Theorem paco10_2_1_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_1 <10= rr) (CIH: l <_paco_10= rr), l <_paco_10= paco10_2_1 gf_0 gf_1 r_0 rr),
  l <10= paco10_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  intros; assert (SIM: paco10_2_1 gf_0 gf_1 r_0 (r_1 \10/ l) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) by eauto.
  clear PR; repeat (try left; do 11 paco_revert; paco_cofix_auto).
Qed.

Theorem paco10_2_0_mon: monotone10_2 (paco10_2_0 gf_0 gf_1).
Proof. paco_cofix_auto; repeat (left; do 11 paco_revert; paco_cofix_auto). Qed.

Theorem paco10_2_1_mon: monotone10_2 (paco10_2_1 gf_0 gf_1).
Proof. paco_cofix_auto; repeat (left; do 11 paco_revert; paco_cofix_auto). Qed.

Theorem paco10_2_0_mult_strong: forall r_0 r_1,
  paco10_2_0 gf_0 gf_1 (upaco10_2_0 gf_0 gf_1 r_0 r_1) (upaco10_2_1 gf_0 gf_1 r_0 r_1) <10= paco10_2_0 gf_0 gf_1 r_0 r_1.
Proof. paco_cofix_auto; repeat (left; do 11 paco_revert; paco_cofix_auto). Qed.

Theorem paco10_2_1_mult_strong: forall r_0 r_1,
  paco10_2_1 gf_0 gf_1 (upaco10_2_0 gf_0 gf_1 r_0 r_1) (upaco10_2_1 gf_0 gf_1 r_0 r_1) <10= paco10_2_1 gf_0 gf_1 r_0 r_1.
Proof. paco_cofix_auto; repeat (left; do 11 paco_revert; paco_cofix_auto). Qed.

Corollary paco10_2_0_mult: forall r_0 r_1,
  paco10_2_0 gf_0 gf_1 (paco10_2_0 gf_0 gf_1 r_0 r_1) (paco10_2_1 gf_0 gf_1 r_0 r_1) <10= paco10_2_0 gf_0 gf_1 r_0 r_1.
Proof. intros; eapply paco10_2_0_mult_strong, paco10_2_0_mon; eauto. Qed.

Corollary paco10_2_1_mult: forall r_0 r_1,
  paco10_2_1 gf_0 gf_1 (paco10_2_0 gf_0 gf_1 r_0 r_1) (paco10_2_1 gf_0 gf_1 r_0 r_1) <10= paco10_2_1 gf_0 gf_1 r_0 r_1.
Proof. intros; eapply paco10_2_1_mult_strong, paco10_2_1_mon; eauto. Qed.

Theorem paco10_2_0_fold: forall r_0 r_1,
  gf_0 (upaco10_2_0 gf_0 gf_1 r_0 r_1) (upaco10_2_1 gf_0 gf_1 r_0 r_1) <10= paco10_2_0 gf_0 gf_1 r_0 r_1.
Proof. intros; econstructor; [ | |eauto]; eauto. Qed.

Theorem paco10_2_1_fold: forall r_0 r_1,
  gf_1 (upaco10_2_0 gf_0 gf_1 r_0 r_1) (upaco10_2_1 gf_0 gf_1 r_0 r_1) <10= paco10_2_1 gf_0 gf_1 r_0 r_1.
Proof. intros; econstructor; [ | |eauto]; eauto. Qed.

Theorem paco10_2_0_unfold: forall (MON: monotone10_2 gf_0) (MON: monotone10_2 gf_1) r_0 r_1,
  paco10_2_0 gf_0 gf_1 r_0 r_1 <10= gf_0 (upaco10_2_0 gf_0 gf_1 r_0 r_1) (upaco10_2_1 gf_0 gf_1 r_0 r_1).
Proof. unfold monotone10_2; intros; destruct PR; eauto. Qed.

Theorem paco10_2_1_unfold: forall (MON: monotone10_2 gf_0) (MON: monotone10_2 gf_1) r_0 r_1,
  paco10_2_1 gf_0 gf_1 r_0 r_1 <10= gf_1 (upaco10_2_0 gf_0 gf_1 r_0 r_1) (upaco10_2_1 gf_0 gf_1 r_0 r_1).
Proof. unfold monotone10_2; intros; destruct PR; eauto. Qed.

End Arg10_2.

Hint Unfold monotone10_2.
Hint Resolve paco10_2_0_fold.
Hint Resolve paco10_2_1_fold.

Arguments paco10_2_0_acc            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 ].
Arguments paco10_2_1_acc            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 ].
Arguments paco10_2_0_mon            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 ].
Arguments paco10_2_1_mon            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 ].
Arguments paco10_2_0_mult_strong    [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 ].
Arguments paco10_2_1_mult_strong    [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 ].
Arguments paco10_2_0_mult           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 ].
Arguments paco10_2_1_mult           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 ].
Arguments paco10_2_0_fold           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 ].
Arguments paco10_2_1_fold           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 ].
Arguments paco10_2_0_unfold         [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 ].
Arguments paco10_2_1_unfold         [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 ].

Instance paco10_2_0_inst  T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 (gf_0 gf_1 : rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9->_) r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : paco_class (paco10_2_0 gf_0 gf_1 r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) :=
{ pacoacc    := paco10_2_0_acc gf_0 gf_1;
  pacomult   := paco10_2_0_mult gf_0 gf_1;
  pacofold   := paco10_2_0_fold gf_0 gf_1;
  pacounfold := paco10_2_0_unfold gf_0 gf_1 }.

Instance paco10_2_1_inst  T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 (gf_0 gf_1 : rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9->_) r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : paco_class (paco10_2_1 gf_0 gf_1 r_0 r_1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) :=
{ pacoacc    := paco10_2_1_acc gf_0 gf_1;
  pacomult   := paco10_2_1_mult gf_0 gf_1;
  pacofold   := paco10_2_1_fold gf_0 gf_1;
  pacounfold := paco10_2_1_unfold gf_0 gf_1 }.

(** 3 Mutual Coinduction *)

Section Arg10_3.

Definition monotone10_3 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 (gf: rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) :=
  forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 r_0 r_1 r_2 r'_0 r'_1 r'_2 (IN: gf r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (LE_0: r_0 <10= r'_0)(LE_1: r_1 <10= r'_1)(LE_2: r_2 <10= r'_2), gf r'_0 r'_1 r'_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9.

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
Variable gf_0 gf_1 gf_2 : rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 -> rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.
Arguments gf_2 : clear implicits.

Theorem paco10_3_0_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_0 <10= rr) (CIH: l <_paco_10= rr), l <_paco_10= paco10_3_0 gf_0 gf_1 gf_2 rr r_1 r_2),
  l <10= paco10_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros; assert (SIM: paco10_3_0 gf_0 gf_1 gf_2 (r_0 \10/ l) r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) by eauto.
  clear PR; repeat (try left; do 11 paco_revert; paco_cofix_auto).
Qed.

Theorem paco10_3_1_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_1 <10= rr) (CIH: l <_paco_10= rr), l <_paco_10= paco10_3_1 gf_0 gf_1 gf_2 r_0 rr r_2),
  l <10= paco10_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros; assert (SIM: paco10_3_1 gf_0 gf_1 gf_2 r_0 (r_1 \10/ l) r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) by eauto.
  clear PR; repeat (try left; do 11 paco_revert; paco_cofix_auto).
Qed.

Theorem paco10_3_2_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_2 <10= rr) (CIH: l <_paco_10= rr), l <_paco_10= paco10_3_2 gf_0 gf_1 gf_2 r_0 r_1 rr),
  l <10= paco10_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros; assert (SIM: paco10_3_2 gf_0 gf_1 gf_2 r_0 r_1 (r_2 \10/ l) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) by eauto.
  clear PR; repeat (try left; do 11 paco_revert; paco_cofix_auto).
Qed.

Theorem paco10_3_0_mon: monotone10_3 (paco10_3_0 gf_0 gf_1 gf_2).
Proof. paco_cofix_auto; repeat (left; do 11 paco_revert; paco_cofix_auto). Qed.

Theorem paco10_3_1_mon: monotone10_3 (paco10_3_1 gf_0 gf_1 gf_2).
Proof. paco_cofix_auto; repeat (left; do 11 paco_revert; paco_cofix_auto). Qed.

Theorem paco10_3_2_mon: monotone10_3 (paco10_3_2 gf_0 gf_1 gf_2).
Proof. paco_cofix_auto; repeat (left; do 11 paco_revert; paco_cofix_auto). Qed.

Theorem paco10_3_0_mult_strong: forall r_0 r_1 r_2,
  paco10_3_0 gf_0 gf_1 gf_2 (upaco10_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco10_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco10_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <10= paco10_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. paco_cofix_auto; repeat (left; do 11 paco_revert; paco_cofix_auto). Qed.

Theorem paco10_3_1_mult_strong: forall r_0 r_1 r_2,
  paco10_3_1 gf_0 gf_1 gf_2 (upaco10_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco10_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco10_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <10= paco10_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. paco_cofix_auto; repeat (left; do 11 paco_revert; paco_cofix_auto). Qed.

Theorem paco10_3_2_mult_strong: forall r_0 r_1 r_2,
  paco10_3_2 gf_0 gf_1 gf_2 (upaco10_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco10_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco10_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <10= paco10_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. paco_cofix_auto; repeat (left; do 11 paco_revert; paco_cofix_auto). Qed.

Corollary paco10_3_0_mult: forall r_0 r_1 r_2,
  paco10_3_0 gf_0 gf_1 gf_2 (paco10_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco10_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco10_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <10= paco10_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco10_3_0_mult_strong, paco10_3_0_mon; eauto. Qed.

Corollary paco10_3_1_mult: forall r_0 r_1 r_2,
  paco10_3_1 gf_0 gf_1 gf_2 (paco10_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco10_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco10_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <10= paco10_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco10_3_1_mult_strong, paco10_3_1_mon; eauto. Qed.

Corollary paco10_3_2_mult: forall r_0 r_1 r_2,
  paco10_3_2 gf_0 gf_1 gf_2 (paco10_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco10_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco10_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <10= paco10_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco10_3_2_mult_strong, paco10_3_2_mon; eauto. Qed.

Theorem paco10_3_0_fold: forall r_0 r_1 r_2,
  gf_0 (upaco10_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco10_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco10_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <10= paco10_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; econstructor; [ | | |eauto]; eauto. Qed.

Theorem paco10_3_1_fold: forall r_0 r_1 r_2,
  gf_1 (upaco10_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco10_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco10_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <10= paco10_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; econstructor; [ | | |eauto]; eauto. Qed.

Theorem paco10_3_2_fold: forall r_0 r_1 r_2,
  gf_2 (upaco10_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco10_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco10_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <10= paco10_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; econstructor; [ | | |eauto]; eauto. Qed.

Theorem paco10_3_0_unfold: forall (MON: monotone10_3 gf_0) (MON: monotone10_3 gf_1) (MON: monotone10_3 gf_2) r_0 r_1 r_2,
  paco10_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 <10= gf_0 (upaco10_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco10_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco10_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof. unfold monotone10_3; intros; destruct PR; eauto. Qed.

Theorem paco10_3_1_unfold: forall (MON: monotone10_3 gf_0) (MON: monotone10_3 gf_1) (MON: monotone10_3 gf_2) r_0 r_1 r_2,
  paco10_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 <10= gf_1 (upaco10_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco10_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco10_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof. unfold monotone10_3; intros; destruct PR; eauto. Qed.

Theorem paco10_3_2_unfold: forall (MON: monotone10_3 gf_0) (MON: monotone10_3 gf_1) (MON: monotone10_3 gf_2) r_0 r_1 r_2,
  paco10_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 <10= gf_2 (upaco10_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco10_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco10_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof. unfold monotone10_3; intros; destruct PR; eauto. Qed.

End Arg10_3.

Hint Unfold monotone10_3.
Hint Resolve paco10_3_0_fold.
Hint Resolve paco10_3_1_fold.
Hint Resolve paco10_3_2_fold.

Arguments paco10_3_0_acc            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 ].
Arguments paco10_3_1_acc            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 ].
Arguments paco10_3_2_acc            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 ].
Arguments paco10_3_0_mon            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 ].
Arguments paco10_3_1_mon            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 ].
Arguments paco10_3_2_mon            [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 ].
Arguments paco10_3_0_mult_strong    [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 ].
Arguments paco10_3_1_mult_strong    [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 ].
Arguments paco10_3_2_mult_strong    [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 ].
Arguments paco10_3_0_mult           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 ].
Arguments paco10_3_1_mult           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 ].
Arguments paco10_3_2_mult           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 ].
Arguments paco10_3_0_fold           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 ].
Arguments paco10_3_1_fold           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 ].
Arguments paco10_3_2_fold           [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 ].
Arguments paco10_3_0_unfold         [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 ].
Arguments paco10_3_1_unfold         [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 ].
Arguments paco10_3_2_unfold         [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 ].

Instance paco10_3_0_inst  T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 (gf_0 gf_1 gf_2 : rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : paco_class (paco10_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) :=
{ pacoacc    := paco10_3_0_acc gf_0 gf_1 gf_2;
  pacomult   := paco10_3_0_mult gf_0 gf_1 gf_2;
  pacofold   := paco10_3_0_fold gf_0 gf_1 gf_2;
  pacounfold := paco10_3_0_unfold gf_0 gf_1 gf_2 }.

Instance paco10_3_1_inst  T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 (gf_0 gf_1 gf_2 : rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : paco_class (paco10_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) :=
{ pacoacc    := paco10_3_1_acc gf_0 gf_1 gf_2;
  pacomult   := paco10_3_1_mult gf_0 gf_1 gf_2;
  pacofold   := paco10_3_1_fold gf_0 gf_1 gf_2;
  pacounfold := paco10_3_1_unfold gf_0 gf_1 gf_2 }.

Instance paco10_3_2_inst  T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 (gf_0 gf_1 gf_2 : rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : paco_class (paco10_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) :=
{ pacoacc    := paco10_3_2_acc gf_0 gf_1 gf_2;
  pacomult   := paco10_3_2_mult gf_0 gf_1 gf_2;
  pacofold   := paco10_3_2_fold gf_0 gf_1 gf_2;
  pacounfold := paco10_3_2_unfold gf_0 gf_1 gf_2 }.

