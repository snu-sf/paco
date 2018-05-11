Require Export paconotation pacotacuser.
Require Import pacotac.
Set Implicit Arguments.

(** ** Predicates of Arity 6
*)

Section Arg6_def.
Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable gf : rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5.
Arguments gf : clear implicits.

CoInductive paco6( r: rel6 T0 T1 T2 T3 T4 T5) x0 x1 x2 x3 x4 x5 : Prop :=
| paco6_pfold pco
    (LE : pco <6= (paco6 r \6/ r))
    (SIM: gf pco x0 x1 x2 x3 x4 x5)
.
Definition upaco6( r: rel6 T0 T1 T2 T3 T4 T5) := paco6 r \6/ r.
End Arg6_def.
Arguments paco6 [ T0 T1 T2 T3 T4 T5 ].
Arguments upaco6 [ T0 T1 T2 T3 T4 T5 ].
Hint Unfold upaco6.

Section Arg6_2_def.
Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable gf_0 gf_1 : rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.

CoInductive paco6_2_0( r_0 r_1: rel6 T0 T1 T2 T3 T4 T5) x0 x1 x2 x3 x4 x5 : Prop :=
| paco6_2_0_pfold pco_0 pco_1
    (LE : pco_0 <6= (paco6_2_0 r_0 r_1 \6/ r_0))
    (LE : pco_1 <6= (paco6_2_1 r_0 r_1 \6/ r_1))
    (SIM: gf_0 pco_0 pco_1 x0 x1 x2 x3 x4 x5)
with paco6_2_1( r_0 r_1: rel6 T0 T1 T2 T3 T4 T5) x0 x1 x2 x3 x4 x5 : Prop :=
| paco6_2_1_pfold pco_0 pco_1
    (LE : pco_0 <6= (paco6_2_0 r_0 r_1 \6/ r_0))
    (LE : pco_1 <6= (paco6_2_1 r_0 r_1 \6/ r_1))
    (SIM: gf_1 pco_0 pco_1 x0 x1 x2 x3 x4 x5)
.
Definition upaco6_2_0( r_0 r_1: rel6 T0 T1 T2 T3 T4 T5) := paco6_2_0 r_0 r_1 \6/ r_0.
Definition upaco6_2_1( r_0 r_1: rel6 T0 T1 T2 T3 T4 T5) := paco6_2_1 r_0 r_1 \6/ r_1.
End Arg6_2_def.
Arguments paco6_2_0 [ T0 T1 T2 T3 T4 T5 ].
Arguments upaco6_2_0 [ T0 T1 T2 T3 T4 T5 ].
Hint Unfold upaco6_2_0.
Arguments paco6_2_1 [ T0 T1 T2 T3 T4 T5 ].
Arguments upaco6_2_1 [ T0 T1 T2 T3 T4 T5 ].
Hint Unfold upaco6_2_1.

Section Arg6_3_def.
Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable gf_0 gf_1 gf_2 : rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.
Arguments gf_2 : clear implicits.

CoInductive paco6_3_0( r_0 r_1 r_2: rel6 T0 T1 T2 T3 T4 T5) x0 x1 x2 x3 x4 x5 : Prop :=
| paco6_3_0_pfold pco_0 pco_1 pco_2
    (LE : pco_0 <6= (paco6_3_0 r_0 r_1 r_2 \6/ r_0))
    (LE : pco_1 <6= (paco6_3_1 r_0 r_1 r_2 \6/ r_1))
    (LE : pco_2 <6= (paco6_3_2 r_0 r_1 r_2 \6/ r_2))
    (SIM: gf_0 pco_0 pco_1 pco_2 x0 x1 x2 x3 x4 x5)
with paco6_3_1( r_0 r_1 r_2: rel6 T0 T1 T2 T3 T4 T5) x0 x1 x2 x3 x4 x5 : Prop :=
| paco6_3_1_pfold pco_0 pco_1 pco_2
    (LE : pco_0 <6= (paco6_3_0 r_0 r_1 r_2 \6/ r_0))
    (LE : pco_1 <6= (paco6_3_1 r_0 r_1 r_2 \6/ r_1))
    (LE : pco_2 <6= (paco6_3_2 r_0 r_1 r_2 \6/ r_2))
    (SIM: gf_1 pco_0 pco_1 pco_2 x0 x1 x2 x3 x4 x5)
with paco6_3_2( r_0 r_1 r_2: rel6 T0 T1 T2 T3 T4 T5) x0 x1 x2 x3 x4 x5 : Prop :=
| paco6_3_2_pfold pco_0 pco_1 pco_2
    (LE : pco_0 <6= (paco6_3_0 r_0 r_1 r_2 \6/ r_0))
    (LE : pco_1 <6= (paco6_3_1 r_0 r_1 r_2 \6/ r_1))
    (LE : pco_2 <6= (paco6_3_2 r_0 r_1 r_2 \6/ r_2))
    (SIM: gf_2 pco_0 pco_1 pco_2 x0 x1 x2 x3 x4 x5)
.
Definition upaco6_3_0( r_0 r_1 r_2: rel6 T0 T1 T2 T3 T4 T5) := paco6_3_0 r_0 r_1 r_2 \6/ r_0.
Definition upaco6_3_1( r_0 r_1 r_2: rel6 T0 T1 T2 T3 T4 T5) := paco6_3_1 r_0 r_1 r_2 \6/ r_1.
Definition upaco6_3_2( r_0 r_1 r_2: rel6 T0 T1 T2 T3 T4 T5) := paco6_3_2 r_0 r_1 r_2 \6/ r_2.
End Arg6_3_def.
Arguments paco6_3_0 [ T0 T1 T2 T3 T4 T5 ].
Arguments upaco6_3_0 [ T0 T1 T2 T3 T4 T5 ].
Hint Unfold upaco6_3_0.
Arguments paco6_3_1 [ T0 T1 T2 T3 T4 T5 ].
Arguments upaco6_3_1 [ T0 T1 T2 T3 T4 T5 ].
Hint Unfold upaco6_3_1.
Arguments paco6_3_2 [ T0 T1 T2 T3 T4 T5 ].
Arguments upaco6_3_2 [ T0 T1 T2 T3 T4 T5 ].
Hint Unfold upaco6_3_2.

(* Less than or equal - internal use only *)
Notation "p <_paco_6= q" :=
  (forall _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 _paco_x5 (PR: p _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 _paco_x5 : Prop), q _paco_x0 _paco_x1 _paco_x2 _paco_x3 _paco_x4 _paco_x5 : Prop)
  (at level 50, no associativity).

(** 1 Mutual Coinduction *)

Section Arg6_1.

Definition monotone6 T0 T1 T2 T3 T4 T5 (gf: rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5) :=
  forall x0 x1 x2 x3 x4 x5 r r' (IN: gf r x0 x1 x2 x3 x4 x5) (LE: r <6= r'), gf r' x0 x1 x2 x3 x4 x5.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable gf : rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5.
Arguments gf : clear implicits.

Theorem paco6_acc: forall
  l r (OBG: forall rr (INC: r <6= rr) (CIH: l <_paco_6= rr), l <_paco_6= paco6 gf rr),
  l <6= paco6 gf r.
Proof.
  intros; assert (SIM: paco6 gf (r \6/ l) x0 x1 x2 x3 x4 x5) by eauto.
  clear PR; repeat (try left; do 7 paco_revert; paco_cofix_auto).
Qed.

Theorem paco6_mon: monotone6 (paco6 gf).
Proof. paco_cofix_auto; repeat (left; do 7 paco_revert; paco_cofix_auto). Qed.

Theorem paco6_mult_strong: forall r,
  paco6 gf (upaco6 gf r) <6= paco6 gf r.
Proof. paco_cofix_auto; repeat (left; do 7 paco_revert; paco_cofix_auto). Qed.

Corollary paco6_mult: forall r,
  paco6 gf (paco6 gf r) <6= paco6 gf r.
Proof. intros; eapply paco6_mult_strong, paco6_mon; eauto. Qed.

Theorem paco6_fold: forall r,
  gf (upaco6 gf r) <6= paco6 gf r.
Proof. intros; econstructor; [ |eauto]; eauto. Qed.

Theorem paco6_unfold: forall (MON: monotone6 gf) r,
  paco6 gf r <6= gf (upaco6 gf r).
Proof. unfold monotone6; intros; destruct PR; eauto. Qed.

End Arg6_1.

Hint Unfold monotone6.
Hint Resolve paco6_fold.

Arguments paco6_acc            [ T0 T1 T2 T3 T4 T5 ].
Arguments paco6_mon            [ T0 T1 T2 T3 T4 T5 ].
Arguments paco6_mult_strong    [ T0 T1 T2 T3 T4 T5 ].
Arguments paco6_mult           [ T0 T1 T2 T3 T4 T5 ].
Arguments paco6_fold           [ T0 T1 T2 T3 T4 T5 ].
Arguments paco6_unfold         [ T0 T1 T2 T3 T4 T5 ].

Instance paco6_inst  T0 T1 T2 T3 T4 T5 (gf : rel6 T0 T1 T2 T3 T4 T5->_) r x0 x1 x2 x3 x4 x5 : paco_class (paco6 gf r x0 x1 x2 x3 x4 x5) :=
{ pacoacc    := paco6_acc gf;
  pacomult   := paco6_mult gf;
  pacofold   := paco6_fold gf;
  pacounfold := paco6_unfold gf }.

(** 2 Mutual Coinduction *)

Section Arg6_2.

Definition monotone6_2 T0 T1 T2 T3 T4 T5 (gf: rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5) :=
  forall x0 x1 x2 x3 x4 x5 r_0 r_1 r'_0 r'_1 (IN: gf r_0 r_1 x0 x1 x2 x3 x4 x5) (LE_0: r_0 <6= r'_0)(LE_1: r_1 <6= r'_1), gf r'_0 r'_1 x0 x1 x2 x3 x4 x5.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable gf_0 gf_1 : rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.

Theorem paco6_2_0_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_0 <6= rr) (CIH: l <_paco_6= rr), l <_paco_6= paco6_2_0 gf_0 gf_1 rr r_1),
  l <6= paco6_2_0 gf_0 gf_1 r_0 r_1.
Proof.
  intros; assert (SIM: paco6_2_0 gf_0 gf_1 (r_0 \6/ l) r_1 x0 x1 x2 x3 x4 x5) by eauto.
  clear PR; repeat (try left; do 7 paco_revert; paco_cofix_auto).
Qed.

Theorem paco6_2_1_acc: forall
  l r_0 r_1 (OBG: forall rr (INC: r_1 <6= rr) (CIH: l <_paco_6= rr), l <_paco_6= paco6_2_1 gf_0 gf_1 r_0 rr),
  l <6= paco6_2_1 gf_0 gf_1 r_0 r_1.
Proof.
  intros; assert (SIM: paco6_2_1 gf_0 gf_1 r_0 (r_1 \6/ l) x0 x1 x2 x3 x4 x5) by eauto.
  clear PR; repeat (try left; do 7 paco_revert; paco_cofix_auto).
Qed.

Theorem paco6_2_0_mon: monotone6_2 (paco6_2_0 gf_0 gf_1).
Proof. paco_cofix_auto; repeat (left; do 7 paco_revert; paco_cofix_auto). Qed.

Theorem paco6_2_1_mon: monotone6_2 (paco6_2_1 gf_0 gf_1).
Proof. paco_cofix_auto; repeat (left; do 7 paco_revert; paco_cofix_auto). Qed.

Theorem paco6_2_0_mult_strong: forall r_0 r_1,
  paco6_2_0 gf_0 gf_1 (upaco6_2_0 gf_0 gf_1 r_0 r_1) (upaco6_2_1 gf_0 gf_1 r_0 r_1) <6= paco6_2_0 gf_0 gf_1 r_0 r_1.
Proof. paco_cofix_auto; repeat (left; do 7 paco_revert; paco_cofix_auto). Qed.

Theorem paco6_2_1_mult_strong: forall r_0 r_1,
  paco6_2_1 gf_0 gf_1 (upaco6_2_0 gf_0 gf_1 r_0 r_1) (upaco6_2_1 gf_0 gf_1 r_0 r_1) <6= paco6_2_1 gf_0 gf_1 r_0 r_1.
Proof. paco_cofix_auto; repeat (left; do 7 paco_revert; paco_cofix_auto). Qed.

Corollary paco6_2_0_mult: forall r_0 r_1,
  paco6_2_0 gf_0 gf_1 (paco6_2_0 gf_0 gf_1 r_0 r_1) (paco6_2_1 gf_0 gf_1 r_0 r_1) <6= paco6_2_0 gf_0 gf_1 r_0 r_1.
Proof. intros; eapply paco6_2_0_mult_strong, paco6_2_0_mon; eauto. Qed.

Corollary paco6_2_1_mult: forall r_0 r_1,
  paco6_2_1 gf_0 gf_1 (paco6_2_0 gf_0 gf_1 r_0 r_1) (paco6_2_1 gf_0 gf_1 r_0 r_1) <6= paco6_2_1 gf_0 gf_1 r_0 r_1.
Proof. intros; eapply paco6_2_1_mult_strong, paco6_2_1_mon; eauto. Qed.

Theorem paco6_2_0_fold: forall r_0 r_1,
  gf_0 (upaco6_2_0 gf_0 gf_1 r_0 r_1) (upaco6_2_1 gf_0 gf_1 r_0 r_1) <6= paco6_2_0 gf_0 gf_1 r_0 r_1.
Proof. intros; econstructor; [ | |eauto]; eauto. Qed.

Theorem paco6_2_1_fold: forall r_0 r_1,
  gf_1 (upaco6_2_0 gf_0 gf_1 r_0 r_1) (upaco6_2_1 gf_0 gf_1 r_0 r_1) <6= paco6_2_1 gf_0 gf_1 r_0 r_1.
Proof. intros; econstructor; [ | |eauto]; eauto. Qed.

Theorem paco6_2_0_unfold: forall (MON: monotone6_2 gf_0) (MON: monotone6_2 gf_1) r_0 r_1,
  paco6_2_0 gf_0 gf_1 r_0 r_1 <6= gf_0 (upaco6_2_0 gf_0 gf_1 r_0 r_1) (upaco6_2_1 gf_0 gf_1 r_0 r_1).
Proof. unfold monotone6_2; intros; destruct PR; eauto. Qed.

Theorem paco6_2_1_unfold: forall (MON: monotone6_2 gf_0) (MON: monotone6_2 gf_1) r_0 r_1,
  paco6_2_1 gf_0 gf_1 r_0 r_1 <6= gf_1 (upaco6_2_0 gf_0 gf_1 r_0 r_1) (upaco6_2_1 gf_0 gf_1 r_0 r_1).
Proof. unfold monotone6_2; intros; destruct PR; eauto. Qed.

End Arg6_2.

Hint Unfold monotone6_2.
Hint Resolve paco6_2_0_fold.
Hint Resolve paco6_2_1_fold.

Arguments paco6_2_0_acc            [ T0 T1 T2 T3 T4 T5 ].
Arguments paco6_2_1_acc            [ T0 T1 T2 T3 T4 T5 ].
Arguments paco6_2_0_mon            [ T0 T1 T2 T3 T4 T5 ].
Arguments paco6_2_1_mon            [ T0 T1 T2 T3 T4 T5 ].
Arguments paco6_2_0_mult_strong    [ T0 T1 T2 T3 T4 T5 ].
Arguments paco6_2_1_mult_strong    [ T0 T1 T2 T3 T4 T5 ].
Arguments paco6_2_0_mult           [ T0 T1 T2 T3 T4 T5 ].
Arguments paco6_2_1_mult           [ T0 T1 T2 T3 T4 T5 ].
Arguments paco6_2_0_fold           [ T0 T1 T2 T3 T4 T5 ].
Arguments paco6_2_1_fold           [ T0 T1 T2 T3 T4 T5 ].
Arguments paco6_2_0_unfold         [ T0 T1 T2 T3 T4 T5 ].
Arguments paco6_2_1_unfold         [ T0 T1 T2 T3 T4 T5 ].

Instance paco6_2_0_inst  T0 T1 T2 T3 T4 T5 (gf_0 gf_1 : rel6 T0 T1 T2 T3 T4 T5->_) r_0 r_1 x0 x1 x2 x3 x4 x5 : paco_class (paco6_2_0 gf_0 gf_1 r_0 r_1 x0 x1 x2 x3 x4 x5) :=
{ pacoacc    := paco6_2_0_acc gf_0 gf_1;
  pacomult   := paco6_2_0_mult gf_0 gf_1;
  pacofold   := paco6_2_0_fold gf_0 gf_1;
  pacounfold := paco6_2_0_unfold gf_0 gf_1 }.

Instance paco6_2_1_inst  T0 T1 T2 T3 T4 T5 (gf_0 gf_1 : rel6 T0 T1 T2 T3 T4 T5->_) r_0 r_1 x0 x1 x2 x3 x4 x5 : paco_class (paco6_2_1 gf_0 gf_1 r_0 r_1 x0 x1 x2 x3 x4 x5) :=
{ pacoacc    := paco6_2_1_acc gf_0 gf_1;
  pacomult   := paco6_2_1_mult gf_0 gf_1;
  pacofold   := paco6_2_1_fold gf_0 gf_1;
  pacounfold := paco6_2_1_unfold gf_0 gf_1 }.

(** 3 Mutual Coinduction *)

Section Arg6_3.

Definition monotone6_3 T0 T1 T2 T3 T4 T5 (gf: rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5) :=
  forall x0 x1 x2 x3 x4 x5 r_0 r_1 r_2 r'_0 r'_1 r'_2 (IN: gf r_0 r_1 r_2 x0 x1 x2 x3 x4 x5) (LE_0: r_0 <6= r'_0)(LE_1: r_1 <6= r'_1)(LE_2: r_2 <6= r'_2), gf r'_0 r'_1 r'_2 x0 x1 x2 x3 x4 x5.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable gf_0 gf_1 gf_2 : rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5 -> rel6 T0 T1 T2 T3 T4 T5.
Arguments gf_0 : clear implicits.
Arguments gf_1 : clear implicits.
Arguments gf_2 : clear implicits.

Theorem paco6_3_0_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_0 <6= rr) (CIH: l <_paco_6= rr), l <_paco_6= paco6_3_0 gf_0 gf_1 gf_2 rr r_1 r_2),
  l <6= paco6_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros; assert (SIM: paco6_3_0 gf_0 gf_1 gf_2 (r_0 \6/ l) r_1 r_2 x0 x1 x2 x3 x4 x5) by eauto.
  clear PR; repeat (try left; do 7 paco_revert; paco_cofix_auto).
Qed.

Theorem paco6_3_1_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_1 <6= rr) (CIH: l <_paco_6= rr), l <_paco_6= paco6_3_1 gf_0 gf_1 gf_2 r_0 rr r_2),
  l <6= paco6_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros; assert (SIM: paco6_3_1 gf_0 gf_1 gf_2 r_0 (r_1 \6/ l) r_2 x0 x1 x2 x3 x4 x5) by eauto.
  clear PR; repeat (try left; do 7 paco_revert; paco_cofix_auto).
Qed.

Theorem paco6_3_2_acc: forall
  l r_0 r_1 r_2 (OBG: forall rr (INC: r_2 <6= rr) (CIH: l <_paco_6= rr), l <_paco_6= paco6_3_2 gf_0 gf_1 gf_2 r_0 r_1 rr),
  l <6= paco6_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof.
  intros; assert (SIM: paco6_3_2 gf_0 gf_1 gf_2 r_0 r_1 (r_2 \6/ l) x0 x1 x2 x3 x4 x5) by eauto.
  clear PR; repeat (try left; do 7 paco_revert; paco_cofix_auto).
Qed.

Theorem paco6_3_0_mon: monotone6_3 (paco6_3_0 gf_0 gf_1 gf_2).
Proof. paco_cofix_auto; repeat (left; do 7 paco_revert; paco_cofix_auto). Qed.

Theorem paco6_3_1_mon: monotone6_3 (paco6_3_1 gf_0 gf_1 gf_2).
Proof. paco_cofix_auto; repeat (left; do 7 paco_revert; paco_cofix_auto). Qed.

Theorem paco6_3_2_mon: monotone6_3 (paco6_3_2 gf_0 gf_1 gf_2).
Proof. paco_cofix_auto; repeat (left; do 7 paco_revert; paco_cofix_auto). Qed.

Theorem paco6_3_0_mult_strong: forall r_0 r_1 r_2,
  paco6_3_0 gf_0 gf_1 gf_2 (upaco6_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco6_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco6_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <6= paco6_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. paco_cofix_auto; repeat (left; do 7 paco_revert; paco_cofix_auto). Qed.

Theorem paco6_3_1_mult_strong: forall r_0 r_1 r_2,
  paco6_3_1 gf_0 gf_1 gf_2 (upaco6_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco6_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco6_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <6= paco6_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. paco_cofix_auto; repeat (left; do 7 paco_revert; paco_cofix_auto). Qed.

Theorem paco6_3_2_mult_strong: forall r_0 r_1 r_2,
  paco6_3_2 gf_0 gf_1 gf_2 (upaco6_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco6_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco6_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <6= paco6_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. paco_cofix_auto; repeat (left; do 7 paco_revert; paco_cofix_auto). Qed.

Corollary paco6_3_0_mult: forall r_0 r_1 r_2,
  paco6_3_0 gf_0 gf_1 gf_2 (paco6_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco6_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco6_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <6= paco6_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco6_3_0_mult_strong, paco6_3_0_mon; eauto. Qed.

Corollary paco6_3_1_mult: forall r_0 r_1 r_2,
  paco6_3_1 gf_0 gf_1 gf_2 (paco6_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco6_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco6_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <6= paco6_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco6_3_1_mult_strong, paco6_3_1_mon; eauto. Qed.

Corollary paco6_3_2_mult: forall r_0 r_1 r_2,
  paco6_3_2 gf_0 gf_1 gf_2 (paco6_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco6_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (paco6_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <6= paco6_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; eapply paco6_3_2_mult_strong, paco6_3_2_mon; eauto. Qed.

Theorem paco6_3_0_fold: forall r_0 r_1 r_2,
  gf_0 (upaco6_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco6_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco6_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <6= paco6_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; econstructor; [ | | |eauto]; eauto. Qed.

Theorem paco6_3_1_fold: forall r_0 r_1 r_2,
  gf_1 (upaco6_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco6_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco6_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <6= paco6_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; econstructor; [ | | |eauto]; eauto. Qed.

Theorem paco6_3_2_fold: forall r_0 r_1 r_2,
  gf_2 (upaco6_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco6_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco6_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2) <6= paco6_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2.
Proof. intros; econstructor; [ | | |eauto]; eauto. Qed.

Theorem paco6_3_0_unfold: forall (MON: monotone6_3 gf_0) (MON: monotone6_3 gf_1) (MON: monotone6_3 gf_2) r_0 r_1 r_2,
  paco6_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 <6= gf_0 (upaco6_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco6_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco6_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof. unfold monotone6_3; intros; destruct PR; eauto. Qed.

Theorem paco6_3_1_unfold: forall (MON: monotone6_3 gf_0) (MON: monotone6_3 gf_1) (MON: monotone6_3 gf_2) r_0 r_1 r_2,
  paco6_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 <6= gf_1 (upaco6_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco6_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco6_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof. unfold monotone6_3; intros; destruct PR; eauto. Qed.

Theorem paco6_3_2_unfold: forall (MON: monotone6_3 gf_0) (MON: monotone6_3 gf_1) (MON: monotone6_3 gf_2) r_0 r_1 r_2,
  paco6_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 <6= gf_2 (upaco6_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco6_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2) (upaco6_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2).
Proof. unfold monotone6_3; intros; destruct PR; eauto. Qed.

End Arg6_3.

Hint Unfold monotone6_3.
Hint Resolve paco6_3_0_fold.
Hint Resolve paco6_3_1_fold.
Hint Resolve paco6_3_2_fold.

Arguments paco6_3_0_acc            [ T0 T1 T2 T3 T4 T5 ].
Arguments paco6_3_1_acc            [ T0 T1 T2 T3 T4 T5 ].
Arguments paco6_3_2_acc            [ T0 T1 T2 T3 T4 T5 ].
Arguments paco6_3_0_mon            [ T0 T1 T2 T3 T4 T5 ].
Arguments paco6_3_1_mon            [ T0 T1 T2 T3 T4 T5 ].
Arguments paco6_3_2_mon            [ T0 T1 T2 T3 T4 T5 ].
Arguments paco6_3_0_mult_strong    [ T0 T1 T2 T3 T4 T5 ].
Arguments paco6_3_1_mult_strong    [ T0 T1 T2 T3 T4 T5 ].
Arguments paco6_3_2_mult_strong    [ T0 T1 T2 T3 T4 T5 ].
Arguments paco6_3_0_mult           [ T0 T1 T2 T3 T4 T5 ].
Arguments paco6_3_1_mult           [ T0 T1 T2 T3 T4 T5 ].
Arguments paco6_3_2_mult           [ T0 T1 T2 T3 T4 T5 ].
Arguments paco6_3_0_fold           [ T0 T1 T2 T3 T4 T5 ].
Arguments paco6_3_1_fold           [ T0 T1 T2 T3 T4 T5 ].
Arguments paco6_3_2_fold           [ T0 T1 T2 T3 T4 T5 ].
Arguments paco6_3_0_unfold         [ T0 T1 T2 T3 T4 T5 ].
Arguments paco6_3_1_unfold         [ T0 T1 T2 T3 T4 T5 ].
Arguments paco6_3_2_unfold         [ T0 T1 T2 T3 T4 T5 ].

Instance paco6_3_0_inst  T0 T1 T2 T3 T4 T5 (gf_0 gf_1 gf_2 : rel6 T0 T1 T2 T3 T4 T5->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 : paco_class (paco6_3_0 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4 x5) :=
{ pacoacc    := paco6_3_0_acc gf_0 gf_1 gf_2;
  pacomult   := paco6_3_0_mult gf_0 gf_1 gf_2;
  pacofold   := paco6_3_0_fold gf_0 gf_1 gf_2;
  pacounfold := paco6_3_0_unfold gf_0 gf_1 gf_2 }.

Instance paco6_3_1_inst  T0 T1 T2 T3 T4 T5 (gf_0 gf_1 gf_2 : rel6 T0 T1 T2 T3 T4 T5->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 : paco_class (paco6_3_1 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4 x5) :=
{ pacoacc    := paco6_3_1_acc gf_0 gf_1 gf_2;
  pacomult   := paco6_3_1_mult gf_0 gf_1 gf_2;
  pacofold   := paco6_3_1_fold gf_0 gf_1 gf_2;
  pacounfold := paco6_3_1_unfold gf_0 gf_1 gf_2 }.

Instance paco6_3_2_inst  T0 T1 T2 T3 T4 T5 (gf_0 gf_1 gf_2 : rel6 T0 T1 T2 T3 T4 T5->_) r_0 r_1 r_2 x0 x1 x2 x3 x4 x5 : paco_class (paco6_3_2 gf_0 gf_1 gf_2 r_0 r_1 r_2 x0 x1 x2 x3 x4 x5) :=
{ pacoacc    := paco6_3_2_acc gf_0 gf_1 gf_2;
  pacomult   := paco6_3_2_mult gf_0 gf_1 gf_2;
  pacofold   := paco6_3_2_fold gf_0 gf_1 gf_2;
  pacounfold := paco6_3_2_unfold gf_0 gf_1 gf_2 }.

