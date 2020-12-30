From Paco Require Import paconotation.

(** ** Less than or equal *)

Definition le0 (p q : rel0) :=
  (forall (PR: p : Prop), q : Prop).
Arguments le0 : clear implicits.

Definition le1 T0 (p q : rel1 T0) :=
  (forall x0 (PR: p x0 : Prop), q x0 : Prop).
Arguments le1 [ T0] p q.

Definition le2 T0 T1 (p q : rel2 T0 T1) :=
  (forall x0 x1 (PR: p x0 x1 : Prop), q x0 x1 : Prop).
Arguments le2 [ T0 T1] p q.

Definition le3 T0 T1 T2 (p q : rel3 T0 T1 T2) :=
  (forall x0 x1 x2 (PR: p x0 x1 x2 : Prop), q x0 x1 x2 : Prop).
Arguments le3 [ T0 T1 T2] p q.

Definition le4 T0 T1 T2 T3 (p q : rel4 T0 T1 T2 T3) :=
  (forall x0 x1 x2 x3 (PR: p x0 x1 x2 x3 : Prop), q x0 x1 x2 x3 : Prop).
Arguments le4 [ T0 T1 T2 T3] p q.

Definition le5 T0 T1 T2 T3 T4 (p q : rel5 T0 T1 T2 T3 T4) :=
  (forall x0 x1 x2 x3 x4 (PR: p x0 x1 x2 x3 x4 : Prop), q x0 x1 x2 x3 x4 : Prop).
Arguments le5 [ T0 T1 T2 T3 T4] p q.

Definition le6 T0 T1 T2 T3 T4 T5 (p q : rel6 T0 T1 T2 T3 T4 T5) :=
  (forall x0 x1 x2 x3 x4 x5 (PR: p x0 x1 x2 x3 x4 x5 : Prop), q x0 x1 x2 x3 x4 x5 : Prop).
Arguments le6 [ T0 T1 T2 T3 T4 T5] p q.

Definition le7 T0 T1 T2 T3 T4 T5 T6 (p q : rel7 T0 T1 T2 T3 T4 T5 T6) :=
  (forall x0 x1 x2 x3 x4 x5 x6 (PR: p x0 x1 x2 x3 x4 x5 x6 : Prop), q x0 x1 x2 x3 x4 x5 x6 : Prop).
Arguments le7 [ T0 T1 T2 T3 T4 T5 T6] p q.

Definition le8 T0 T1 T2 T3 T4 T5 T6 T7 (p q : rel8 T0 T1 T2 T3 T4 T5 T6 T7) :=
  (forall x0 x1 x2 x3 x4 x5 x6 x7 (PR: p x0 x1 x2 x3 x4 x5 x6 x7 : Prop), q x0 x1 x2 x3 x4 x5 x6 x7 : Prop).
Arguments le8 [ T0 T1 T2 T3 T4 T5 T6 T7] p q.

Notation "p <0== q" :=
  (le0 p q)
  (at level 50, no associativity, only parsing).

Notation "p <1== q" :=
  (le1 p q)
  (at level 50, no associativity).

Notation "p <2== q" :=
  (le2 p q)
  (at level 50, no associativity).

Notation "p <3== q" :=
  (le3 p q)
  (at level 50, no associativity).

Notation "p <4== q" :=
  (le4 p q)
  (at level 50, no associativity).

Notation "p <5== q" :=
  (le5 p q)
  (at level 50, no associativity).

Notation "p <6== q" :=
  (le6 p q)
  (at level 50, no associativity).

Notation "p <7== q" :=
  (le7 p q)
  (at level 50, no associativity).

Notation "p <8== q" :=
  (le8 p q)
  (at level 50, no associativity).

(** ** Tranisitivity and Reflexivity *)

Lemma le0_trans(r0 r1 r2 : rel0)
      (LE0 : r0 <0== r1) (LE1 : r1 <0== r2) :
  r0 <0== r2.
Proof. do 0 intro. intros H. eapply LE1, LE0, H. Qed.

Lemma le1_trans T0(r0 r1 r2 : rel1 T0)
      (LE0 : r0 <1== r1) (LE1 : r1 <1== r2) :
  r0 <1== r2.
Proof. do 1 intro. intros H. eapply LE1, LE0, H. Qed.

Lemma le2_trans T0 T1(r0 r1 r2 : rel2 T0 T1)
      (LE0 : r0 <2== r1) (LE1 : r1 <2== r2) :
  r0 <2== r2.
Proof. do 2 intro. intros H. eapply LE1, LE0, H. Qed.

Lemma le3_trans T0 T1 T2(r0 r1 r2 : rel3 T0 T1 T2)
      (LE0 : r0 <3== r1) (LE1 : r1 <3== r2) :
  r0 <3== r2.
Proof. do 3 intro. intros H. eapply LE1, LE0, H. Qed.

Lemma le4_trans T0 T1 T2 T3(r0 r1 r2 : rel4 T0 T1 T2 T3)
      (LE0 : r0 <4== r1) (LE1 : r1 <4== r2) :
  r0 <4== r2.
Proof. do 4 intro. intros H. eapply LE1, LE0, H. Qed.

Lemma le5_trans T0 T1 T2 T3 T4(r0 r1 r2 : rel5 T0 T1 T2 T3 T4)
      (LE0 : r0 <5== r1) (LE1 : r1 <5== r2) :
  r0 <5== r2.
Proof. do 5 intro. intros H. eapply LE1, LE0, H. Qed.

Lemma le6_trans T0 T1 T2 T3 T4 T5(r0 r1 r2 : rel6 T0 T1 T2 T3 T4 T5)
      (LE0 : r0 <6== r1) (LE1 : r1 <6== r2) :
  r0 <6== r2.
Proof. do 6 intro. intros H. eapply LE1, LE0, H. Qed.

Lemma le7_trans T0 T1 T2 T3 T4 T5 T6(r0 r1 r2 : rel7 T0 T1 T2 T3 T4 T5 T6)
      (LE0 : r0 <7== r1) (LE1 : r1 <7== r2) :
  r0 <7== r2.
Proof. do 7 intro. intros H. eapply LE1, LE0, H. Qed.

Lemma le8_trans T0 T1 T2 T3 T4 T5 T6 T7(r0 r1 r2 : rel8 T0 T1 T2 T3 T4 T5 T6 T7)
      (LE0 : r0 <8== r1) (LE1 : r1 <8== r2) :
  r0 <8== r2.
Proof. do 8 intro. intros H. eapply LE1, LE0, H. Qed.

Lemma le0_refl(r : rel0) :
  r <0== r.
Proof. do 0 intro. intros H. apply H. Qed.

Lemma le1_refl T0(r : rel1 T0) :
  r <1== r.
Proof. do 1 intro. intros H. apply H. Qed.

Lemma le2_refl T0 T1(r : rel2 T0 T1) :
  r <2== r.
Proof. do 2 intro. intros H. apply H. Qed.

Lemma le3_refl T0 T1 T2(r : rel3 T0 T1 T2) :
  r <3== r.
Proof. do 3 intro. intros H. apply H. Qed.

Lemma le4_refl T0 T1 T2 T3(r : rel4 T0 T1 T2 T3) :
  r <4== r.
Proof. do 4 intro. intros H. apply H. Qed.

Lemma le5_refl T0 T1 T2 T3 T4(r : rel5 T0 T1 T2 T3 T4) :
  r <5== r.
Proof. do 5 intro. intros H. apply H. Qed.

Lemma le6_refl T0 T1 T2 T3 T4 T5(r : rel6 T0 T1 T2 T3 T4 T5) :
  r <6== r.
Proof. do 6 intro. intros H. apply H. Qed.

Lemma le7_refl T0 T1 T2 T3 T4 T5 T6(r : rel7 T0 T1 T2 T3 T4 T5 T6) :
  r <7== r.
Proof. do 7 intro. intros H. apply H. Qed.

Lemma le8_refl T0 T1 T2 T3 T4 T5 T6 T7(r : rel8 T0 T1 T2 T3 T4 T5 T6 T7) :
  r <8== r.
Proof. do 8 intro. intros H. apply H. Qed.

