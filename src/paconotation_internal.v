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

