Require Import paconotation.

Tactic Notation "repeat_intros" int(n)
 := let name := fresh "x" in
     do n (let name := fresh "x" in intros name).

(** ** Less than or equal *)

Definition le0 (p q : rel0) :=
  (forall (PR: p : Prop), q : Prop).
Arguments le0 : clear implicits.

Definition le1 T0 (p q : rel1 T0) :=
  (forall x0 (PR: p x0 : Prop), q x0 : Prop).
Arguments le1 [ T0].

Definition le2 T0 T1 (p q : rel2 T0 T1) :=
  (forall x0 x1 (PR: p x0 x1 : Prop), q x0 x1 : Prop).
Arguments le2 [ T0 T1].

Definition le3 T0 T1 T2 (p q : rel3 T0 T1 T2) :=
  (forall x0 x1 x2 (PR: p x0 x1 x2 : Prop), q x0 x1 x2 : Prop).
Arguments le3 [ T0 T1 T2].

Definition le4 T0 T1 T2 T3 (p q : rel4 T0 T1 T2 T3) :=
  (forall x0 x1 x2 x3 (PR: p x0 x1 x2 x3 : Prop), q x0 x1 x2 x3 : Prop).
Arguments le4 [ T0 T1 T2 T3].

Definition le5 T0 T1 T2 T3 T4 (p q : rel5 T0 T1 T2 T3 T4) :=
  (forall x0 x1 x2 x3 x4 (PR: p x0 x1 x2 x3 x4 : Prop), q x0 x1 x2 x3 x4 : Prop).
Arguments le5 [ T0 T1 T2 T3 T4].

Definition le6 T0 T1 T2 T3 T4 T5 (p q : rel6 T0 T1 T2 T3 T4 T5) :=
  (forall x0 x1 x2 x3 x4 x5 (PR: p x0 x1 x2 x3 x4 x5 : Prop), q x0 x1 x2 x3 x4 x5 : Prop).
Arguments le6 [ T0 T1 T2 T3 T4 T5].

Definition le7 T0 T1 T2 T3 T4 T5 T6 (p q : rel7 T0 T1 T2 T3 T4 T5 T6) :=
  (forall x0 x1 x2 x3 x4 x5 x6 (PR: p x0 x1 x2 x3 x4 x5 x6 : Prop), q x0 x1 x2 x3 x4 x5 x6 : Prop).
Arguments le7 [ T0 T1 T2 T3 T4 T5 T6].

Definition le8 T0 T1 T2 T3 T4 T5 T6 T7 (p q : rel8 T0 T1 T2 T3 T4 T5 T6 T7) :=
  (forall x0 x1 x2 x3 x4 x5 x6 x7 (PR: p x0 x1 x2 x3 x4 x5 x6 x7 : Prop), q x0 x1 x2 x3 x4 x5 x6 x7 : Prop).
Arguments le8 [ T0 T1 T2 T3 T4 T5 T6 T7].

Definition le9 T0 T1 T2 T3 T4 T5 T6 T7 T8 (p q : rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8) :=
  (forall x0 x1 x2 x3 x4 x5 x6 x7 x8 (PR: p x0 x1 x2 x3 x4 x5 x6 x7 x8 : Prop), q x0 x1 x2 x3 x4 x5 x6 x7 x8 : Prop).
Arguments le9 [ T0 T1 T2 T3 T4 T5 T6 T7 T8].

Definition le10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 (p q : rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) :=
  (forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 (PR: p x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Prop), q x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Prop).
Arguments le10 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9].

Definition le11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 (p q : rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10) :=
  (forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (PR: p x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : Prop), q x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : Prop).
Arguments le11 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10].

Definition le12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 (p q : rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11) :=
  (forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 (PR: p x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Prop), q x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Prop).
Arguments le12 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11].

Definition le13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 (p q : rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12) :=
  (forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 (PR: p x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : Prop), q x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : Prop).
Arguments le13 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12].

Definition le14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 (p q : rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13) :=
  (forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 (PR: p x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : Prop), q x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : Prop).
Arguments le14 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13].

Definition le15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 (p q : rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14) :=
  (forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 (PR: p x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : Prop), q x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : Prop).
Arguments le15 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14].

Definition le16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 (p q : rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15) :=
  (forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 (PR: p x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : Prop), q x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : Prop).
Arguments le16 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15].

Definition le17 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 (p q : rel17 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16) :=
  (forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 (PR: p x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : Prop), q x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : Prop).
Arguments le17 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16].

Definition le18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 (p q : rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17) :=
  (forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 (PR: p x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : Prop), q x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : Prop).
Arguments le18 [ T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17].

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

Notation "p <9== q" :=
  (le9 p q)
  (at level 50, no associativity).

Notation "p <10== q" :=
  (le10 p q)
  (at level 50, no associativity).

Notation "p <11== q" :=
  (le11 p q)
  (at level 50, no associativity).

Notation "p <12== q" :=
  (le12 p q)
  (at level 50, no associativity).

Notation "p <13== q" :=
  (le13 p q)
  (at level 50, no associativity).

Notation "p <14== q" :=
  (le14 p q)
  (at level 50, no associativity).

Notation "p <15== q" :=
  (le15 p q)
  (at level 50, no associativity).

Notation "p <16== q" :=
  (le16 p q)
  (at level 50, no associativity).

Notation "p <17== q" :=
  (le17 p q)
  (at level 50, no associativity).

Notation "p <18== q" :=
  (le18 p q)
  (at level 50, no associativity).

(** ** Tranisitivity and Reflexivity *)

Lemma le0_trans(r0 r1 r2 : rel0)
      (LE0 : r0 <0== r1) (LE1 : r1 <0== r2) :
  r0 <0== r2.
Proof. repeat_intros 0. intros H. eapply LE1, LE0, H. Qed.

Lemma le1_trans T0(r0 r1 r2 : rel1 T0)
      (LE0 : r0 <1== r1) (LE1 : r1 <1== r2) :
  r0 <1== r2.
Proof. repeat_intros 1. intros H. eapply LE1, LE0, H. Qed.

Lemma le2_trans T0 T1(r0 r1 r2 : rel2 T0 T1)
      (LE0 : r0 <2== r1) (LE1 : r1 <2== r2) :
  r0 <2== r2.
Proof. repeat_intros 2. intros H. eapply LE1, LE0, H. Qed.

Lemma le3_trans T0 T1 T2(r0 r1 r2 : rel3 T0 T1 T2)
      (LE0 : r0 <3== r1) (LE1 : r1 <3== r2) :
  r0 <3== r2.
Proof. repeat_intros 3. intros H. eapply LE1, LE0, H. Qed.

Lemma le4_trans T0 T1 T2 T3(r0 r1 r2 : rel4 T0 T1 T2 T3)
      (LE0 : r0 <4== r1) (LE1 : r1 <4== r2) :
  r0 <4== r2.
Proof. repeat_intros 4. intros H. eapply LE1, LE0, H. Qed.

Lemma le5_trans T0 T1 T2 T3 T4(r0 r1 r2 : rel5 T0 T1 T2 T3 T4)
      (LE0 : r0 <5== r1) (LE1 : r1 <5== r2) :
  r0 <5== r2.
Proof. repeat_intros 5. intros H. eapply LE1, LE0, H. Qed.

Lemma le6_trans T0 T1 T2 T3 T4 T5(r0 r1 r2 : rel6 T0 T1 T2 T3 T4 T5)
      (LE0 : r0 <6== r1) (LE1 : r1 <6== r2) :
  r0 <6== r2.
Proof. repeat_intros 6. intros H. eapply LE1, LE0, H. Qed.

Lemma le7_trans T0 T1 T2 T3 T4 T5 T6(r0 r1 r2 : rel7 T0 T1 T2 T3 T4 T5 T6)
      (LE0 : r0 <7== r1) (LE1 : r1 <7== r2) :
  r0 <7== r2.
Proof. repeat_intros 7. intros H. eapply LE1, LE0, H. Qed.

Lemma le8_trans T0 T1 T2 T3 T4 T5 T6 T7(r0 r1 r2 : rel8 T0 T1 T2 T3 T4 T5 T6 T7)
      (LE0 : r0 <8== r1) (LE1 : r1 <8== r2) :
  r0 <8== r2.
Proof. repeat_intros 8. intros H. eapply LE1, LE0, H. Qed.

Lemma le9_trans T0 T1 T2 T3 T4 T5 T6 T7 T8(r0 r1 r2 : rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8)
      (LE0 : r0 <9== r1) (LE1 : r1 <9== r2) :
  r0 <9== r2.
Proof. repeat_intros 9. intros H. eapply LE1, LE0, H. Qed.

Lemma le10_trans T0 T1 T2 T3 T4 T5 T6 T7 T8 T9(r0 r1 r2 : rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9)
      (LE0 : r0 <10== r1) (LE1 : r1 <10== r2) :
  r0 <10== r2.
Proof. repeat_intros 10. intros H. eapply LE1, LE0, H. Qed.

Lemma le11_trans T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10(r0 r1 r2 : rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10)
      (LE0 : r0 <11== r1) (LE1 : r1 <11== r2) :
  r0 <11== r2.
Proof. repeat_intros 11. intros H. eapply LE1, LE0, H. Qed.

Lemma le12_trans T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11(r0 r1 r2 : rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11)
      (LE0 : r0 <12== r1) (LE1 : r1 <12== r2) :
  r0 <12== r2.
Proof. repeat_intros 12. intros H. eapply LE1, LE0, H. Qed.

Lemma le13_trans T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12(r0 r1 r2 : rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12)
      (LE0 : r0 <13== r1) (LE1 : r1 <13== r2) :
  r0 <13== r2.
Proof. repeat_intros 13. intros H. eapply LE1, LE0, H. Qed.

Lemma le14_trans T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13(r0 r1 r2 : rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13)
      (LE0 : r0 <14== r1) (LE1 : r1 <14== r2) :
  r0 <14== r2.
Proof. repeat_intros 14. intros H. eapply LE1, LE0, H. Qed.

Lemma le15_trans T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14(r0 r1 r2 : rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14)
      (LE0 : r0 <15== r1) (LE1 : r1 <15== r2) :
  r0 <15== r2.
Proof. repeat_intros 15. intros H. eapply LE1, LE0, H. Qed.

Lemma le16_trans T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15(r0 r1 r2 : rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15)
      (LE0 : r0 <16== r1) (LE1 : r1 <16== r2) :
  r0 <16== r2.
Proof. repeat_intros 16. intros H. eapply LE1, LE0, H. Qed.

Lemma le17_trans T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16(r0 r1 r2 : rel17 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16)
      (LE0 : r0 <17== r1) (LE1 : r1 <17== r2) :
  r0 <17== r2.
Proof. repeat_intros 17. intros H. eapply LE1, LE0, H. Qed.

Lemma le18_trans T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17(r0 r1 r2 : rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17)
      (LE0 : r0 <18== r1) (LE1 : r1 <18== r2) :
  r0 <18== r2.
Proof. repeat_intros 18. intros H. eapply LE1, LE0, H. Qed.

Lemma le0_refl(r : rel0) :
  r <0== r.
Proof. repeat_intros 0. intros H. apply H. Qed.

Lemma le1_refl T0(r : rel1 T0) :
  r <1== r.
Proof. repeat_intros 1. intros H. apply H. Qed.

Lemma le2_refl T0 T1(r : rel2 T0 T1) :
  r <2== r.
Proof. repeat_intros 2. intros H. apply H. Qed.

Lemma le3_refl T0 T1 T2(r : rel3 T0 T1 T2) :
  r <3== r.
Proof. repeat_intros 3. intros H. apply H. Qed.

Lemma le4_refl T0 T1 T2 T3(r : rel4 T0 T1 T2 T3) :
  r <4== r.
Proof. repeat_intros 4. intros H. apply H. Qed.

Lemma le5_refl T0 T1 T2 T3 T4(r : rel5 T0 T1 T2 T3 T4) :
  r <5== r.
Proof. repeat_intros 5. intros H. apply H. Qed.

Lemma le6_refl T0 T1 T2 T3 T4 T5(r : rel6 T0 T1 T2 T3 T4 T5) :
  r <6== r.
Proof. repeat_intros 6. intros H. apply H. Qed.

Lemma le7_refl T0 T1 T2 T3 T4 T5 T6(r : rel7 T0 T1 T2 T3 T4 T5 T6) :
  r <7== r.
Proof. repeat_intros 7. intros H. apply H. Qed.

Lemma le8_refl T0 T1 T2 T3 T4 T5 T6 T7(r : rel8 T0 T1 T2 T3 T4 T5 T6 T7) :
  r <8== r.
Proof. repeat_intros 8. intros H. apply H. Qed.

Lemma le9_refl T0 T1 T2 T3 T4 T5 T6 T7 T8(r : rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8) :
  r <9== r.
Proof. repeat_intros 9. intros H. apply H. Qed.

Lemma le10_refl T0 T1 T2 T3 T4 T5 T6 T7 T8 T9(r : rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9) :
  r <10== r.
Proof. repeat_intros 10. intros H. apply H. Qed.

Lemma le11_refl T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10(r : rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10) :
  r <11== r.
Proof. repeat_intros 11. intros H. apply H. Qed.

Lemma le12_refl T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11(r : rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11) :
  r <12== r.
Proof. repeat_intros 12. intros H. apply H. Qed.

Lemma le13_refl T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12(r : rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12) :
  r <13== r.
Proof. repeat_intros 13. intros H. apply H. Qed.

Lemma le14_refl T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13(r : rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13) :
  r <14== r.
Proof. repeat_intros 14. intros H. apply H. Qed.

Lemma le15_refl T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14(r : rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14) :
  r <15== r.
Proof. repeat_intros 15. intros H. apply H. Qed.

Lemma le16_refl T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15(r : rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15) :
  r <16== r.
Proof. repeat_intros 16. intros H. apply H. Qed.

Lemma le17_refl T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16(r : rel17 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16) :
  r <17== r.
Proof. repeat_intros 17. intros H. apply H. Qed.

Lemma le18_refl T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17(r : rel18 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17) :
  r <18== r.
Proof. repeat_intros 18. intros H. apply H. Qed.

