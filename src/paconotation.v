(** * Common notations and definitions *)

(** ** Types of dependent predicates *)

Definition rel0 :=
  Prop.
Arguments rel0 : clear implicits.

Definition rel1 T0 :=
  forall (x0: T0), Prop.
Arguments rel1 : clear implicits.

Definition rel2 T0 T1 :=
  forall (x0: T0) (x1: T1 x0), Prop.
Arguments rel2 : clear implicits.

Definition rel3 T0 T1 T2 :=
  forall (x0: T0) (x1: T1 x0) (x2: T2 x0 x1), Prop.
Arguments rel3 : clear implicits.

Definition rel4 T0 T1 T2 T3 :=
  forall (x0: T0) (x1: T1 x0) (x2: T2 x0 x1) (x3: T3 x0 x1 x2), Prop.
Arguments rel4 : clear implicits.

Definition rel5 T0 T1 T2 T3 T4 :=
  forall (x0: T0) (x1: T1 x0) (x2: T2 x0 x1) (x3: T3 x0 x1 x2) (x4: T4 x0 x1 x2 x3), Prop.
Arguments rel5 : clear implicits.

Definition rel6 T0 T1 T2 T3 T4 T5 :=
  forall (x0: T0) (x1: T1 x0) (x2: T2 x0 x1) (x3: T3 x0 x1 x2) (x4: T4 x0 x1 x2 x3) (x5: T5 x0 x1 x2 x3 x4), Prop.
Arguments rel6 : clear implicits.

Definition rel7 T0 T1 T2 T3 T4 T5 T6 :=
  forall (x0: T0) (x1: T1 x0) (x2: T2 x0 x1) (x3: T3 x0 x1 x2) (x4: T4 x0 x1 x2 x3) (x5: T5 x0 x1 x2 x3 x4) (x6: T6 x0 x1 x2 x3 x4 x5), Prop.
Arguments rel7 : clear implicits.

Definition rel8 T0 T1 T2 T3 T4 T5 T6 T7 :=
  forall (x0: T0) (x1: T1 x0) (x2: T2 x0 x1) (x3: T3 x0 x1 x2) (x4: T4 x0 x1 x2 x3) (x5: T5 x0 x1 x2 x3 x4) (x6: T6 x0 x1 x2 x3 x4 x5) (x7: T7 x0 x1 x2 x3 x4 x5 x6), Prop.
Arguments rel8 : clear implicits.

Definition rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 :=
  forall (x0: T0) (x1: T1 x0) (x2: T2 x0 x1) (x3: T3 x0 x1 x2) (x4: T4 x0 x1 x2 x3) (x5: T5 x0 x1 x2 x3 x4) (x6: T6 x0 x1 x2 x3 x4 x5) (x7: T7 x0 x1 x2 x3 x4 x5 x6) (x8: T8 x0 x1 x2 x3 x4 x5 x6 x7), Prop.
Arguments rel9 : clear implicits.

(** ** Bottom *)

Definition bot0 := False.

Definition bot1 { T0} (x0: T0) := False.

Definition bot2 { T0 T1} (x0: T0) (x1: T1 x0) := False.

Definition bot3 { T0 T1 T2} (x0: T0) (x1: T1 x0) (x2: T2 x0 x1) := False.

Definition bot4 { T0 T1 T2 T3} (x0: T0) (x1: T1 x0) (x2: T2 x0 x1) (x3: T3 x0 x1 x2) := False.

Definition bot5 { T0 T1 T2 T3 T4} (x0: T0) (x1: T1 x0) (x2: T2 x0 x1) (x3: T3 x0 x1 x2) (x4: T4 x0 x1 x2 x3) := False.

Definition bot6 { T0 T1 T2 T3 T4 T5} (x0: T0) (x1: T1 x0) (x2: T2 x0 x1) (x3: T3 x0 x1 x2) (x4: T4 x0 x1 x2 x3) (x5: T5 x0 x1 x2 x3 x4) := False.

Definition bot7 { T0 T1 T2 T3 T4 T5 T6} (x0: T0) (x1: T1 x0) (x2: T2 x0 x1) (x3: T3 x0 x1 x2) (x4: T4 x0 x1 x2 x3) (x5: T5 x0 x1 x2 x3 x4) (x6: T6 x0 x1 x2 x3 x4 x5) := False.

Definition bot8 { T0 T1 T2 T3 T4 T5 T6 T7} (x0: T0) (x1: T1 x0) (x2: T2 x0 x1) (x3: T3 x0 x1 x2) (x4: T4 x0 x1 x2 x3) (x5: T5 x0 x1 x2 x3 x4) (x6: T6 x0 x1 x2 x3 x4 x5) (x7: T7 x0 x1 x2 x3 x4 x5 x6) := False.

Definition bot9 { T0 T1 T2 T3 T4 T5 T6 T7 T8} (x0: T0) (x1: T1 x0) (x2: T2 x0 x1) (x3: T3 x0 x1 x2) (x4: T4 x0 x1 x2 x3) (x5: T5 x0 x1 x2 x3 x4) (x6: T6 x0 x1 x2 x3 x4 x5) (x7: T7 x0 x1 x2 x3 x4 x5 x6) (x8: T8 x0 x1 x2 x3 x4 x5 x6 x7) := False.

(** ** Less than or equal *)

Notation "p <0= q" :=
  (forall (PR: p : Prop), q : Prop)
  (at level 50, no associativity, only parsing).

Notation "p <1= q" :=
  (forall x0 (PR: p x0 : Prop), q x0 : Prop)
  (at level 50, no associativity).

Notation "p <2= q" :=
  (forall x0 x1 (PR: p x0 x1 : Prop), q x0 x1 : Prop)
  (at level 50, no associativity).

Notation "p <3= q" :=
  (forall x0 x1 x2 (PR: p x0 x1 x2 : Prop), q x0 x1 x2 : Prop)
  (at level 50, no associativity).

Notation "p <4= q" :=
  (forall x0 x1 x2 x3 (PR: p x0 x1 x2 x3 : Prop), q x0 x1 x2 x3 : Prop)
  (at level 50, no associativity).

Notation "p <5= q" :=
  (forall x0 x1 x2 x3 x4 (PR: p x0 x1 x2 x3 x4 : Prop), q x0 x1 x2 x3 x4 : Prop)
  (at level 50, no associativity).

Notation "p <6= q" :=
  (forall x0 x1 x2 x3 x4 x5 (PR: p x0 x1 x2 x3 x4 x5 : Prop), q x0 x1 x2 x3 x4 x5 : Prop)
  (at level 50, no associativity).

Notation "p <7= q" :=
  (forall x0 x1 x2 x3 x4 x5 x6 (PR: p x0 x1 x2 x3 x4 x5 x6 : Prop), q x0 x1 x2 x3 x4 x5 x6 : Prop)
  (at level 50, no associativity).

Notation "p <8= q" :=
  (forall x0 x1 x2 x3 x4 x5 x6 x7 (PR: p x0 x1 x2 x3 x4 x5 x6 x7 : Prop), q x0 x1 x2 x3 x4 x5 x6 x7 : Prop)
  (at level 50, no associativity).

Notation "p <9= q" :=
  (forall x0 x1 x2 x3 x4 x5 x6 x7 x8 (PR: p x0 x1 x2 x3 x4 x5 x6 x7 x8 : Prop), q x0 x1 x2 x3 x4 x5 x6 x7 x8 : Prop)
  (at level 50, no associativity).

(** ** Union *)

Notation "p \0/ q" :=
  (p \/ q)
  (at level 50, no associativity, only parsing).

Notation "p \1/ q" :=
  (fun x0 => p x0 \/ q x0)
  (at level 50, no associativity).

Notation "p \2/ q" :=
  (fun x0 x1 => p x0 x1 \/ q x0 x1)
  (at level 50, no associativity).

Notation "p \3/ q" :=
  (fun x0 x1 x2 => p x0 x1 x2 \/ q x0 x1 x2)
  (at level 50, no associativity).

Notation "p \4/ q" :=
  (fun x0 x1 x2 x3 => p x0 x1 x2 x3 \/ q x0 x1 x2 x3)
  (at level 50, no associativity).

Notation "p \5/ q" :=
  (fun x0 x1 x2 x3 x4 => p x0 x1 x2 x3 x4 \/ q x0 x1 x2 x3 x4)
  (at level 50, no associativity).

Notation "p \6/ q" :=
  (fun x0 x1 x2 x3 x4 x5 => p x0 x1 x2 x3 x4 x5 \/ q x0 x1 x2 x3 x4 x5)
  (at level 50, no associativity).

Notation "p \7/ q" :=
  (fun x0 x1 x2 x3 x4 x5 x6 => p x0 x1 x2 x3 x4 x5 x6 \/ q x0 x1 x2 x3 x4 x5 x6)
  (at level 50, no associativity).

Notation "p \8/ q" :=
  (fun x0 x1 x2 x3 x4 x5 x6 x7 => p x0 x1 x2 x3 x4 x5 x6 x7 \/ q x0 x1 x2 x3 x4 x5 x6 x7)
  (at level 50, no associativity).

Notation "p \9/ q" :=
  (fun x0 x1 x2 x3 x4 x5 x6 x7 x8 => p x0 x1 x2 x3 x4 x5 x6 x7 x8 \/ q x0 x1 x2 x3 x4 x5 x6 x7 x8)
  (at level 50, no associativity).

(** ** Intersection *)

Notation "p /0\ q" :=
  (p /\ q)
  (at level 50, no associativity, only parsing).

Notation "p /1\ q" :=
  (fun x0 => p x0 /\ q x0)
  (at level 50, no associativity).

Notation "p /2\ q" :=
  (fun x0 x1 => p x0 x1 /\ q x0 x1)
  (at level 50, no associativity).

Notation "p /3\ q" :=
  (fun x0 x1 x2 => p x0 x1 x2 /\ q x0 x1 x2)
  (at level 50, no associativity).

Notation "p /4\ q" :=
  (fun x0 x1 x2 x3 => p x0 x1 x2 x3 /\ q x0 x1 x2 x3)
  (at level 50, no associativity).

Notation "p /5\ q" :=
  (fun x0 x1 x2 x3 x4 => p x0 x1 x2 x3 x4 /\ q x0 x1 x2 x3 x4)
  (at level 50, no associativity).

Notation "p /6\ q" :=
  (fun x0 x1 x2 x3 x4 x5 => p x0 x1 x2 x3 x4 x5 /\ q x0 x1 x2 x3 x4 x5)
  (at level 50, no associativity).

Notation "p /7\ q" :=
  (fun x0 x1 x2 x3 x4 x5 x6 => p x0 x1 x2 x3 x4 x5 x6 /\ q x0 x1 x2 x3 x4 x5 x6)
  (at level 50, no associativity).

Notation "p /8\ q" :=
  (fun x0 x1 x2 x3 x4 x5 x6 x7 => p x0 x1 x2 x3 x4 x5 x6 x7 /\ q x0 x1 x2 x3 x4 x5 x6 x7)
  (at level 50, no associativity).

Notation "p /9\ q" :=
  (fun x0 x1 x2 x3 x4 x5 x6 x7 x8 => p x0 x1 x2 x3 x4 x5 x6 x7 x8 /\ q x0 x1 x2 x3 x4 x5 x6 x7 x8)
  (at level 50, no associativity).

