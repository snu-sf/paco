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

(** ** Bottom *)

Definition bot0 := False.

Definition bot1 { T0} (x0: T0) := False.

Definition bot2 { T0 T1} (x0: T0) (x1: T1 x0) := False.

Definition bot3 { T0 T1 T2} (x0: T0) (x1: T1 x0) (x2: T2 x0 x1) := False.

Definition bot4 { T0 T1 T2 T3} (x0: T0) (x1: T1 x0) (x2: T2 x0 x1) (x3: T3 x0 x1 x2) := False.

Definition bot5 { T0 T1 T2 T3 T4} (x0: T0) (x1: T1 x0) (x2: T2 x0 x1) (x3: T3 x0 x1 x2) (x4: T4 x0 x1 x2 x3) := False.

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

