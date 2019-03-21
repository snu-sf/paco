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

Definition rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 :=
  forall (x0: T0) (x1: T1 x0) (x2: T2 x0 x1) (x3: T3 x0 x1 x2) (x4: T4 x0 x1 x2 x3) (x5: T5 x0 x1 x2 x3 x4) (x6: T6 x0 x1 x2 x3 x4 x5) (x7: T7 x0 x1 x2 x3 x4 x5 x6) (x8: T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: T9 x0 x1 x2 x3 x4 x5 x6 x7 x8), Prop.
Arguments rel10 : clear implicits.

Definition rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 :=
  forall (x0: T0) (x1: T1 x0) (x2: T2 x0 x1) (x3: T3 x0 x1 x2) (x4: T4 x0 x1 x2 x3) (x5: T5 x0 x1 x2 x3 x4) (x6: T6 x0 x1 x2 x3 x4 x5) (x7: T7 x0 x1 x2 x3 x4 x5 x6) (x8: T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9), Prop.
Arguments rel11 : clear implicits.

Definition rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 :=
  forall (x0: T0) (x1: T1 x0) (x2: T2 x0 x1) (x3: T3 x0 x1 x2) (x4: T4 x0 x1 x2 x3) (x5: T5 x0 x1 x2 x3 x4) (x6: T6 x0 x1 x2 x3 x4 x5) (x7: T7 x0 x1 x2 x3 x4 x5 x6) (x8: T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10), Prop.
Arguments rel12 : clear implicits.

Definition rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 :=
  forall (x0: T0) (x1: T1 x0) (x2: T2 x0 x1) (x3: T3 x0 x1 x2) (x4: T4 x0 x1 x2 x3) (x5: T5 x0 x1 x2 x3 x4) (x6: T6 x0 x1 x2 x3 x4 x5) (x7: T7 x0 x1 x2 x3 x4 x5 x6) (x8: T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) (x12: T12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11), Prop.
Arguments rel13 : clear implicits.

Definition rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 :=
  forall (x0: T0) (x1: T1 x0) (x2: T2 x0 x1) (x3: T3 x0 x1 x2) (x4: T4 x0 x1 x2 x3) (x5: T5 x0 x1 x2 x3 x4) (x6: T6 x0 x1 x2 x3 x4 x5) (x7: T7 x0 x1 x2 x3 x4 x5 x6) (x8: T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) (x12: T12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) (x13: T13 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12), Prop.
Arguments rel14 : clear implicits.

Definition rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 :=
  forall (x0: T0) (x1: T1 x0) (x2: T2 x0 x1) (x3: T3 x0 x1 x2) (x4: T4 x0 x1 x2 x3) (x5: T5 x0 x1 x2 x3 x4) (x6: T6 x0 x1 x2 x3 x4 x5) (x7: T7 x0 x1 x2 x3 x4 x5 x6) (x8: T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) (x12: T12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) (x13: T13 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) (x14: T14 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13), Prop.
Arguments rel15 : clear implicits.

Definition rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 :=
  forall (x0: T0) (x1: T1 x0) (x2: T2 x0 x1) (x3: T3 x0 x1 x2) (x4: T4 x0 x1 x2 x3) (x5: T5 x0 x1 x2 x3 x4) (x6: T6 x0 x1 x2 x3 x4 x5) (x7: T7 x0 x1 x2 x3 x4 x5 x6) (x8: T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) (x12: T12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) (x13: T13 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) (x14: T14 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) (x15: T15 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14), Prop.
Arguments rel16 : clear implicits.

(** ** Signatures *)

Record sig0T  :=
  exist0T {
    }.

Definition uncurry0  (R: rel0): rel1 sig0T :=
  fun x => R.
Definition curry0  (R: rel1 sig0T): rel0 :=
  R (exist0T).

Record sig1T { T0} :=
  exist1T {
      proj1T0: @T0;
    }.
Arguments exist1T { T0}.
Definition uncurry1 { T0} (R: rel1 T0): rel1 sig1T :=
  fun x => R (proj1T0 x).
Definition curry1 { T0} (R: rel1 sig1T): rel1 T0 :=
  fun x0 => R (exist1T x0).

Record sig2T { T0 T1} :=
  exist2T {
      proj2T0: @T0;
      proj2T1: @T1 proj2T0;
    }.
Arguments exist2T { T0 T1} [ proj2T0].
Definition uncurry2 { T0 T1} (R: rel2 T0 T1): rel1 sig2T :=
  fun x => R (proj2T0 x) (proj2T1 x).
Definition curry2 { T0 T1} (R: rel1 sig2T): rel2 T0 T1 :=
  fun x0 x1 => R (exist2T x1).

Record sig3T { T0 T1 T2} :=
  exist3T {
      proj3T0: @T0;
      proj3T1: @T1 proj3T0;
      proj3T2: @T2 proj3T0 proj3T1;
    }.
Arguments exist3T { T0 T1 T2} [ proj3T0 proj3T1].
Definition uncurry3 { T0 T1 T2} (R: rel3 T0 T1 T2): rel1 sig3T :=
  fun x => R (proj3T0 x) (proj3T1 x) (proj3T2 x).
Definition curry3 { T0 T1 T2} (R: rel1 sig3T): rel3 T0 T1 T2 :=
  fun x0 x1 x2 => R (exist3T x2).

Record sig4T { T0 T1 T2 T3} :=
  exist4T {
      proj4T0: @T0;
      proj4T1: @T1 proj4T0;
      proj4T2: @T2 proj4T0 proj4T1;
      proj4T3: @T3 proj4T0 proj4T1 proj4T2;
    }.
Arguments exist4T { T0 T1 T2 T3} [ proj4T0 proj4T1 proj4T2].
Definition uncurry4 { T0 T1 T2 T3} (R: rel4 T0 T1 T2 T3): rel1 sig4T :=
  fun x => R (proj4T0 x) (proj4T1 x) (proj4T2 x) (proj4T3 x).
Definition curry4 { T0 T1 T2 T3} (R: rel1 sig4T): rel4 T0 T1 T2 T3 :=
  fun x0 x1 x2 x3 => R (exist4T x3).

Record sig5T { T0 T1 T2 T3 T4} :=
  exist5T {
      proj5T0: @T0;
      proj5T1: @T1 proj5T0;
      proj5T2: @T2 proj5T0 proj5T1;
      proj5T3: @T3 proj5T0 proj5T1 proj5T2;
      proj5T4: @T4 proj5T0 proj5T1 proj5T2 proj5T3;
    }.
Arguments exist5T { T0 T1 T2 T3 T4} [ proj5T0 proj5T1 proj5T2 proj5T3].
Definition uncurry5 { T0 T1 T2 T3 T4} (R: rel5 T0 T1 T2 T3 T4): rel1 sig5T :=
  fun x => R (proj5T0 x) (proj5T1 x) (proj5T2 x) (proj5T3 x) (proj5T4 x).
Definition curry5 { T0 T1 T2 T3 T4} (R: rel1 sig5T): rel5 T0 T1 T2 T3 T4 :=
  fun x0 x1 x2 x3 x4 => R (exist5T x4).

Record sig6T { T0 T1 T2 T3 T4 T5} :=
  exist6T {
      proj6T0: @T0;
      proj6T1: @T1 proj6T0;
      proj6T2: @T2 proj6T0 proj6T1;
      proj6T3: @T3 proj6T0 proj6T1 proj6T2;
      proj6T4: @T4 proj6T0 proj6T1 proj6T2 proj6T3;
      proj6T5: @T5 proj6T0 proj6T1 proj6T2 proj6T3 proj6T4;
    }.
Arguments exist6T { T0 T1 T2 T3 T4 T5} [ proj6T0 proj6T1 proj6T2 proj6T3 proj6T4].
Definition uncurry6 { T0 T1 T2 T3 T4 T5} (R: rel6 T0 T1 T2 T3 T4 T5): rel1 sig6T :=
  fun x => R (proj6T0 x) (proj6T1 x) (proj6T2 x) (proj6T3 x) (proj6T4 x) (proj6T5 x).
Definition curry6 { T0 T1 T2 T3 T4 T5} (R: rel1 sig6T): rel6 T0 T1 T2 T3 T4 T5 :=
  fun x0 x1 x2 x3 x4 x5 => R (exist6T x5).

Record sig7T { T0 T1 T2 T3 T4 T5 T6} :=
  exist7T {
      proj7T0: @T0;
      proj7T1: @T1 proj7T0;
      proj7T2: @T2 proj7T0 proj7T1;
      proj7T3: @T3 proj7T0 proj7T1 proj7T2;
      proj7T4: @T4 proj7T0 proj7T1 proj7T2 proj7T3;
      proj7T5: @T5 proj7T0 proj7T1 proj7T2 proj7T3 proj7T4;
      proj7T6: @T6 proj7T0 proj7T1 proj7T2 proj7T3 proj7T4 proj7T5;
    }.
Arguments exist7T { T0 T1 T2 T3 T4 T5 T6} [ proj7T0 proj7T1 proj7T2 proj7T3 proj7T4 proj7T5].
Definition uncurry7 { T0 T1 T2 T3 T4 T5 T6} (R: rel7 T0 T1 T2 T3 T4 T5 T6): rel1 sig7T :=
  fun x => R (proj7T0 x) (proj7T1 x) (proj7T2 x) (proj7T3 x) (proj7T4 x) (proj7T5 x) (proj7T6 x).
Definition curry7 { T0 T1 T2 T3 T4 T5 T6} (R: rel1 sig7T): rel7 T0 T1 T2 T3 T4 T5 T6 :=
  fun x0 x1 x2 x3 x4 x5 x6 => R (exist7T x6).

Record sig8T { T0 T1 T2 T3 T4 T5 T6 T7} :=
  exist8T {
      proj8T0: @T0;
      proj8T1: @T1 proj8T0;
      proj8T2: @T2 proj8T0 proj8T1;
      proj8T3: @T3 proj8T0 proj8T1 proj8T2;
      proj8T4: @T4 proj8T0 proj8T1 proj8T2 proj8T3;
      proj8T5: @T5 proj8T0 proj8T1 proj8T2 proj8T3 proj8T4;
      proj8T6: @T6 proj8T0 proj8T1 proj8T2 proj8T3 proj8T4 proj8T5;
      proj8T7: @T7 proj8T0 proj8T1 proj8T2 proj8T3 proj8T4 proj8T5 proj8T6;
    }.
Arguments exist8T { T0 T1 T2 T3 T4 T5 T6 T7} [ proj8T0 proj8T1 proj8T2 proj8T3 proj8T4 proj8T5 proj8T6].
Definition uncurry8 { T0 T1 T2 T3 T4 T5 T6 T7} (R: rel8 T0 T1 T2 T3 T4 T5 T6 T7): rel1 sig8T :=
  fun x => R (proj8T0 x) (proj8T1 x) (proj8T2 x) (proj8T3 x) (proj8T4 x) (proj8T5 x) (proj8T6 x) (proj8T7 x).
Definition curry8 { T0 T1 T2 T3 T4 T5 T6 T7} (R: rel1 sig8T): rel8 T0 T1 T2 T3 T4 T5 T6 T7 :=
  fun x0 x1 x2 x3 x4 x5 x6 x7 => R (exist8T x7).

Record sig9T { T0 T1 T2 T3 T4 T5 T6 T7 T8} :=
  exist9T {
      proj9T0: @T0;
      proj9T1: @T1 proj9T0;
      proj9T2: @T2 proj9T0 proj9T1;
      proj9T3: @T3 proj9T0 proj9T1 proj9T2;
      proj9T4: @T4 proj9T0 proj9T1 proj9T2 proj9T3;
      proj9T5: @T5 proj9T0 proj9T1 proj9T2 proj9T3 proj9T4;
      proj9T6: @T6 proj9T0 proj9T1 proj9T2 proj9T3 proj9T4 proj9T5;
      proj9T7: @T7 proj9T0 proj9T1 proj9T2 proj9T3 proj9T4 proj9T5 proj9T6;
      proj9T8: @T8 proj9T0 proj9T1 proj9T2 proj9T3 proj9T4 proj9T5 proj9T6 proj9T7;
    }.
Arguments exist9T { T0 T1 T2 T3 T4 T5 T6 T7 T8} [ proj9T0 proj9T1 proj9T2 proj9T3 proj9T4 proj9T5 proj9T6 proj9T7].
Definition uncurry9 { T0 T1 T2 T3 T4 T5 T6 T7 T8} (R: rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8): rel1 sig9T :=
  fun x => R (proj9T0 x) (proj9T1 x) (proj9T2 x) (proj9T3 x) (proj9T4 x) (proj9T5 x) (proj9T6 x) (proj9T7 x) (proj9T8 x).
Definition curry9 { T0 T1 T2 T3 T4 T5 T6 T7 T8} (R: rel1 sig9T): rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8 :=
  fun x0 x1 x2 x3 x4 x5 x6 x7 x8 => R (exist9T x8).

Record sig10T { T0 T1 T2 T3 T4 T5 T6 T7 T8 T9} :=
  exist10T {
      proj10T0: @T0;
      proj10T1: @T1 proj10T0;
      proj10T2: @T2 proj10T0 proj10T1;
      proj10T3: @T3 proj10T0 proj10T1 proj10T2;
      proj10T4: @T4 proj10T0 proj10T1 proj10T2 proj10T3;
      proj10T5: @T5 proj10T0 proj10T1 proj10T2 proj10T3 proj10T4;
      proj10T6: @T6 proj10T0 proj10T1 proj10T2 proj10T3 proj10T4 proj10T5;
      proj10T7: @T7 proj10T0 proj10T1 proj10T2 proj10T3 proj10T4 proj10T5 proj10T6;
      proj10T8: @T8 proj10T0 proj10T1 proj10T2 proj10T3 proj10T4 proj10T5 proj10T6 proj10T7;
      proj10T9: @T9 proj10T0 proj10T1 proj10T2 proj10T3 proj10T4 proj10T5 proj10T6 proj10T7 proj10T8;
    }.
Arguments exist10T { T0 T1 T2 T3 T4 T5 T6 T7 T8 T9} [ proj10T0 proj10T1 proj10T2 proj10T3 proj10T4 proj10T5 proj10T6 proj10T7 proj10T8].
Definition uncurry10 { T0 T1 T2 T3 T4 T5 T6 T7 T8 T9} (R: rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9): rel1 sig10T :=
  fun x => R (proj10T0 x) (proj10T1 x) (proj10T2 x) (proj10T3 x) (proj10T4 x) (proj10T5 x) (proj10T6 x) (proj10T7 x) (proj10T8 x) (proj10T9 x).
Definition curry10 { T0 T1 T2 T3 T4 T5 T6 T7 T8 T9} (R: rel1 sig10T): rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 :=
  fun x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 => R (exist10T x9).

Record sig11T { T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10} :=
  exist11T {
      proj11T0: @T0;
      proj11T1: @T1 proj11T0;
      proj11T2: @T2 proj11T0 proj11T1;
      proj11T3: @T3 proj11T0 proj11T1 proj11T2;
      proj11T4: @T4 proj11T0 proj11T1 proj11T2 proj11T3;
      proj11T5: @T5 proj11T0 proj11T1 proj11T2 proj11T3 proj11T4;
      proj11T6: @T6 proj11T0 proj11T1 proj11T2 proj11T3 proj11T4 proj11T5;
      proj11T7: @T7 proj11T0 proj11T1 proj11T2 proj11T3 proj11T4 proj11T5 proj11T6;
      proj11T8: @T8 proj11T0 proj11T1 proj11T2 proj11T3 proj11T4 proj11T5 proj11T6 proj11T7;
      proj11T9: @T9 proj11T0 proj11T1 proj11T2 proj11T3 proj11T4 proj11T5 proj11T6 proj11T7 proj11T8;
      proj11T10: @T10 proj11T0 proj11T1 proj11T2 proj11T3 proj11T4 proj11T5 proj11T6 proj11T7 proj11T8 proj11T9;
    }.
Arguments exist11T { T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10} [ proj11T0 proj11T1 proj11T2 proj11T3 proj11T4 proj11T5 proj11T6 proj11T7 proj11T8 proj11T9].
Definition uncurry11 { T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10} (R: rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10): rel1 sig11T :=
  fun x => R (proj11T0 x) (proj11T1 x) (proj11T2 x) (proj11T3 x) (proj11T4 x) (proj11T5 x) (proj11T6 x) (proj11T7 x) (proj11T8 x) (proj11T9 x) (proj11T10 x).
Definition curry11 { T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10} (R: rel1 sig11T): rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 :=
  fun x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 => R (exist11T x10).

Record sig12T { T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11} :=
  exist12T {
      proj12T0: @T0;
      proj12T1: @T1 proj12T0;
      proj12T2: @T2 proj12T0 proj12T1;
      proj12T3: @T3 proj12T0 proj12T1 proj12T2;
      proj12T4: @T4 proj12T0 proj12T1 proj12T2 proj12T3;
      proj12T5: @T5 proj12T0 proj12T1 proj12T2 proj12T3 proj12T4;
      proj12T6: @T6 proj12T0 proj12T1 proj12T2 proj12T3 proj12T4 proj12T5;
      proj12T7: @T7 proj12T0 proj12T1 proj12T2 proj12T3 proj12T4 proj12T5 proj12T6;
      proj12T8: @T8 proj12T0 proj12T1 proj12T2 proj12T3 proj12T4 proj12T5 proj12T6 proj12T7;
      proj12T9: @T9 proj12T0 proj12T1 proj12T2 proj12T3 proj12T4 proj12T5 proj12T6 proj12T7 proj12T8;
      proj12T10: @T10 proj12T0 proj12T1 proj12T2 proj12T3 proj12T4 proj12T5 proj12T6 proj12T7 proj12T8 proj12T9;
      proj12T11: @T11 proj12T0 proj12T1 proj12T2 proj12T3 proj12T4 proj12T5 proj12T6 proj12T7 proj12T8 proj12T9 proj12T10;
    }.
Arguments exist12T { T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11} [ proj12T0 proj12T1 proj12T2 proj12T3 proj12T4 proj12T5 proj12T6 proj12T7 proj12T8 proj12T9 proj12T10].
Definition uncurry12 { T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11} (R: rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11): rel1 sig12T :=
  fun x => R (proj12T0 x) (proj12T1 x) (proj12T2 x) (proj12T3 x) (proj12T4 x) (proj12T5 x) (proj12T6 x) (proj12T7 x) (proj12T8 x) (proj12T9 x) (proj12T10 x) (proj12T11 x).
Definition curry12 { T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11} (R: rel1 sig12T): rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 :=
  fun x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 => R (exist12T x11).

Record sig13T { T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12} :=
  exist13T {
      proj13T0: @T0;
      proj13T1: @T1 proj13T0;
      proj13T2: @T2 proj13T0 proj13T1;
      proj13T3: @T3 proj13T0 proj13T1 proj13T2;
      proj13T4: @T4 proj13T0 proj13T1 proj13T2 proj13T3;
      proj13T5: @T5 proj13T0 proj13T1 proj13T2 proj13T3 proj13T4;
      proj13T6: @T6 proj13T0 proj13T1 proj13T2 proj13T3 proj13T4 proj13T5;
      proj13T7: @T7 proj13T0 proj13T1 proj13T2 proj13T3 proj13T4 proj13T5 proj13T6;
      proj13T8: @T8 proj13T0 proj13T1 proj13T2 proj13T3 proj13T4 proj13T5 proj13T6 proj13T7;
      proj13T9: @T9 proj13T0 proj13T1 proj13T2 proj13T3 proj13T4 proj13T5 proj13T6 proj13T7 proj13T8;
      proj13T10: @T10 proj13T0 proj13T1 proj13T2 proj13T3 proj13T4 proj13T5 proj13T6 proj13T7 proj13T8 proj13T9;
      proj13T11: @T11 proj13T0 proj13T1 proj13T2 proj13T3 proj13T4 proj13T5 proj13T6 proj13T7 proj13T8 proj13T9 proj13T10;
      proj13T12: @T12 proj13T0 proj13T1 proj13T2 proj13T3 proj13T4 proj13T5 proj13T6 proj13T7 proj13T8 proj13T9 proj13T10 proj13T11;
    }.
Arguments exist13T { T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12} [ proj13T0 proj13T1 proj13T2 proj13T3 proj13T4 proj13T5 proj13T6 proj13T7 proj13T8 proj13T9 proj13T10 proj13T11].
Definition uncurry13 { T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12} (R: rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12): rel1 sig13T :=
  fun x => R (proj13T0 x) (proj13T1 x) (proj13T2 x) (proj13T3 x) (proj13T4 x) (proj13T5 x) (proj13T6 x) (proj13T7 x) (proj13T8 x) (proj13T9 x) (proj13T10 x) (proj13T11 x) (proj13T12 x).
Definition curry13 { T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12} (R: rel1 sig13T): rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 :=
  fun x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 => R (exist13T x12).

Record sig14T { T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13} :=
  exist14T {
      proj14T0: @T0;
      proj14T1: @T1 proj14T0;
      proj14T2: @T2 proj14T0 proj14T1;
      proj14T3: @T3 proj14T0 proj14T1 proj14T2;
      proj14T4: @T4 proj14T0 proj14T1 proj14T2 proj14T3;
      proj14T5: @T5 proj14T0 proj14T1 proj14T2 proj14T3 proj14T4;
      proj14T6: @T6 proj14T0 proj14T1 proj14T2 proj14T3 proj14T4 proj14T5;
      proj14T7: @T7 proj14T0 proj14T1 proj14T2 proj14T3 proj14T4 proj14T5 proj14T6;
      proj14T8: @T8 proj14T0 proj14T1 proj14T2 proj14T3 proj14T4 proj14T5 proj14T6 proj14T7;
      proj14T9: @T9 proj14T0 proj14T1 proj14T2 proj14T3 proj14T4 proj14T5 proj14T6 proj14T7 proj14T8;
      proj14T10: @T10 proj14T0 proj14T1 proj14T2 proj14T3 proj14T4 proj14T5 proj14T6 proj14T7 proj14T8 proj14T9;
      proj14T11: @T11 proj14T0 proj14T1 proj14T2 proj14T3 proj14T4 proj14T5 proj14T6 proj14T7 proj14T8 proj14T9 proj14T10;
      proj14T12: @T12 proj14T0 proj14T1 proj14T2 proj14T3 proj14T4 proj14T5 proj14T6 proj14T7 proj14T8 proj14T9 proj14T10 proj14T11;
      proj14T13: @T13 proj14T0 proj14T1 proj14T2 proj14T3 proj14T4 proj14T5 proj14T6 proj14T7 proj14T8 proj14T9 proj14T10 proj14T11 proj14T12;
    }.
Arguments exist14T { T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13} [ proj14T0 proj14T1 proj14T2 proj14T3 proj14T4 proj14T5 proj14T6 proj14T7 proj14T8 proj14T9 proj14T10 proj14T11 proj14T12].
Definition uncurry14 { T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13} (R: rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13): rel1 sig14T :=
  fun x => R (proj14T0 x) (proj14T1 x) (proj14T2 x) (proj14T3 x) (proj14T4 x) (proj14T5 x) (proj14T6 x) (proj14T7 x) (proj14T8 x) (proj14T9 x) (proj14T10 x) (proj14T11 x) (proj14T12 x) (proj14T13 x).
Definition curry14 { T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13} (R: rel1 sig14T): rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 :=
  fun x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 => R (exist14T x13).

Record sig15T { T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14} :=
  exist15T {
      proj15T0: @T0;
      proj15T1: @T1 proj15T0;
      proj15T2: @T2 proj15T0 proj15T1;
      proj15T3: @T3 proj15T0 proj15T1 proj15T2;
      proj15T4: @T4 proj15T0 proj15T1 proj15T2 proj15T3;
      proj15T5: @T5 proj15T0 proj15T1 proj15T2 proj15T3 proj15T4;
      proj15T6: @T6 proj15T0 proj15T1 proj15T2 proj15T3 proj15T4 proj15T5;
      proj15T7: @T7 proj15T0 proj15T1 proj15T2 proj15T3 proj15T4 proj15T5 proj15T6;
      proj15T8: @T8 proj15T0 proj15T1 proj15T2 proj15T3 proj15T4 proj15T5 proj15T6 proj15T7;
      proj15T9: @T9 proj15T0 proj15T1 proj15T2 proj15T3 proj15T4 proj15T5 proj15T6 proj15T7 proj15T8;
      proj15T10: @T10 proj15T0 proj15T1 proj15T2 proj15T3 proj15T4 proj15T5 proj15T6 proj15T7 proj15T8 proj15T9;
      proj15T11: @T11 proj15T0 proj15T1 proj15T2 proj15T3 proj15T4 proj15T5 proj15T6 proj15T7 proj15T8 proj15T9 proj15T10;
      proj15T12: @T12 proj15T0 proj15T1 proj15T2 proj15T3 proj15T4 proj15T5 proj15T6 proj15T7 proj15T8 proj15T9 proj15T10 proj15T11;
      proj15T13: @T13 proj15T0 proj15T1 proj15T2 proj15T3 proj15T4 proj15T5 proj15T6 proj15T7 proj15T8 proj15T9 proj15T10 proj15T11 proj15T12;
      proj15T14: @T14 proj15T0 proj15T1 proj15T2 proj15T3 proj15T4 proj15T5 proj15T6 proj15T7 proj15T8 proj15T9 proj15T10 proj15T11 proj15T12 proj15T13;
    }.
Arguments exist15T { T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14} [ proj15T0 proj15T1 proj15T2 proj15T3 proj15T4 proj15T5 proj15T6 proj15T7 proj15T8 proj15T9 proj15T10 proj15T11 proj15T12 proj15T13].
Definition uncurry15 { T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14} (R: rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14): rel1 sig15T :=
  fun x => R (proj15T0 x) (proj15T1 x) (proj15T2 x) (proj15T3 x) (proj15T4 x) (proj15T5 x) (proj15T6 x) (proj15T7 x) (proj15T8 x) (proj15T9 x) (proj15T10 x) (proj15T11 x) (proj15T12 x) (proj15T13 x) (proj15T14 x).
Definition curry15 { T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14} (R: rel1 sig15T): rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 :=
  fun x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 => R (exist15T x14).

Record sig16T { T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15} :=
  exist16T {
      proj16T0: @T0;
      proj16T1: @T1 proj16T0;
      proj16T2: @T2 proj16T0 proj16T1;
      proj16T3: @T3 proj16T0 proj16T1 proj16T2;
      proj16T4: @T4 proj16T0 proj16T1 proj16T2 proj16T3;
      proj16T5: @T5 proj16T0 proj16T1 proj16T2 proj16T3 proj16T4;
      proj16T6: @T6 proj16T0 proj16T1 proj16T2 proj16T3 proj16T4 proj16T5;
      proj16T7: @T7 proj16T0 proj16T1 proj16T2 proj16T3 proj16T4 proj16T5 proj16T6;
      proj16T8: @T8 proj16T0 proj16T1 proj16T2 proj16T3 proj16T4 proj16T5 proj16T6 proj16T7;
      proj16T9: @T9 proj16T0 proj16T1 proj16T2 proj16T3 proj16T4 proj16T5 proj16T6 proj16T7 proj16T8;
      proj16T10: @T10 proj16T0 proj16T1 proj16T2 proj16T3 proj16T4 proj16T5 proj16T6 proj16T7 proj16T8 proj16T9;
      proj16T11: @T11 proj16T0 proj16T1 proj16T2 proj16T3 proj16T4 proj16T5 proj16T6 proj16T7 proj16T8 proj16T9 proj16T10;
      proj16T12: @T12 proj16T0 proj16T1 proj16T2 proj16T3 proj16T4 proj16T5 proj16T6 proj16T7 proj16T8 proj16T9 proj16T10 proj16T11;
      proj16T13: @T13 proj16T0 proj16T1 proj16T2 proj16T3 proj16T4 proj16T5 proj16T6 proj16T7 proj16T8 proj16T9 proj16T10 proj16T11 proj16T12;
      proj16T14: @T14 proj16T0 proj16T1 proj16T2 proj16T3 proj16T4 proj16T5 proj16T6 proj16T7 proj16T8 proj16T9 proj16T10 proj16T11 proj16T12 proj16T13;
      proj16T15: @T15 proj16T0 proj16T1 proj16T2 proj16T3 proj16T4 proj16T5 proj16T6 proj16T7 proj16T8 proj16T9 proj16T10 proj16T11 proj16T12 proj16T13 proj16T14;
    }.
Arguments exist16T { T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15} [ proj16T0 proj16T1 proj16T2 proj16T3 proj16T4 proj16T5 proj16T6 proj16T7 proj16T8 proj16T9 proj16T10 proj16T11 proj16T12 proj16T13 proj16T14].
Definition uncurry16 { T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15} (R: rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15): rel1 sig16T :=
  fun x => R (proj16T0 x) (proj16T1 x) (proj16T2 x) (proj16T3 x) (proj16T4 x) (proj16T5 x) (proj16T6 x) (proj16T7 x) (proj16T8 x) (proj16T9 x) (proj16T10 x) (proj16T11 x) (proj16T12 x) (proj16T13 x) (proj16T14 x) (proj16T15 x).
Definition curry16 { T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15} (R: rel1 sig16T): rel16 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 :=
  fun x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 => R (exist16T x15).

(** ** Bottom *)

Definition pacoid {A : Type} (a: A) : A := a.

Notation bot0 :=
  (pacoid(curry0(fun _ => False))).

Notation bot1 :=
  (pacoid(curry1(fun _ => False))).

Notation bot2 :=
  (pacoid(curry2(fun _ => False))).

Notation bot3 :=
  (pacoid(curry3(fun _ => False))).

Notation bot4 :=
  (pacoid(curry4(fun _ => False))).

Notation bot5 :=
  (pacoid(curry5(fun _ => False))).

Notation bot6 :=
  (pacoid(curry6(fun _ => False))).

Notation bot7 :=
  (pacoid(curry7(fun _ => False))).

Notation bot8 :=
  (pacoid(curry8(fun _ => False))).

Notation bot9 :=
  (pacoid(curry9(fun _ => False))).

Notation bot10 :=
  (pacoid(curry10(fun _ => False))).

Notation bot11 :=
  (pacoid(curry11(fun _ => False))).

Notation bot12 :=
  (pacoid(curry12(fun _ => False))).

Notation bot13 :=
  (pacoid(curry13(fun _ => False))).

Notation bot14 :=
  (pacoid(curry14(fun _ => False))).

Notation bot15 :=
  (pacoid(curry15(fun _ => False))).

Notation bot16 :=
  (pacoid(curry16(fun _ => False))).

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

Notation "p <10= q" :=
  (forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 (PR: p x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Prop), q x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Prop)
  (at level 50, no associativity).

Notation "p <11= q" :=
  (forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (PR: p x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : Prop), q x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : Prop)
  (at level 50, no associativity).

Notation "p <12= q" :=
  (forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 (PR: p x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Prop), q x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Prop)
  (at level 50, no associativity).

Notation "p <13= q" :=
  (forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 (PR: p x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : Prop), q x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : Prop)
  (at level 50, no associativity).

Notation "p <14= q" :=
  (forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 (PR: p x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : Prop), q x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : Prop)
  (at level 50, no associativity).

Notation "p <15= q" :=
  (forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 (PR: p x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : Prop), q x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : Prop)
  (at level 50, no associativity).

Notation "p <16= q" :=
  (forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 (PR: p x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : Prop), q x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : Prop)
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

Notation "p \10/ q" :=
  (fun x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 => p x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 \/ q x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)
  (at level 50, no associativity).

Notation "p \11/ q" :=
  (fun x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 => p x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 \/ q x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
  (at level 50, no associativity).

Notation "p \12/ q" :=
  (fun x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 => p x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 \/ q x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)
  (at level 50, no associativity).

Notation "p \13/ q" :=
  (fun x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 => p x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 \/ q x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)
  (at level 50, no associativity).

Notation "p \14/ q" :=
  (fun x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 => p x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 \/ q x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13)
  (at level 50, no associativity).

Notation "p \15/ q" :=
  (fun x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 => p x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 \/ q x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14)
  (at level 50, no associativity).

Notation "p \16/ q" :=
  (fun x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 => p x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 \/ q x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15)
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

Notation "p /10\ q" :=
  (fun x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 => p x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 /\ q x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)
  (at level 50, no associativity).

Notation "p /11\ q" :=
  (fun x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 => p x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 /\ q x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
  (at level 50, no associativity).

Notation "p /12\ q" :=
  (fun x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 => p x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 /\ q x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)
  (at level 50, no associativity).

Notation "p /13\ q" :=
  (fun x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 => p x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 /\ q x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)
  (at level 50, no associativity).

Notation "p /14\ q" :=
  (fun x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 => p x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 /\ q x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13)
  (at level 50, no associativity).

Notation "p /15\ q" :=
  (fun x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 => p x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 /\ q x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14)
  (at level 50, no associativity).

Notation "p /16\ q" :=
  (fun x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 => p x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 /\ q x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15)
  (at level 50, no associativity).

