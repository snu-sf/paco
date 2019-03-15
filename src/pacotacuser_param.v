Require Import pacoall.

(** ** gcpn_fold
*)

Ltac gcpn_fold :=
  match goal with 
  | [|- ?gf (cpn0 _ ?r)] => change (gf (cpn0 gf r)) with (gcpn0 gf r)
  | [|- ?gf (cpn1 _ ?r) _] => change (gf (cpn1 gf r)) with (gcpn1 gf r)
  | [|- ?gf (cpn2 _ ?r) _ _] => change (gf (cpn2 gf r)) with (gcpn2 gf r)
  | [|- ?gf (cpn3 _ ?r) _ _ _] => change (gf (cpn3 gf r)) with (gcpn3 gf r)
  | [|- ?gf (cpn4 _ ?r) _ _ _ _] => change (gf (cpn4 gf r)) with (gcpn4 gf r)
  | [|- ?gf (cpn5 _ ?r) _ _ _ _ _] => change (gf (cpn5 gf r)) with (gcpn5 gf r)
  | [|- ?gf (cpn6 _ ?r) _ _ _ _ _ _] => change (gf (cpn6 gf r)) with (gcpn6 gf r)
  | [|- ?gf (cpn7 _ ?r) _ _ _ _ _ _ _] => change (gf (cpn7 gf r)) with (gcpn7 gf r)
  | [|- ?gf (cpn8 _ ?r) _ _ _ _ _ _ _ _] => change (gf (cpn8 gf r)) with (gcpn8 gf r)
  | [|- ?gf (cpn9 _ ?r) _ _ _ _ _ _ _ _ _] => change (gf (cpn9 gf r)) with (gcpn9 gf r)
  | [|- ?gf (cpn10 _ ?r) _ _ _ _ _ _ _ _ _ _] => change (gf (cpn10 gf r)) with (gcpn10 gf r)
  | [|- ?gf (cpn11 _ ?r) _ _ _ _ _ _ _ _ _ _ _] => change (gf (cpn11 gf r)) with (gcpn11 gf r)
  | [|- ?gf (cpn12 _ ?r) _ _ _ _ _ _ _ _ _ _ _ _] => change (gf (cpn12 gf r)) with (gcpn12 gf r)
  | [|- ?gf (cpn13 _ ?r) _ _ _ _ _ _ _ _ _ _ _ _ _] => change (gf (cpn13 gf r)) with (gcpn13 gf r)
  | [|- ?gf (cpn14 _ ?r) _ _ _ _ _ _ _ _ _ _ _ _ _ _] => change (gf (cpn14 gf r)) with (gcpn14 gf r)
  | [|- ?gf (cpn15 _ ?r) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _] => change (gf (cpn15 gf r)) with (gcpn15 gf r)
  | [|- ?gf (cpn16 _ ?r) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _] => change (gf (cpn16 gf r)) with (gcpn16 gf r)
  | [|- ?gf (cpn17 _ ?r) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _] => change (gf (cpn17 gf r)) with (gcpn17 gf r)
  | [|- ?gf (cpn18 _ ?r) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _] => change (gf (cpn18 gf r)) with (gcpn18 gf r)
  end.

(** ** ucompat
*)

Ltac ucompat :=
  match goal with 
  | [|- context[cpn0]] => eapply wcompat0_sound; eauto with paco
  | [|- context[cpn1]] => eapply wcompat1_sound; eauto with paco
  | [|- context[cpn2]] => eapply wcompat2_sound; eauto with paco
  | [|- context[cpn3]] => eapply wcompat3_sound; eauto with paco
  | [|- context[cpn4]] => eapply wcompat4_sound; eauto with paco
  | [|- context[cpn5]] => eapply wcompat5_sound; eauto with paco
  | [|- context[cpn6]] => eapply wcompat6_sound; eauto with paco
  | [|- context[cpn7]] => eapply wcompat7_sound; eauto with paco
  | [|- context[cpn8]] => eapply wcompat8_sound; eauto with paco
  | [|- context[cpn9]] => eapply wcompat9_sound; eauto with paco
  | [|- context[cpn10]] => eapply wcompat10_sound; eauto with paco
  | [|- context[cpn11]] => eapply wcompat11_sound; eauto with paco
  | [|- context[cpn12]] => eapply wcompat12_sound; eauto with paco
  | [|- context[cpn13]] => eapply wcompat13_sound; eauto with paco
  | [|- context[cpn14]] => eapply wcompat14_sound; eauto with paco
  | [|- context[cpn15]] => eapply wcompat15_sound; eauto with paco
  | [|- context[cpn16]] => eapply wcompat16_sound; eauto with paco
  | [|- context[cpn17]] => eapply wcompat17_sound; eauto with paco
  | [|- context[cpn18]] => eapply wcompat18_sound; eauto with paco
  end.

(** ** uinit
*)

Ltac uinit :=
  repeat red;
  match goal with 
  | [|- context[paco0]] => under_forall ltac:(eapply cpn0_init; [eauto with paco|])
  | [|- context[paco1]] => under_forall ltac:(eapply cpn1_init; [eauto with paco|])
  | [|- context[paco2]] => under_forall ltac:(eapply cpn2_init; [eauto with paco|])
  | [|- context[paco3]] => under_forall ltac:(eapply cpn3_init; [eauto with paco|])
  | [|- context[paco4]] => under_forall ltac:(eapply cpn4_init; [eauto with paco|])
  | [|- context[paco5]] => under_forall ltac:(eapply cpn5_init; [eauto with paco|])
  | [|- context[paco6]] => under_forall ltac:(eapply cpn6_init; [eauto with paco|])
  | [|- context[paco7]] => under_forall ltac:(eapply cpn7_init; [eauto with paco|])
  | [|- context[paco8]] => under_forall ltac:(eapply cpn8_init; [eauto with paco|])
  | [|- context[paco9]] => under_forall ltac:(eapply cpn9_init; [eauto with paco|])
  | [|- context[paco10]] => under_forall ltac:(eapply cpn10_init; [eauto with paco|])
  | [|- context[paco11]] => under_forall ltac:(eapply cpn11_init; [eauto with paco|])
  | [|- context[paco12]] => under_forall ltac:(eapply cpn12_init; [eauto with paco|])
  | [|- context[paco13]] => under_forall ltac:(eapply cpn13_init; [eauto with paco|])
  | [|- context[paco14]] => under_forall ltac:(eapply cpn14_init; [eauto with paco|])
  | [|- context[paco15]] => under_forall ltac:(eapply cpn15_init; [eauto with paco|])
  | [|- context[paco16]] => under_forall ltac:(eapply cpn16_init; [eauto with paco|])
  | [|- context[paco17]] => under_forall ltac:(eapply cpn17_init; [eauto with paco|])
  | [|- context[paco18]] => under_forall ltac:(eapply cpn18_init; [eauto with paco|])
  end.

(** ** ustep
*)

Ltac ustep :=
  match goal with 
  | [|- context[cpn0]] => under_forall ltac:(eapply cpn0_step; [eauto with paco|])
  | [|- context[cpn1]] => under_forall ltac:(eapply cpn1_step; [eauto with paco|])
  | [|- context[cpn2]] => under_forall ltac:(eapply cpn2_step; [eauto with paco|])
  | [|- context[cpn3]] => under_forall ltac:(eapply cpn3_step; [eauto with paco|])
  | [|- context[cpn4]] => under_forall ltac:(eapply cpn4_step; [eauto with paco|])
  | [|- context[cpn5]] => under_forall ltac:(eapply cpn5_step; [eauto with paco|])
  | [|- context[cpn6]] => under_forall ltac:(eapply cpn6_step; [eauto with paco|])
  | [|- context[cpn7]] => under_forall ltac:(eapply cpn7_step; [eauto with paco|])
  | [|- context[cpn8]] => under_forall ltac:(eapply cpn8_step; [eauto with paco|])
  | [|- context[cpn9]] => under_forall ltac:(eapply cpn9_step; [eauto with paco|])
  | [|- context[cpn10]] => under_forall ltac:(eapply cpn10_step; [eauto with paco|])
  | [|- context[cpn11]] => under_forall ltac:(eapply cpn11_step; [eauto with paco|])
  | [|- context[cpn12]] => under_forall ltac:(eapply cpn12_step; [eauto with paco|])
  | [|- context[cpn13]] => under_forall ltac:(eapply cpn13_step; [eauto with paco|])
  | [|- context[cpn14]] => under_forall ltac:(eapply cpn14_step; [eauto with paco|])
  | [|- context[cpn15]] => under_forall ltac:(eapply cpn15_step; [eauto with paco|])
  | [|- context[cpn16]] => under_forall ltac:(eapply cpn16_step; [eauto with paco|])
  | [|- context[cpn17]] => under_forall ltac:(eapply cpn17_step; [eauto with paco|])
  | [|- context[cpn18]] => under_forall ltac:(eapply cpn18_step; [eauto with paco|])
  end.

(** ** uclo H
*)

Ltac uclo H :=
  match goal with 
  | [|- context[cpn0]]  => under_forall ltac:(eapply cpn0_clo; [|eapply H|]; [eauto with paco|])
  | [|- context[gcpn0]] => under_forall ltac:(eapply gcpn0_clo; [|eapply H|]; [eauto with paco|])
  | [|- context[cpn1]]  => under_forall ltac:(eapply cpn1_clo; [|eapply H|]; [eauto with paco|])
  | [|- context[gcpn1]] => under_forall ltac:(eapply gcpn1_clo; [|eapply H|]; [eauto with paco|])
  | [|- context[cpn2]]  => under_forall ltac:(eapply cpn2_clo; [|eapply H|]; [eauto with paco|])
  | [|- context[gcpn2]] => under_forall ltac:(eapply gcpn2_clo; [|eapply H|]; [eauto with paco|])
  | [|- context[cpn3]]  => under_forall ltac:(eapply cpn3_clo; [|eapply H|]; [eauto with paco|])
  | [|- context[gcpn3]] => under_forall ltac:(eapply gcpn3_clo; [|eapply H|]; [eauto with paco|])
  | [|- context[cpn4]]  => under_forall ltac:(eapply cpn4_clo; [|eapply H|]; [eauto with paco|])
  | [|- context[gcpn4]] => under_forall ltac:(eapply gcpn4_clo; [|eapply H|]; [eauto with paco|])
  | [|- context[cpn5]]  => under_forall ltac:(eapply cpn5_clo; [|eapply H|]; [eauto with paco|])
  | [|- context[gcpn5]] => under_forall ltac:(eapply gcpn5_clo; [|eapply H|]; [eauto with paco|])
  | [|- context[cpn6]]  => under_forall ltac:(eapply cpn6_clo; [|eapply H|]; [eauto with paco|])
  | [|- context[gcpn6]] => under_forall ltac:(eapply gcpn6_clo; [|eapply H|]; [eauto with paco|])
  | [|- context[cpn7]]  => under_forall ltac:(eapply cpn7_clo; [|eapply H|]; [eauto with paco|])
  | [|- context[gcpn7]] => under_forall ltac:(eapply gcpn7_clo; [|eapply H|]; [eauto with paco|])
  | [|- context[cpn8]]  => under_forall ltac:(eapply cpn8_clo; [|eapply H|]; [eauto with paco|])
  | [|- context[gcpn8]] => under_forall ltac:(eapply gcpn8_clo; [|eapply H|]; [eauto with paco|])
  | [|- context[cpn9]]  => under_forall ltac:(eapply cpn9_clo; [|eapply H|]; [eauto with paco|])
  | [|- context[gcpn9]] => under_forall ltac:(eapply gcpn9_clo; [|eapply H|]; [eauto with paco|])
  | [|- context[cpn10]]  => under_forall ltac:(eapply cpn10_clo; [|eapply H|]; [eauto with paco|])
  | [|- context[gcpn10]] => under_forall ltac:(eapply gcpn10_clo; [|eapply H|]; [eauto with paco|])
  | [|- context[cpn11]]  => under_forall ltac:(eapply cpn11_clo; [|eapply H|]; [eauto with paco|])
  | [|- context[gcpn11]] => under_forall ltac:(eapply gcpn11_clo; [|eapply H|]; [eauto with paco|])
  | [|- context[cpn12]]  => under_forall ltac:(eapply cpn12_clo; [|eapply H|]; [eauto with paco|])
  | [|- context[gcpn12]] => under_forall ltac:(eapply gcpn12_clo; [|eapply H|]; [eauto with paco|])
  | [|- context[cpn13]]  => under_forall ltac:(eapply cpn13_clo; [|eapply H|]; [eauto with paco|])
  | [|- context[gcpn13]] => under_forall ltac:(eapply gcpn13_clo; [|eapply H|]; [eauto with paco|])
  | [|- context[cpn14]]  => under_forall ltac:(eapply cpn14_clo; [|eapply H|]; [eauto with paco|])
  | [|- context[gcpn14]] => under_forall ltac:(eapply gcpn14_clo; [|eapply H|]; [eauto with paco|])
  | [|- context[cpn15]]  => under_forall ltac:(eapply cpn15_clo; [|eapply H|]; [eauto with paco|])
  | [|- context[gcpn15]] => under_forall ltac:(eapply gcpn15_clo; [|eapply H|]; [eauto with paco|])
  | [|- context[cpn16]]  => under_forall ltac:(eapply cpn16_clo; [|eapply H|]; [eauto with paco|])
  | [|- context[gcpn16]] => under_forall ltac:(eapply gcpn16_clo; [|eapply H|]; [eauto with paco|])
  | [|- context[cpn17]]  => under_forall ltac:(eapply cpn17_clo; [|eapply H|]; [eauto with paco|])
  | [|- context[gcpn17]] => under_forall ltac:(eapply gcpn17_clo; [|eapply H|]; [eauto with paco|])
  | [|- context[cpn18]]  => under_forall ltac:(eapply cpn18_clo; [|eapply H|]; [eauto with paco|])
  | [|- context[gcpn18]] => under_forall ltac:(eapply gcpn18_clo; [|eapply H|]; [eauto with paco|])
  end.

(** ** ufinal
*)

Ltac ufinal :=
  match goal with 
  | [|- context[cpn0]]  => under_forall ltac:(eapply cpn0_final; [eauto with paco|])
  | [|- context[gcpn0]] => under_forall ltac:(eapply gcpn0_final; [eauto with paco|])
  | [|- context[cpn1]]  => under_forall ltac:(eapply cpn1_final; [eauto with paco|])
  | [|- context[gcpn1]] => under_forall ltac:(eapply gcpn1_final; [eauto with paco|])
  | [|- context[cpn2]]  => under_forall ltac:(eapply cpn2_final; [eauto with paco|])
  | [|- context[gcpn2]] => under_forall ltac:(eapply gcpn2_final; [eauto with paco|])
  | [|- context[cpn3]]  => under_forall ltac:(eapply cpn3_final; [eauto with paco|])
  | [|- context[gcpn3]] => under_forall ltac:(eapply gcpn3_final; [eauto with paco|])
  | [|- context[cpn4]]  => under_forall ltac:(eapply cpn4_final; [eauto with paco|])
  | [|- context[gcpn4]] => under_forall ltac:(eapply gcpn4_final; [eauto with paco|])
  | [|- context[cpn5]]  => under_forall ltac:(eapply cpn5_final; [eauto with paco|])
  | [|- context[gcpn5]] => under_forall ltac:(eapply gcpn5_final; [eauto with paco|])
  | [|- context[cpn6]]  => under_forall ltac:(eapply cpn6_final; [eauto with paco|])
  | [|- context[gcpn6]] => under_forall ltac:(eapply gcpn6_final; [eauto with paco|])
  | [|- context[cpn7]]  => under_forall ltac:(eapply cpn7_final; [eauto with paco|])
  | [|- context[gcpn7]] => under_forall ltac:(eapply gcpn7_final; [eauto with paco|])
  | [|- context[cpn8]]  => under_forall ltac:(eapply cpn8_final; [eauto with paco|])
  | [|- context[gcpn8]] => under_forall ltac:(eapply gcpn8_final; [eauto with paco|])
  | [|- context[cpn9]]  => under_forall ltac:(eapply cpn9_final; [eauto with paco|])
  | [|- context[gcpn9]] => under_forall ltac:(eapply gcpn9_final; [eauto with paco|])
  | [|- context[cpn10]]  => under_forall ltac:(eapply cpn10_final; [eauto with paco|])
  | [|- context[gcpn10]] => under_forall ltac:(eapply gcpn10_final; [eauto with paco|])
  | [|- context[cpn11]]  => under_forall ltac:(eapply cpn11_final; [eauto with paco|])
  | [|- context[gcpn11]] => under_forall ltac:(eapply gcpn11_final; [eauto with paco|])
  | [|- context[cpn12]]  => under_forall ltac:(eapply cpn12_final; [eauto with paco|])
  | [|- context[gcpn12]] => under_forall ltac:(eapply gcpn12_final; [eauto with paco|])
  | [|- context[cpn13]]  => under_forall ltac:(eapply cpn13_final; [eauto with paco|])
  | [|- context[gcpn13]] => under_forall ltac:(eapply gcpn13_final; [eauto with paco|])
  | [|- context[cpn14]]  => under_forall ltac:(eapply cpn14_final; [eauto with paco|])
  | [|- context[gcpn14]] => under_forall ltac:(eapply gcpn14_final; [eauto with paco|])
  | [|- context[cpn15]]  => under_forall ltac:(eapply cpn15_final; [eauto with paco|])
  | [|- context[gcpn15]] => under_forall ltac:(eapply gcpn15_final; [eauto with paco|])
  | [|- context[cpn16]]  => under_forall ltac:(eapply cpn16_final; [eauto with paco|])
  | [|- context[gcpn16]] => under_forall ltac:(eapply gcpn16_final; [eauto with paco|])
  | [|- context[cpn17]]  => under_forall ltac:(eapply cpn17_final; [eauto with paco|])
  | [|- context[gcpn17]] => under_forall ltac:(eapply gcpn17_final; [eauto with paco|])
  | [|- context[cpn18]]  => under_forall ltac:(eapply cpn18_final; [eauto with paco|])
  | [|- context[gcpn18]] => under_forall ltac:(eapply gcpn18_final; [eauto with paco|])
  end.

(** ** ucofix CIH
*)

Ltac ucofix CIH :=
  match goal with 
  | [|- context[cpn0]]  =>
    under_forall ltac:(eapply cpn0_from_paco; [eauto with paco|]);
    pcofix CIH;
    under_forall ltac:(eapply gcpn0_to_paco; [eauto with paco|])
  | [|- context[gcpn0]] =>
    under_forall ltac:(eapply gcpn0_from_paco; [eauto with paco|]);
    pcofix CIH;
    under_forall ltac:(eapply gcpn0_to_paco; [eauto with paco|])
  | [|- context[cpn1]]  =>
    under_forall ltac:(eapply cpn1_from_paco; [eauto with paco|]);
    pcofix CIH;
    under_forall ltac:(eapply gcpn1_to_paco; [eauto with paco|])
  | [|- context[gcpn1]] =>
    under_forall ltac:(eapply gcpn1_from_paco; [eauto with paco|]);
    pcofix CIH;
    under_forall ltac:(eapply gcpn1_to_paco; [eauto with paco|])
  | [|- context[cpn2]]  =>
    under_forall ltac:(eapply cpn2_from_paco; [eauto with paco|]);
    pcofix CIH;
    under_forall ltac:(eapply gcpn2_to_paco; [eauto with paco|])
  | [|- context[gcpn2]] =>
    under_forall ltac:(eapply gcpn2_from_paco; [eauto with paco|]);
    pcofix CIH;
    under_forall ltac:(eapply gcpn2_to_paco; [eauto with paco|])
  | [|- context[cpn3]]  =>
    under_forall ltac:(eapply cpn3_from_paco; [eauto with paco|]);
    pcofix CIH;
    under_forall ltac:(eapply gcpn3_to_paco; [eauto with paco|])
  | [|- context[gcpn3]] =>
    under_forall ltac:(eapply gcpn3_from_paco; [eauto with paco|]);
    pcofix CIH;
    under_forall ltac:(eapply gcpn3_to_paco; [eauto with paco|])
  | [|- context[cpn4]]  =>
    under_forall ltac:(eapply cpn4_from_paco; [eauto with paco|]);
    pcofix CIH;
    under_forall ltac:(eapply gcpn4_to_paco; [eauto with paco|])
  | [|- context[gcpn4]] =>
    under_forall ltac:(eapply gcpn4_from_paco; [eauto with paco|]);
    pcofix CIH;
    under_forall ltac:(eapply gcpn4_to_paco; [eauto with paco|])
  | [|- context[cpn5]]  =>
    under_forall ltac:(eapply cpn5_from_paco; [eauto with paco|]);
    pcofix CIH;
    under_forall ltac:(eapply gcpn5_to_paco; [eauto with paco|])
  | [|- context[gcpn5]] =>
    under_forall ltac:(eapply gcpn5_from_paco; [eauto with paco|]);
    pcofix CIH;
    under_forall ltac:(eapply gcpn5_to_paco; [eauto with paco|])
  | [|- context[cpn6]]  =>
    under_forall ltac:(eapply cpn6_from_paco; [eauto with paco|]);
    pcofix CIH;
    under_forall ltac:(eapply gcpn6_to_paco; [eauto with paco|])
  | [|- context[gcpn6]] =>
    under_forall ltac:(eapply gcpn6_from_paco; [eauto with paco|]);
    pcofix CIH;
    under_forall ltac:(eapply gcpn6_to_paco; [eauto with paco|])
  | [|- context[cpn7]]  =>
    under_forall ltac:(eapply cpn7_from_paco; [eauto with paco|]);
    pcofix CIH;
    under_forall ltac:(eapply gcpn7_to_paco; [eauto with paco|])
  | [|- context[gcpn7]] =>
    under_forall ltac:(eapply gcpn7_from_paco; [eauto with paco|]);
    pcofix CIH;
    under_forall ltac:(eapply gcpn7_to_paco; [eauto with paco|])
  | [|- context[cpn8]]  =>
    under_forall ltac:(eapply cpn8_from_paco; [eauto with paco|]);
    pcofix CIH;
    under_forall ltac:(eapply gcpn8_to_paco; [eauto with paco|])
  | [|- context[gcpn8]] =>
    under_forall ltac:(eapply gcpn8_from_paco; [eauto with paco|]);
    pcofix CIH;
    under_forall ltac:(eapply gcpn8_to_paco; [eauto with paco|])
  | [|- context[cpn9]]  =>
    under_forall ltac:(eapply cpn9_from_paco; [eauto with paco|]);
    pcofix CIH;
    under_forall ltac:(eapply gcpn9_to_paco; [eauto with paco|])
  | [|- context[gcpn9]] =>
    under_forall ltac:(eapply gcpn9_from_paco; [eauto with paco|]);
    pcofix CIH;
    under_forall ltac:(eapply gcpn9_to_paco; [eauto with paco|])
  | [|- context[cpn10]]  =>
    under_forall ltac:(eapply cpn10_from_paco; [eauto with paco|]);
    pcofix CIH;
    under_forall ltac:(eapply gcpn10_to_paco; [eauto with paco|])
  | [|- context[gcpn10]] =>
    under_forall ltac:(eapply gcpn10_from_paco; [eauto with paco|]);
    pcofix CIH;
    under_forall ltac:(eapply gcpn10_to_paco; [eauto with paco|])
  | [|- context[cpn11]]  =>
    under_forall ltac:(eapply cpn11_from_paco; [eauto with paco|]);
    pcofix CIH;
    under_forall ltac:(eapply gcpn11_to_paco; [eauto with paco|])
  | [|- context[gcpn11]] =>
    under_forall ltac:(eapply gcpn11_from_paco; [eauto with paco|]);
    pcofix CIH;
    under_forall ltac:(eapply gcpn11_to_paco; [eauto with paco|])
  | [|- context[cpn12]]  =>
    under_forall ltac:(eapply cpn12_from_paco; [eauto with paco|]);
    pcofix CIH;
    under_forall ltac:(eapply gcpn12_to_paco; [eauto with paco|])
  | [|- context[gcpn12]] =>
    under_forall ltac:(eapply gcpn12_from_paco; [eauto with paco|]);
    pcofix CIH;
    under_forall ltac:(eapply gcpn12_to_paco; [eauto with paco|])
  | [|- context[cpn13]]  =>
    under_forall ltac:(eapply cpn13_from_paco; [eauto with paco|]);
    pcofix CIH;
    under_forall ltac:(eapply gcpn13_to_paco; [eauto with paco|])
  | [|- context[gcpn13]] =>
    under_forall ltac:(eapply gcpn13_from_paco; [eauto with paco|]);
    pcofix CIH;
    under_forall ltac:(eapply gcpn13_to_paco; [eauto with paco|])
  | [|- context[cpn14]]  =>
    under_forall ltac:(eapply cpn14_from_paco; [eauto with paco|]);
    pcofix CIH;
    under_forall ltac:(eapply gcpn14_to_paco; [eauto with paco|])
  | [|- context[gcpn14]] =>
    under_forall ltac:(eapply gcpn14_from_paco; [eauto with paco|]);
    pcofix CIH;
    under_forall ltac:(eapply gcpn14_to_paco; [eauto with paco|])
  | [|- context[cpn15]]  =>
    under_forall ltac:(eapply cpn15_from_paco; [eauto with paco|]);
    pcofix CIH;
    under_forall ltac:(eapply gcpn15_to_paco; [eauto with paco|])
  | [|- context[gcpn15]] =>
    under_forall ltac:(eapply gcpn15_from_paco; [eauto with paco|]);
    pcofix CIH;
    under_forall ltac:(eapply gcpn15_to_paco; [eauto with paco|])
  | [|- context[cpn16]]  =>
    under_forall ltac:(eapply cpn16_from_paco; [eauto with paco|]);
    pcofix CIH;
    under_forall ltac:(eapply gcpn16_to_paco; [eauto with paco|])
  | [|- context[gcpn16]] =>
    under_forall ltac:(eapply gcpn16_from_paco; [eauto with paco|]);
    pcofix CIH;
    under_forall ltac:(eapply gcpn16_to_paco; [eauto with paco|])
  | [|- context[cpn17]]  =>
    under_forall ltac:(eapply cpn17_from_paco; [eauto with paco|]);
    pcofix CIH;
    under_forall ltac:(eapply gcpn17_to_paco; [eauto with paco|])
  | [|- context[gcpn17]] =>
    under_forall ltac:(eapply gcpn17_from_paco; [eauto with paco|]);
    pcofix CIH;
    under_forall ltac:(eapply gcpn17_to_paco; [eauto with paco|])
  | [|- context[cpn18]]  =>
    under_forall ltac:(eapply cpn18_from_paco; [eauto with paco|]);
    pcofix CIH;
    under_forall ltac:(eapply gcpn18_to_paco; [eauto with paco|])
  | [|- context[gcpn18]] =>
    under_forall ltac:(eapply gcpn18_from_paco; [eauto with paco|]);
    pcofix CIH;
    under_forall ltac:(eapply gcpn18_to_paco; [eauto with paco|])
  end.

(** ** pfold_reverse 
*)

Ltac pfold_reverse :=
  repeat red;
  match goal with 
  | [|- _ (upaco0 ?gf _)] => eapply (paco0_unfold (gf := gf))
  | [|- _ (upaco1 ?gf _) _] => eapply (paco1_unfold (gf := gf))
  | [|- _ (upaco2 ?gf _) _ _] => eapply (paco2_unfold (gf := gf))
  | [|- _ (upaco3 ?gf _) _ _ _] => eapply (paco3_unfold (gf := gf))
  | [|- _ (upaco4 ?gf _) _ _ _ _] => eapply (paco4_unfold (gf := gf))
  | [|- _ (upaco5 ?gf _) _ _ _ _ _] => eapply (paco5_unfold (gf := gf))
  | [|- _ (upaco6 ?gf _) _ _ _ _ _ _] => eapply (paco6_unfold (gf := gf))
  | [|- _ (upaco7 ?gf _) _ _ _ _ _ _ _] => eapply (paco7_unfold (gf := gf))
  | [|- _ (upaco8 ?gf _) _ _ _ _ _ _ _ _] => eapply (paco8_unfold (gf := gf))
  | [|- _ (upaco9 ?gf _) _ _ _ _ _ _ _ _ _] => eapply (paco9_unfold (gf := gf))
  | [|- _ (upaco10 ?gf _) _ _ _ _ _ _ _ _ _ _] => eapply (paco10_unfold (gf := gf))
  | [|- _ (upaco11 ?gf _) _ _ _ _ _ _ _ _ _ _ _] => eapply (paco11_unfold (gf := gf))
  | [|- _ (upaco12 ?gf _) _ _ _ _ _ _ _ _ _ _ _ _] => eapply (paco12_unfold (gf := gf))
  | [|- _ (upaco13 ?gf _) _ _ _ _ _ _ _ _ _ _ _ _ _] => eapply (paco13_unfold (gf := gf))
  | [|- _ (upaco14 ?gf _) _ _ _ _ _ _ _ _ _ _ _ _ _ _] => eapply (paco14_unfold (gf := gf))
  | [|- _ (upaco15 ?gf _) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _] => eapply (paco15_unfold (gf := gf))
  | [|- _ (upaco16 ?gf _) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _] => eapply (paco16_unfold (gf := gf))
  | [|- _ (upaco17 ?gf _) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _] => eapply (paco17_unfold (gf := gf))
  | [|- _ (upaco18 ?gf _) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _] => eapply (paco18_unfold (gf := gf))
  end;
  eauto with paco.

(** ** punfold_reverse H 
*)

Ltac punfold_reverse H :=
  repeat red in H;
  let PP := type of H in
  match PP with
  | _ (upaco0 ?gf _) => eapply (paco0_fold gf) in H
  | _ (upaco1 ?gf _) _ => eapply (paco1_fold gf) in H
  | _ (upaco2 ?gf _) _ _ => eapply (paco2_fold gf) in H
  | _ (upaco3 ?gf _) _ _ _ => eapply (paco3_fold gf) in H
  | _ (upaco4 ?gf _) _ _ _ _ => eapply (paco4_fold gf) in H
  | _ (upaco5 ?gf _) _ _ _ _ _ => eapply (paco5_fold gf) in H
  | _ (upaco6 ?gf _) _ _ _ _ _ _ => eapply (paco6_fold gf) in H
  | _ (upaco7 ?gf _) _ _ _ _ _ _ _ => eapply (paco7_fold gf) in H
  | _ (upaco8 ?gf _) _ _ _ _ _ _ _ _ => eapply (paco8_fold gf) in H
  | _ (upaco9 ?gf _) _ _ _ _ _ _ _ _ _ => eapply (paco9_fold gf) in H
  | _ (upaco10 ?gf _) _ _ _ _ _ _ _ _ _ _ => eapply (paco10_fold gf) in H
  | _ (upaco11 ?gf _) _ _ _ _ _ _ _ _ _ _ _ => eapply (paco11_fold gf) in H
  | _ (upaco12 ?gf _) _ _ _ _ _ _ _ _ _ _ _ _ => eapply (paco12_fold gf) in H
  | _ (upaco13 ?gf _) _ _ _ _ _ _ _ _ _ _ _ _ _ => eapply (paco13_fold gf) in H
  | _ (upaco14 ?gf _) _ _ _ _ _ _ _ _ _ _ _ _ _ _ => eapply (paco14_fold gf) in H
  | _ (upaco15 ?gf _) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => eapply (paco15_fold gf) in H
  | _ (upaco16 ?gf _) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => eapply (paco16_fold gf) in H
  | _ (upaco17 ?gf _) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => eapply (paco17_fold gf) in H
  | _ (upaco18 ?gf _) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => eapply (paco18_fold gf) in H
  end;
  eauto with paco.

