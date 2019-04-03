Require Import pacotac_internal pacotac pacoall cpnall.

(** ** uinit
*)

Tactic Notation "uinit_" :=
  match goal with
  | [|- context[paco0]] => eapply cpn0_init; [eauto with paco|]
  | [|- context[paco1]] => eapply cpn1_init; [eauto with paco|]
  | [|- context[paco2]] => eapply cpn2_init; [eauto with paco|]
  | [|- context[paco3]] => eapply cpn3_init; [eauto with paco|]
  | [|- context[paco4]] => eapply cpn4_init; [eauto with paco|]
  | [|- context[paco5]] => eapply cpn5_init; [eauto with paco|]
  | [|- context[paco6]] => eapply cpn6_init; [eauto with paco|]
  | [|- context[paco7]] => eapply cpn7_init; [eauto with paco|]
  | [|- context[paco8]] => eapply cpn8_init; [eauto with paco|]
  | [|- context[paco9]] => eapply cpn9_init; [eauto with paco|]
  | [|- context[paco10]] => eapply cpn10_init; [eauto with paco|]
  | [|- context[paco11]] => eapply cpn11_init; [eauto with paco|]
  | [|- context[paco12]] => eapply cpn12_init; [eauto with paco|]
  | [|- context[paco13]] => eapply cpn13_init; [eauto with paco|]
  | [|- context[paco14]] => eapply cpn14_init; [eauto with paco|]
  end.
Ltac uinit := repeat red; under_forall ltac:(uinit_).

(** ** ufinal
*)

Tactic Notation "ufinal_" :=
  match goal with
  | [|- context[fcpn0]] => eapply fcpn0_final; [eauto with paco|]
  | [|- context[cpn0]]  => eapply cpn0_final; [eauto with paco|]
  | [|- context[fcpn1]] => eapply fcpn1_final; [eauto with paco|]
  | [|- context[cpn1]]  => eapply cpn1_final; [eauto with paco|]
  | [|- context[fcpn2]] => eapply fcpn2_final; [eauto with paco|]
  | [|- context[cpn2]]  => eapply cpn2_final; [eauto with paco|]
  | [|- context[fcpn3]] => eapply fcpn3_final; [eauto with paco|]
  | [|- context[cpn3]]  => eapply cpn3_final; [eauto with paco|]
  | [|- context[fcpn4]] => eapply fcpn4_final; [eauto with paco|]
  | [|- context[cpn4]]  => eapply cpn4_final; [eauto with paco|]
  | [|- context[fcpn5]] => eapply fcpn5_final; [eauto with paco|]
  | [|- context[cpn5]]  => eapply cpn5_final; [eauto with paco|]
  | [|- context[fcpn6]] => eapply fcpn6_final; [eauto with paco|]
  | [|- context[cpn6]]  => eapply cpn6_final; [eauto with paco|]
  | [|- context[fcpn7]] => eapply fcpn7_final; [eauto with paco|]
  | [|- context[cpn7]]  => eapply cpn7_final; [eauto with paco|]
  | [|- context[fcpn8]] => eapply fcpn8_final; [eauto with paco|]
  | [|- context[cpn8]]  => eapply cpn8_final; [eauto with paco|]
  | [|- context[fcpn9]] => eapply fcpn9_final; [eauto with paco|]
  | [|- context[cpn9]]  => eapply cpn9_final; [eauto with paco|]
  | [|- context[fcpn10]] => eapply fcpn10_final; [eauto with paco|]
  | [|- context[cpn10]]  => eapply cpn10_final; [eauto with paco|]
  | [|- context[fcpn11]] => eapply fcpn11_final; [eauto with paco|]
  | [|- context[cpn11]]  => eapply cpn11_final; [eauto with paco|]
  | [|- context[fcpn12]] => eapply fcpn12_final; [eauto with paco|]
  | [|- context[cpn12]]  => eapply cpn12_final; [eauto with paco|]
  | [|- context[fcpn13]] => eapply fcpn13_final; [eauto with paco|]
  | [|- context[cpn13]]  => eapply cpn13_final; [eauto with paco|]
  | [|- context[fcpn14]] => eapply fcpn14_final; [eauto with paco|]
  | [|- context[cpn14]]  => eapply cpn14_final; [eauto with paco|]
  end.
Ltac ufinal := under_forall ltac:(ufinal_).

(** ** fcpn_fold
*)

Ltac fcpn_fold :=
  match goal with
  | [|- ?gf (cpn0 _ ?r)] => change (gf (cpn0 gf r)) with (fcpn0 gf r)
  | [|- ?gf (cpn1 _ ?r) _] => change (gf (cpn1 gf r)) with (fcpn1 gf r)
  | [|- ?gf (cpn2 _ ?r) _ _] => change (gf (cpn2 gf r)) with (fcpn2 gf r)
  | [|- ?gf (cpn3 _ ?r) _ _ _] => change (gf (cpn3 gf r)) with (fcpn3 gf r)
  | [|- ?gf (cpn4 _ ?r) _ _ _ _] => change (gf (cpn4 gf r)) with (fcpn4 gf r)
  | [|- ?gf (cpn5 _ ?r) _ _ _ _ _] => change (gf (cpn5 gf r)) with (fcpn5 gf r)
  | [|- ?gf (cpn6 _ ?r) _ _ _ _ _ _] => change (gf (cpn6 gf r)) with (fcpn6 gf r)
  | [|- ?gf (cpn7 _ ?r) _ _ _ _ _ _ _] => change (gf (cpn7 gf r)) with (fcpn7 gf r)
  | [|- ?gf (cpn8 _ ?r) _ _ _ _ _ _ _ _] => change (gf (cpn8 gf r)) with (fcpn8 gf r)
  | [|- ?gf (cpn9 _ ?r) _ _ _ _ _ _ _ _ _] => change (gf (cpn9 gf r)) with (fcpn9 gf r)
  | [|- ?gf (cpn10 _ ?r) _ _ _ _ _ _ _ _ _ _] => change (gf (cpn10 gf r)) with (fcpn10 gf r)
  | [|- ?gf (cpn11 _ ?r) _ _ _ _ _ _ _ _ _ _ _] => change (gf (cpn11 gf r)) with (fcpn11 gf r)
  | [|- ?gf (cpn12 _ ?r) _ _ _ _ _ _ _ _ _ _ _ _] => change (gf (cpn12 gf r)) with (fcpn12 gf r)
  | [|- ?gf (cpn13 _ ?r) _ _ _ _ _ _ _ _ _ _ _ _ _] => change (gf (cpn13 gf r)) with (fcpn13 gf r)
  | [|- ?gf (cpn14 _ ?r) _ _ _ _ _ _ _ _ _ _ _ _ _ _] => change (gf (cpn14 gf r)) with (fcpn14 gf r)
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
  end.

(** ** ubase
*)

Tactic Notation "ubase_" :=
  match goal with
  | [|- context[cpn0]] => eapply cpn0_base
  | [|- context[cpn1]] => eapply cpn1_base
  | [|- context[cpn2]] => eapply cpn2_base
  | [|- context[cpn3]] => eapply cpn3_base
  | [|- context[cpn4]] => eapply cpn4_base
  | [|- context[cpn5]] => eapply cpn5_base
  | [|- context[cpn6]] => eapply cpn6_base
  | [|- context[cpn7]] => eapply cpn7_base
  | [|- context[cpn8]] => eapply cpn8_base
  | [|- context[cpn9]] => eapply cpn9_base
  | [|- context[cpn10]] => eapply cpn10_base
  | [|- context[cpn11]] => eapply cpn11_base
  | [|- context[cpn12]] => eapply cpn12_base
  | [|- context[cpn13]] => eapply cpn13_base
  | [|- context[cpn14]] => eapply cpn14_base
  end.
Ltac ubase := under_forall ltac:(ubase_).

(** ** uunfold H
*)

Ltac uunfold H :=
  repeat red in H;
  let G := type of H in
  match G with
  | context[cpn0] => eapply cpn0_unfold in H; [|eauto with paco]
  | context[cpn1] => eapply cpn1_unfold in H; [|eauto with paco]
  | context[cpn2] => eapply cpn2_unfold in H; [|eauto with paco]
  | context[cpn3] => eapply cpn3_unfold in H; [|eauto with paco]
  | context[cpn4] => eapply cpn4_unfold in H; [|eauto with paco]
  | context[cpn5] => eapply cpn5_unfold in H; [|eauto with paco]
  | context[cpn6] => eapply cpn6_unfold in H; [|eauto with paco]
  | context[cpn7] => eapply cpn7_unfold in H; [|eauto with paco]
  | context[cpn8] => eapply cpn8_unfold in H; [|eauto with paco]
  | context[cpn9] => eapply cpn9_unfold in H; [|eauto with paco]
  | context[cpn10] => eapply cpn10_unfold in H; [|eauto with paco]
  | context[cpn11] => eapply cpn11_unfold in H; [|eauto with paco]
  | context[cpn12] => eapply cpn12_unfold in H; [|eauto with paco]
  | context[cpn13] => eapply cpn13_unfold in H; [|eauto with paco]
  | context[cpn14] => eapply cpn14_unfold in H; [|eauto with paco]
  end.

(** ** ucpn
*)

Tactic Notation "ucpn_" :=
  match goal with
  | [|- context[cpn0]] => eapply cpn0_cpn; [eauto with paco|]
  | [|- context[cpn1]] => eapply cpn1_cpn; [eauto with paco|]
  | [|- context[cpn2]] => eapply cpn2_cpn; [eauto with paco|]
  | [|- context[cpn3]] => eapply cpn3_cpn; [eauto with paco|]
  | [|- context[cpn4]] => eapply cpn4_cpn; [eauto with paco|]
  | [|- context[cpn5]] => eapply cpn5_cpn; [eauto with paco|]
  | [|- context[cpn6]] => eapply cpn6_cpn; [eauto with paco|]
  | [|- context[cpn7]] => eapply cpn7_cpn; [eauto with paco|]
  | [|- context[cpn8]] => eapply cpn8_cpn; [eauto with paco|]
  | [|- context[cpn9]] => eapply cpn9_cpn; [eauto with paco|]
  | [|- context[cpn10]] => eapply cpn10_cpn; [eauto with paco|]
  | [|- context[cpn11]] => eapply cpn11_cpn; [eauto with paco|]
  | [|- context[cpn12]] => eapply cpn12_cpn; [eauto with paco|]
  | [|- context[cpn13]] => eapply cpn13_cpn; [eauto with paco|]
  | [|- context[cpn14]] => eapply cpn14_cpn; [eauto with paco|]
  end.
Ltac ucpn := repeat red; under_forall ltac:(ucpn_).

(** ** ustep
*)

Tactic Notation "ustep_" :=
  match goal with
  | [|- context[cpn0]] => eapply cpn0_step; [eauto with paco|]
  | [|- context[cpn1]] => eapply cpn1_step; [eauto with paco|]
  | [|- context[cpn2]] => eapply cpn2_step; [eauto with paco|]
  | [|- context[cpn3]] => eapply cpn3_step; [eauto with paco|]
  | [|- context[cpn4]] => eapply cpn4_step; [eauto with paco|]
  | [|- context[cpn5]] => eapply cpn5_step; [eauto with paco|]
  | [|- context[cpn6]] => eapply cpn6_step; [eauto with paco|]
  | [|- context[cpn7]] => eapply cpn7_step; [eauto with paco|]
  | [|- context[cpn8]] => eapply cpn8_step; [eauto with paco|]
  | [|- context[cpn9]] => eapply cpn9_step; [eauto with paco|]
  | [|- context[cpn10]] => eapply cpn10_step; [eauto with paco|]
  | [|- context[cpn11]] => eapply cpn11_step; [eauto with paco|]
  | [|- context[cpn12]] => eapply cpn12_step; [eauto with paco|]
  | [|- context[cpn13]] => eapply cpn13_step; [eauto with paco|]
  | [|- context[cpn14]] => eapply cpn14_step; [eauto with paco|]
  end.
Ltac ustep := repeat red; under_forall ltac:(ustep_).

(** ** uclo H
*)

Tactic Notation "guclo__" constr(H) :=
  match goal with
  | [|- context[fcpn0]] => eapply fcpn0_clo; [|eapply H|]; [eauto with paco|..]
  | [|- context[fcpn1]] => eapply fcpn1_clo; [|eapply H|]; [eauto with paco|..]
  | [|- context[fcpn2]] => eapply fcpn2_clo; [|eapply H|]; [eauto with paco|..]
  | [|- context[fcpn3]] => eapply fcpn3_clo; [|eapply H|]; [eauto with paco|..]
  | [|- context[fcpn4]] => eapply fcpn4_clo; [|eapply H|]; [eauto with paco|..]
  | [|- context[fcpn5]] => eapply fcpn5_clo; [|eapply H|]; [eauto with paco|..]
  | [|- context[fcpn6]] => eapply fcpn6_clo; [|eapply H|]; [eauto with paco|..]
  | [|- context[fcpn7]] => eapply fcpn7_clo; [|eapply H|]; [eauto with paco|..]
  | [|- context[fcpn8]] => eapply fcpn8_clo; [|eapply H|]; [eauto with paco|..]
  | [|- context[fcpn9]] => eapply fcpn9_clo; [|eapply H|]; [eauto with paco|..]
  | [|- context[fcpn10]] => eapply fcpn10_clo; [|eapply H|]; [eauto with paco|..]
  | [|- context[fcpn11]] => eapply fcpn11_clo; [|eapply H|]; [eauto with paco|..]
  | [|- context[fcpn12]] => eapply fcpn12_clo; [|eapply H|]; [eauto with paco|..]
  | [|- context[fcpn13]] => eapply fcpn13_clo; [|eapply H|]; [eauto with paco|..]
  | [|- context[fcpn14]] => eapply fcpn14_clo; [|eapply H|]; [eauto with paco|..]
  end.
Ltac guclo_ H := under_forall ltac:(guclo__ H).
Tactic Notation "uclo__" constr(H) :=
  match goal with
  | [|- context[cpn0]]  => eapply cpn0_clo; [|eapply H|]; [eauto with paco|..]
  | [|- context[cpn1]]  => eapply cpn1_clo; [|eapply H|]; [eauto with paco|..]
  | [|- context[cpn2]]  => eapply cpn2_clo; [|eapply H|]; [eauto with paco|..]
  | [|- context[cpn3]]  => eapply cpn3_clo; [|eapply H|]; [eauto with paco|..]
  | [|- context[cpn4]]  => eapply cpn4_clo; [|eapply H|]; [eauto with paco|..]
  | [|- context[cpn5]]  => eapply cpn5_clo; [|eapply H|]; [eauto with paco|..]
  | [|- context[cpn6]]  => eapply cpn6_clo; [|eapply H|]; [eauto with paco|..]
  | [|- context[cpn7]]  => eapply cpn7_clo; [|eapply H|]; [eauto with paco|..]
  | [|- context[cpn8]]  => eapply cpn8_clo; [|eapply H|]; [eauto with paco|..]
  | [|- context[cpn9]]  => eapply cpn9_clo; [|eapply H|]; [eauto with paco|..]
  | [|- context[cpn10]]  => eapply cpn10_clo; [|eapply H|]; [eauto with paco|..]
  | [|- context[cpn11]]  => eapply cpn11_clo; [|eapply H|]; [eauto with paco|..]
  | [|- context[cpn12]]  => eapply cpn12_clo; [|eapply H|]; [eauto with paco|..]
  | [|- context[cpn13]]  => eapply cpn13_clo; [|eapply H|]; [eauto with paco|..]
  | [|- context[cpn14]]  => eapply cpn14_clo; [|eapply H|]; [eauto with paco|..]
  end.
Ltac uclo_ H := repeat red; under_forall ltac:(uclo__ H).
Ltac uclo H := first[ guclo_ H | uclo_ H ].

(** ** ucofix CIH [with r]
*)

Tactic Notation "gucofix_" ident(CIH) "with" ident(r) :=
  generalize _paco_mark_cons; intros;
  match goal with
  | [|- context[fcpn0]] =>
    (eapply fcpn0_from_paco; [eauto with paco|]); paco_revert_hyp _paco_mark;
    pcofix CIH with r;
    under_forall ltac:(eapply fcpn0_to_paco; [eauto with paco|])
  | [|- context[fcpn1]] =>
    (eapply fcpn1_from_paco; [eauto with paco|]); paco_revert_hyp _paco_mark;
    pcofix CIH with r;
    under_forall ltac:(eapply fcpn1_to_paco; [eauto with paco|])
  | [|- context[fcpn2]] =>
    (eapply fcpn2_from_paco; [eauto with paco|]); paco_revert_hyp _paco_mark;
    pcofix CIH with r;
    under_forall ltac:(eapply fcpn2_to_paco; [eauto with paco|])
  | [|- context[fcpn3]] =>
    (eapply fcpn3_from_paco; [eauto with paco|]); paco_revert_hyp _paco_mark;
    pcofix CIH with r;
    under_forall ltac:(eapply fcpn3_to_paco; [eauto with paco|])
  | [|- context[fcpn4]] =>
    (eapply fcpn4_from_paco; [eauto with paco|]); paco_revert_hyp _paco_mark;
    pcofix CIH with r;
    under_forall ltac:(eapply fcpn4_to_paco; [eauto with paco|])
  | [|- context[fcpn5]] =>
    (eapply fcpn5_from_paco; [eauto with paco|]); paco_revert_hyp _paco_mark;
    pcofix CIH with r;
    under_forall ltac:(eapply fcpn5_to_paco; [eauto with paco|])
  | [|- context[fcpn6]] =>
    (eapply fcpn6_from_paco; [eauto with paco|]); paco_revert_hyp _paco_mark;
    pcofix CIH with r;
    under_forall ltac:(eapply fcpn6_to_paco; [eauto with paco|])
  | [|- context[fcpn7]] =>
    (eapply fcpn7_from_paco; [eauto with paco|]); paco_revert_hyp _paco_mark;
    pcofix CIH with r;
    under_forall ltac:(eapply fcpn7_to_paco; [eauto with paco|])
  | [|- context[fcpn8]] =>
    (eapply fcpn8_from_paco; [eauto with paco|]); paco_revert_hyp _paco_mark;
    pcofix CIH with r;
    under_forall ltac:(eapply fcpn8_to_paco; [eauto with paco|])
  | [|- context[fcpn9]] =>
    (eapply fcpn9_from_paco; [eauto with paco|]); paco_revert_hyp _paco_mark;
    pcofix CIH with r;
    under_forall ltac:(eapply fcpn9_to_paco; [eauto with paco|])
  | [|- context[fcpn10]] =>
    (eapply fcpn10_from_paco; [eauto with paco|]); paco_revert_hyp _paco_mark;
    pcofix CIH with r;
    under_forall ltac:(eapply fcpn10_to_paco; [eauto with paco|])
  | [|- context[fcpn11]] =>
    (eapply fcpn11_from_paco; [eauto with paco|]); paco_revert_hyp _paco_mark;
    pcofix CIH with r;
    under_forall ltac:(eapply fcpn11_to_paco; [eauto with paco|])
  | [|- context[fcpn12]] =>
    (eapply fcpn12_from_paco; [eauto with paco|]); paco_revert_hyp _paco_mark;
    pcofix CIH with r;
    under_forall ltac:(eapply fcpn12_to_paco; [eauto with paco|])
  | [|- context[fcpn13]] =>
    (eapply fcpn13_from_paco; [eauto with paco|]); paco_revert_hyp _paco_mark;
    pcofix CIH with r;
    under_forall ltac:(eapply fcpn13_to_paco; [eauto with paco|])
  | [|- context[fcpn14]] =>
    (eapply fcpn14_from_paco; [eauto with paco|]); paco_revert_hyp _paco_mark;
    pcofix CIH with r;
    under_forall ltac:(eapply fcpn14_to_paco; [eauto with paco|])
  end.
Tactic Notation "ucofix_" ident(CIH) "with" ident(r) :=
  repeat red;
  generalize _paco_mark_cons; intros;
  match goal with
  | [|- context[cpn0]]  =>
    (eapply cpn0_from_paco; [eauto with paco|]); paco_revert_hyp _paco_mark;
    pcofix CIH with r;
    under_forall ltac:(eapply fcpn0_to_paco; [eauto with paco|])
  | [|- context[cpn1]]  =>
    (eapply cpn1_from_paco; [eauto with paco|]); paco_revert_hyp _paco_mark;
    pcofix CIH with r;
    under_forall ltac:(eapply fcpn1_to_paco; [eauto with paco|])
  | [|- context[cpn2]]  =>
    (eapply cpn2_from_paco; [eauto with paco|]); paco_revert_hyp _paco_mark;
    pcofix CIH with r;
    under_forall ltac:(eapply fcpn2_to_paco; [eauto with paco|])
  | [|- context[cpn3]]  =>
    (eapply cpn3_from_paco; [eauto with paco|]); paco_revert_hyp _paco_mark;
    pcofix CIH with r;
    under_forall ltac:(eapply fcpn3_to_paco; [eauto with paco|])
  | [|- context[cpn4]]  =>
    (eapply cpn4_from_paco; [eauto with paco|]); paco_revert_hyp _paco_mark;
    pcofix CIH with r;
    under_forall ltac:(eapply fcpn4_to_paco; [eauto with paco|])
  | [|- context[cpn5]]  =>
    (eapply cpn5_from_paco; [eauto with paco|]); paco_revert_hyp _paco_mark;
    pcofix CIH with r;
    under_forall ltac:(eapply fcpn5_to_paco; [eauto with paco|])
  | [|- context[cpn6]]  =>
    (eapply cpn6_from_paco; [eauto with paco|]); paco_revert_hyp _paco_mark;
    pcofix CIH with r;
    under_forall ltac:(eapply fcpn6_to_paco; [eauto with paco|])
  | [|- context[cpn7]]  =>
    (eapply cpn7_from_paco; [eauto with paco|]); paco_revert_hyp _paco_mark;
    pcofix CIH with r;
    under_forall ltac:(eapply fcpn7_to_paco; [eauto with paco|])
  | [|- context[cpn8]]  =>
    (eapply cpn8_from_paco; [eauto with paco|]); paco_revert_hyp _paco_mark;
    pcofix CIH with r;
    under_forall ltac:(eapply fcpn8_to_paco; [eauto with paco|])
  | [|- context[cpn9]]  =>
    (eapply cpn9_from_paco; [eauto with paco|]); paco_revert_hyp _paco_mark;
    pcofix CIH with r;
    under_forall ltac:(eapply fcpn9_to_paco; [eauto with paco|])
  | [|- context[cpn10]]  =>
    (eapply cpn10_from_paco; [eauto with paco|]); paco_revert_hyp _paco_mark;
    pcofix CIH with r;
    under_forall ltac:(eapply fcpn10_to_paco; [eauto with paco|])
  | [|- context[cpn11]]  =>
    (eapply cpn11_from_paco; [eauto with paco|]); paco_revert_hyp _paco_mark;
    pcofix CIH with r;
    under_forall ltac:(eapply fcpn11_to_paco; [eauto with paco|])
  | [|- context[cpn12]]  =>
    (eapply cpn12_from_paco; [eauto with paco|]); paco_revert_hyp _paco_mark;
    pcofix CIH with r;
    under_forall ltac:(eapply fcpn12_to_paco; [eauto with paco|])
  | [|- context[cpn13]]  =>
    (eapply cpn13_from_paco; [eauto with paco|]); paco_revert_hyp _paco_mark;
    pcofix CIH with r;
    under_forall ltac:(eapply fcpn13_to_paco; [eauto with paco|])
  | [|- context[cpn14]]  =>
    (eapply cpn14_from_paco; [eauto with paco|]); paco_revert_hyp _paco_mark;
    pcofix CIH with r;
    under_forall ltac:(eapply fcpn14_to_paco; [eauto with paco|])
  end.
Tactic Notation "ucofix" ident(CIH) "with" ident(r) :=
  first[ gucofix_ CIH with r | ucofix_ CIH with r ].
Tactic Notation "ucofix" ident(CIH) := ucofix CIH with r.

