Require Import pacotac_internal pacotac pacoall pcpnall.

(** ** uinit
*)

Tactic Notation "uinit_" :=
  match goal with
  | [|- context[paco0]] => eapply ucpn0_init; [eauto with paco|]
  | [|- context[paco1]] => eapply ucpn1_init; [eauto with paco|]
  | [|- context[paco2]] => eapply ucpn2_init; [eauto with paco|]
  | [|- context[paco3]] => eapply ucpn3_init; [eauto with paco|]
  | [|- context[paco4]] => eapply ucpn4_init; [eauto with paco|]
  | [|- context[paco5]] => eapply ucpn5_init; [eauto with paco|]
  | [|- context[paco6]] => eapply ucpn6_init; [eauto with paco|]
  | [|- context[paco7]] => eapply ucpn7_init; [eauto with paco|]
  | [|- context[paco8]] => eapply ucpn8_init; [eauto with paco|]
  | [|- context[paco9]] => eapply ucpn9_init; [eauto with paco|]
  | [|- context[paco10]] => eapply ucpn10_init; [eauto with paco|]
  | [|- context[paco11]] => eapply ucpn11_init; [eauto with paco|]
  | [|- context[paco12]] => eapply ucpn12_init; [eauto with paco|]
  | [|- context[paco13]] => eapply ucpn13_init; [eauto with paco|]
  | [|- context[paco14]] => eapply ucpn14_init; [eauto with paco|]
  end.
Tactic Notation "uinit" := repeat red; under_forall ltac:(uinit_).

(** ** ufinal
*)

Tactic Notation "ufinal_" :=
  match goal with
  | [|- context[dcpn0]] => first[eapply ucpn0_final | eapply pcpn0_final]
  | [|- context[dcpn1]] => first[eapply ucpn1_final | eapply pcpn1_final]
  | [|- context[dcpn2]] => first[eapply ucpn2_final | eapply pcpn2_final]
  | [|- context[dcpn3]] => first[eapply ucpn3_final | eapply pcpn3_final]
  | [|- context[dcpn4]] => first[eapply ucpn4_final | eapply pcpn4_final]
  | [|- context[dcpn5]] => first[eapply ucpn5_final | eapply pcpn5_final]
  | [|- context[dcpn6]] => first[eapply ucpn6_final | eapply pcpn6_final]
  | [|- context[dcpn7]] => first[eapply ucpn7_final | eapply pcpn7_final]
  | [|- context[dcpn8]] => first[eapply ucpn8_final | eapply pcpn8_final]
  | [|- context[dcpn9]] => first[eapply ucpn9_final | eapply pcpn9_final]
  | [|- context[dcpn10]] => first[eapply ucpn10_final | eapply pcpn10_final]
  | [|- context[dcpn11]] => first[eapply ucpn11_final | eapply pcpn11_final]
  | [|- context[dcpn12]] => first[eapply ucpn12_final | eapply pcpn12_final]
  | [|- context[dcpn13]] => first[eapply ucpn13_final | eapply pcpn13_final]
  | [|- context[dcpn14]] => first[eapply ucpn14_final | eapply pcpn14_final]
  end.
Tactic Notation "ufinal" := repeat red; under_forall ltac:(ufinal_).

(** ** ucpn_fold
*)

Tactic Notation "ucpn_fold_" :=
  match goal with
  | [|- context[dcpn0 ?gf ?r]] => first [apply ucpn0_id | apply pcpn0_id]
  | [|- context[dcpn1 ?gf ?r]] => first [apply ucpn1_id | apply pcpn1_id]
  | [|- context[dcpn2 ?gf ?r]] => first [apply ucpn2_id | apply pcpn2_id]
  | [|- context[dcpn3 ?gf ?r]] => first [apply ucpn3_id | apply pcpn3_id]
  | [|- context[dcpn4 ?gf ?r]] => first [apply ucpn4_id | apply pcpn4_id]
  | [|- context[dcpn5 ?gf ?r]] => first [apply ucpn5_id | apply pcpn5_id]
  | [|- context[dcpn6 ?gf ?r]] => first [apply ucpn6_id | apply pcpn6_id]
  | [|- context[dcpn7 ?gf ?r]] => first [apply ucpn7_id | apply pcpn7_id]
  | [|- context[dcpn8 ?gf ?r]] => first [apply ucpn8_id | apply pcpn8_id]
  | [|- context[dcpn9 ?gf ?r]] => first [apply ucpn9_id | apply pcpn9_id]
  | [|- context[dcpn10 ?gf ?r]] => first [apply ucpn10_id | apply pcpn10_id]
  | [|- context[dcpn11 ?gf ?r]] => first [apply ucpn11_id | apply pcpn11_id]
  | [|- context[dcpn12 ?gf ?r]] => first [apply ucpn12_id | apply pcpn12_id]
  | [|- context[dcpn13 ?gf ?r]] => first [apply ucpn13_id | apply pcpn13_id]
  | [|- context[dcpn14 ?gf ?r]] => first [apply ucpn14_id | apply pcpn14_id]
  end.
Tactic Notation "ucpn_fold" := repeat red; under_forall ltac:(ucpn_fold_).

(** ** uunfold H
*)

Ltac uunfold H :=
  repeat red in H;
  let G := type of H in
  match G with
  | context[dcpn0] => eapply pcpn0_unfold in H; [|eauto with paco]
  | context[dcpn1] => eapply pcpn1_unfold in H; [|eauto with paco]
  | context[dcpn2] => eapply pcpn2_unfold in H; [|eauto with paco]
  | context[dcpn3] => eapply pcpn3_unfold in H; [|eauto with paco]
  | context[dcpn4] => eapply pcpn4_unfold in H; [|eauto with paco]
  | context[dcpn5] => eapply pcpn5_unfold in H; [|eauto with paco]
  | context[dcpn6] => eapply pcpn6_unfold in H; [|eauto with paco]
  | context[dcpn7] => eapply pcpn7_unfold in H; [|eauto with paco]
  | context[dcpn8] => eapply pcpn8_unfold in H; [|eauto with paco]
  | context[dcpn9] => eapply pcpn9_unfold in H; [|eauto with paco]
  | context[dcpn10] => eapply pcpn10_unfold in H; [|eauto with paco]
  | context[dcpn11] => eapply pcpn11_unfold in H; [|eauto with paco]
  | context[dcpn12] => eapply pcpn12_unfold in H; [|eauto with paco]
  | context[dcpn13] => eapply pcpn13_unfold in H; [|eauto with paco]
  | context[dcpn14] => eapply pcpn14_unfold in H; [|eauto with paco]
  end.

(** ** ubase
*)

Tactic Notation "ubase_" :=
  match goal with
  | [|- context[dcpn0]] => eapply ucpn0_base
  | [|- context[dcpn1]] => eapply ucpn1_base
  | [|- context[dcpn2]] => eapply ucpn2_base
  | [|- context[dcpn3]] => eapply ucpn3_base
  | [|- context[dcpn4]] => eapply ucpn4_base
  | [|- context[dcpn5]] => eapply ucpn5_base
  | [|- context[dcpn6]] => eapply ucpn6_base
  | [|- context[dcpn7]] => eapply ucpn7_base
  | [|- context[dcpn8]] => eapply ucpn8_base
  | [|- context[dcpn9]] => eapply ucpn9_base
  | [|- context[dcpn10]] => eapply ucpn10_base
  | [|- context[dcpn11]] => eapply ucpn11_base
  | [|- context[dcpn12]] => eapply ucpn12_base
  | [|- context[dcpn13]] => eapply ucpn13_base
  | [|- context[dcpn14]] => eapply ucpn14_base
  end.
Ltac ubase := repeat red; under_forall ltac:(ubase_).

(** ** ucpn
*)

Tactic Notation "ucpn_" :=
  match goal with
  | [|- context[dcpn0]] => eapply ucpn0_ucpn; [eauto with paco|]
  | [|- context[dcpn1]] => eapply ucpn1_ucpn; [eauto with paco|]
  | [|- context[dcpn2]] => eapply ucpn2_ucpn; [eauto with paco|]
  | [|- context[dcpn3]] => eapply ucpn3_ucpn; [eauto with paco|]
  | [|- context[dcpn4]] => eapply ucpn4_ucpn; [eauto with paco|]
  | [|- context[dcpn5]] => eapply ucpn5_ucpn; [eauto with paco|]
  | [|- context[dcpn6]] => eapply ucpn6_ucpn; [eauto with paco|]
  | [|- context[dcpn7]] => eapply ucpn7_ucpn; [eauto with paco|]
  | [|- context[dcpn8]] => eapply ucpn8_ucpn; [eauto with paco|]
  | [|- context[dcpn9]] => eapply ucpn9_ucpn; [eauto with paco|]
  | [|- context[dcpn10]] => eapply ucpn10_ucpn; [eauto with paco|]
  | [|- context[dcpn11]] => eapply ucpn11_ucpn; [eauto with paco|]
  | [|- context[dcpn12]] => eapply ucpn12_ucpn; [eauto with paco|]
  | [|- context[dcpn13]] => eapply ucpn13_ucpn; [eauto with paco|]
  | [|- context[dcpn14]] => eapply ucpn14_ucpn; [eauto with paco|]
  end.
Ltac ucpn := repeat red; under_forall ltac:(ucpn_).

(** ** ustep
*)

Tactic Notation "ustep_" :=
  match goal with
  | [|- context[dcpn0]] => first[eapply ucpn0_step | eapply pcpn0_step]
  | [|- context[dcpn1]] => first[eapply ucpn1_step | eapply pcpn1_step]
  | [|- context[dcpn2]] => first[eapply ucpn2_step | eapply pcpn2_step]
  | [|- context[dcpn3]] => first[eapply ucpn3_step | eapply pcpn3_step]
  | [|- context[dcpn4]] => first[eapply ucpn4_step | eapply pcpn4_step]
  | [|- context[dcpn5]] => first[eapply ucpn5_step | eapply pcpn5_step]
  | [|- context[dcpn6]] => first[eapply ucpn6_step | eapply pcpn6_step]
  | [|- context[dcpn7]] => first[eapply ucpn7_step | eapply pcpn7_step]
  | [|- context[dcpn8]] => first[eapply ucpn8_step | eapply pcpn8_step]
  | [|- context[dcpn9]] => first[eapply ucpn9_step | eapply pcpn9_step]
  | [|- context[dcpn10]] => first[eapply ucpn10_step | eapply pcpn10_step]
  | [|- context[dcpn11]] => first[eapply ucpn11_step | eapply pcpn11_step]
  | [|- context[dcpn12]] => first[eapply ucpn12_step | eapply pcpn12_step]
  | [|- context[dcpn13]] => first[eapply ucpn13_step | eapply pcpn13_step]
  | [|- context[dcpn14]] => first[eapply ucpn14_step | eapply pcpn14_step]
  end.
Ltac ustep := repeat red; under_forall ltac:(ustep_).

(** ** uclo H
*)

Tactic Notation "uclo_" constr(H) :=
  match goal with
  | [|- context[dcpn0]]  => first[eapply ucpn0_clo; [|eapply H|]; [eauto with paco|..] | eapply pcpn0_clo; [|eapply H|]; [eauto with paco|..]]
  | [|- context[dcpn1]]  => first[eapply ucpn1_clo; [|eapply H|]; [eauto with paco|..] | eapply pcpn1_clo; [|eapply H|]; [eauto with paco|..]]
  | [|- context[dcpn2]]  => first[eapply ucpn2_clo; [|eapply H|]; [eauto with paco|..] | eapply pcpn2_clo; [|eapply H|]; [eauto with paco|..]]
  | [|- context[dcpn3]]  => first[eapply ucpn3_clo; [|eapply H|]; [eauto with paco|..] | eapply pcpn3_clo; [|eapply H|]; [eauto with paco|..]]
  | [|- context[dcpn4]]  => first[eapply ucpn4_clo; [|eapply H|]; [eauto with paco|..] | eapply pcpn4_clo; [|eapply H|]; [eauto with paco|..]]
  | [|- context[dcpn5]]  => first[eapply ucpn5_clo; [|eapply H|]; [eauto with paco|..] | eapply pcpn5_clo; [|eapply H|]; [eauto with paco|..]]
  | [|- context[dcpn6]]  => first[eapply ucpn6_clo; [|eapply H|]; [eauto with paco|..] | eapply pcpn6_clo; [|eapply H|]; [eauto with paco|..]]
  | [|- context[dcpn7]]  => first[eapply ucpn7_clo; [|eapply H|]; [eauto with paco|..] | eapply pcpn7_clo; [|eapply H|]; [eauto with paco|..]]
  | [|- context[dcpn8]]  => first[eapply ucpn8_clo; [|eapply H|]; [eauto with paco|..] | eapply pcpn8_clo; [|eapply H|]; [eauto with paco|..]]
  | [|- context[dcpn9]]  => first[eapply ucpn9_clo; [|eapply H|]; [eauto with paco|..] | eapply pcpn9_clo; [|eapply H|]; [eauto with paco|..]]
  | [|- context[dcpn10]]  => first[eapply ucpn10_clo; [|eapply H|]; [eauto with paco|..] | eapply pcpn10_clo; [|eapply H|]; [eauto with paco|..]]
  | [|- context[dcpn11]]  => first[eapply ucpn11_clo; [|eapply H|]; [eauto with paco|..] | eapply pcpn11_clo; [|eapply H|]; [eauto with paco|..]]
  | [|- context[dcpn12]]  => first[eapply ucpn12_clo; [|eapply H|]; [eauto with paco|..] | eapply pcpn12_clo; [|eapply H|]; [eauto with paco|..]]
  | [|- context[dcpn13]]  => first[eapply ucpn13_clo; [|eapply H|]; [eauto with paco|..] | eapply pcpn13_clo; [|eapply H|]; [eauto with paco|..]]
  | [|- context[dcpn14]]  => first[eapply ucpn14_clo; [|eapply H|]; [eauto with paco|..] | eapply pcpn14_clo; [|eapply H|]; [eauto with paco|..]]
  end.
Ltac uclo H := repeat red; under_forall ltac:(uclo_ H).

(** ** ucofix CIH [with r]
*)

Tactic Notation "ucofix" ident(CIH) "with" ident(r) :=
  repeat red;
  generalize _paco_mark_cons; intros;
  match goal with
  | [|- context[dcpn0]] =>
    try left;
    paco_revert_hyp _paco_mark;
    pcofix CIH using @pcpn0_cofix with r; [eauto with paco|]
  | [|- context[dcpn1]] =>
    try left;
    paco_revert_hyp _paco_mark;
    pcofix CIH using @pcpn1_cofix with r; [eauto with paco|]
  | [|- context[dcpn2]] =>
    try left;
    paco_revert_hyp _paco_mark;
    pcofix CIH using @pcpn2_cofix with r; [eauto with paco|]
  | [|- context[dcpn3]] =>
    try left;
    paco_revert_hyp _paco_mark;
    pcofix CIH using @pcpn3_cofix with r; [eauto with paco|]
  | [|- context[dcpn4]] =>
    try left;
    paco_revert_hyp _paco_mark;
    pcofix CIH using @pcpn4_cofix with r; [eauto with paco|]
  | [|- context[dcpn5]] =>
    try left;
    paco_revert_hyp _paco_mark;
    pcofix CIH using @pcpn5_cofix with r; [eauto with paco|]
  | [|- context[dcpn6]] =>
    try left;
    paco_revert_hyp _paco_mark;
    pcofix CIH using @pcpn6_cofix with r; [eauto with paco|]
  | [|- context[dcpn7]] =>
    try left;
    paco_revert_hyp _paco_mark;
    pcofix CIH using @pcpn7_cofix with r; [eauto with paco|]
  | [|- context[dcpn8]] =>
    try left;
    paco_revert_hyp _paco_mark;
    pcofix CIH using @pcpn8_cofix with r; [eauto with paco|]
  | [|- context[dcpn9]] =>
    try left;
    paco_revert_hyp _paco_mark;
    pcofix CIH using @pcpn9_cofix with r; [eauto with paco|]
  | [|- context[dcpn10]] =>
    try left;
    paco_revert_hyp _paco_mark;
    pcofix CIH using @pcpn10_cofix with r; [eauto with paco|]
  | [|- context[dcpn11]] =>
    try left;
    paco_revert_hyp _paco_mark;
    pcofix CIH using @pcpn11_cofix with r; [eauto with paco|]
  | [|- context[dcpn12]] =>
    try left;
    paco_revert_hyp _paco_mark;
    pcofix CIH using @pcpn12_cofix with r; [eauto with paco|]
  | [|- context[dcpn13]] =>
    try left;
    paco_revert_hyp _paco_mark;
    pcofix CIH using @pcpn13_cofix with r; [eauto with paco|]
  | [|- context[dcpn14]] =>
    try left;
    paco_revert_hyp _paco_mark;
    pcofix CIH using @pcpn14_cofix with r; [eauto with paco|]
  end.
Tactic Notation "ucofix" ident(CIH) := ucofix CIH with r.

