Require Import pacotac_internal pacotac pacoall cpnall gcpnall.

(** ** ginit
*)

Tactic Notation "ginit_" :=
  match goal with
  | [|- context[cpn0]] => eapply gcpn0_init; [eauto with paco|]
  | [|- context[cpn1]] => eapply gcpn1_init; [eauto with paco|]
  | [|- context[cpn2]] => eapply gcpn2_init; [eauto with paco|]
  | [|- context[cpn3]] => eapply gcpn3_init; [eauto with paco|]
  | [|- context[cpn4]] => eapply gcpn4_init; [eauto with paco|]
  | [|- context[cpn5]] => eapply gcpn5_init; [eauto with paco|]
  | [|- context[cpn6]] => eapply gcpn6_init; [eauto with paco|]
  | [|- context[cpn7]] => eapply gcpn7_init; [eauto with paco|]
  | [|- context[cpn8]] => eapply gcpn8_init; [eauto with paco|]
  | [|- context[cpn9]] => eapply gcpn9_init; [eauto with paco|]
  | [|- context[cpn10]] => eapply gcpn10_init; [eauto with paco|]
  | [|- context[cpn11]] => eapply gcpn11_init; [eauto with paco|]
  | [|- context[cpn12]] => eapply gcpn12_init; [eauto with paco|]
  | [|- context[cpn13]] => eapply gcpn13_init; [eauto with paco|]
  | [|- context[cpn14]] => eapply gcpn14_init; [eauto with paco|]
  end.
Ltac ginit := repeat red; under_forall ltac:(ginit_).

(** ** gfinal
*)

Tactic Notation "gfinal_" :=
  match goal with
  | [|- context[gcpn0]]  => eapply gcpn0_final
  | [|- context[gcpn1]]  => eapply gcpn1_final
  | [|- context[gcpn2]]  => eapply gcpn2_final
  | [|- context[gcpn3]]  => eapply gcpn3_final
  | [|- context[gcpn4]]  => eapply gcpn4_final
  | [|- context[gcpn5]]  => eapply gcpn5_final
  | [|- context[gcpn6]]  => eapply gcpn6_final
  | [|- context[gcpn7]]  => eapply gcpn7_final
  | [|- context[gcpn8]]  => eapply gcpn8_final
  | [|- context[gcpn9]]  => eapply gcpn9_final
  | [|- context[gcpn10]]  => eapply gcpn10_final
  | [|- context[gcpn11]]  => eapply gcpn11_final
  | [|- context[gcpn12]]  => eapply gcpn12_final
  | [|- context[gcpn13]]  => eapply gcpn13_final
  | [|- context[gcpn14]]  => eapply gcpn14_final
  end.
Ltac gfinal := repeat red; under_forall ltac:(gfinal_).

(** ** gunfold H
*)

Ltac gunfold H :=
  repeat red in H;
  let G := type of H in
  match G with
  | context[gcpn0] => eapply gcpn0_unfold in H; [|eauto with paco]
  | context[gcpn1] => eapply gcpn1_unfold in H; [|eauto with paco]
  | context[gcpn2] => eapply gcpn2_unfold in H; [|eauto with paco]
  | context[gcpn3] => eapply gcpn3_unfold in H; [|eauto with paco]
  | context[gcpn4] => eapply gcpn4_unfold in H; [|eauto with paco]
  | context[gcpn5] => eapply gcpn5_unfold in H; [|eauto with paco]
  | context[gcpn6] => eapply gcpn6_unfold in H; [|eauto with paco]
  | context[gcpn7] => eapply gcpn7_unfold in H; [|eauto with paco]
  | context[gcpn8] => eapply gcpn8_unfold in H; [|eauto with paco]
  | context[gcpn9] => eapply gcpn9_unfold in H; [|eauto with paco]
  | context[gcpn10] => eapply gcpn10_unfold in H; [|eauto with paco]
  | context[gcpn11] => eapply gcpn11_unfold in H; [|eauto with paco]
  | context[gcpn12] => eapply gcpn12_unfold in H; [|eauto with paco]
  | context[gcpn13] => eapply gcpn13_unfold in H; [|eauto with paco]
  | context[gcpn14] => eapply gcpn14_unfold in H; [|eauto with paco]
  end.

(** ** gbase
*)

Tactic Notation "gbase_" :=
  match goal with
  | [|- context[gcpn0]] => eapply gcpn0_base
  | [|- context[gcpn1]] => eapply gcpn1_base
  | [|- context[gcpn2]] => eapply gcpn2_base
  | [|- context[gcpn3]] => eapply gcpn3_base
  | [|- context[gcpn4]] => eapply gcpn4_base
  | [|- context[gcpn5]] => eapply gcpn5_base
  | [|- context[gcpn6]] => eapply gcpn6_base
  | [|- context[gcpn7]] => eapply gcpn7_base
  | [|- context[gcpn8]] => eapply gcpn8_base
  | [|- context[gcpn9]] => eapply gcpn9_base
  | [|- context[gcpn10]] => eapply gcpn10_base
  | [|- context[gcpn11]] => eapply gcpn11_base
  | [|- context[gcpn12]] => eapply gcpn12_base
  | [|- context[gcpn13]] => eapply gcpn13_base
  | [|- context[gcpn14]] => eapply gcpn14_base
  end.
Ltac gbase := repeat red; under_forall ltac:(gbase_).

(** ** gcpn
*)

Tactic Notation "gcpn_" :=
  match goal with
  | [|- context[gcpn0]] => eapply gcpn0_cpn; [eauto with paco|]
  | [|- context[gcpn1]] => eapply gcpn1_cpn; [eauto with paco|]
  | [|- context[gcpn2]] => eapply gcpn2_cpn; [eauto with paco|]
  | [|- context[gcpn3]] => eapply gcpn3_cpn; [eauto with paco|]
  | [|- context[gcpn4]] => eapply gcpn4_cpn; [eauto with paco|]
  | [|- context[gcpn5]] => eapply gcpn5_cpn; [eauto with paco|]
  | [|- context[gcpn6]] => eapply gcpn6_cpn; [eauto with paco|]
  | [|- context[gcpn7]] => eapply gcpn7_cpn; [eauto with paco|]
  | [|- context[gcpn8]] => eapply gcpn8_cpn; [eauto with paco|]
  | [|- context[gcpn9]] => eapply gcpn9_cpn; [eauto with paco|]
  | [|- context[gcpn10]] => eapply gcpn10_cpn; [eauto with paco|]
  | [|- context[gcpn11]] => eapply gcpn11_cpn; [eauto with paco|]
  | [|- context[gcpn12]] => eapply gcpn12_cpn; [eauto with paco|]
  | [|- context[gcpn13]] => eapply gcpn13_cpn; [eauto with paco|]
  | [|- context[gcpn14]] => eapply gcpn14_cpn; [eauto with paco|]
  end.
Ltac gcpn := repeat red; under_forall ltac:(gcpn_).

(** ** gstep
*)

Tactic Notation "gstep_" :=
  match goal with
  | [|- context[gcpn0]] => eapply gcpn0_step; [eauto with paco|]
  | [|- context[gcpn1]] => eapply gcpn1_step; [eauto with paco|]
  | [|- context[gcpn2]] => eapply gcpn2_step; [eauto with paco|]
  | [|- context[gcpn3]] => eapply gcpn3_step; [eauto with paco|]
  | [|- context[gcpn4]] => eapply gcpn4_step; [eauto with paco|]
  | [|- context[gcpn5]] => eapply gcpn5_step; [eauto with paco|]
  | [|- context[gcpn6]] => eapply gcpn6_step; [eauto with paco|]
  | [|- context[gcpn7]] => eapply gcpn7_step; [eauto with paco|]
  | [|- context[gcpn8]] => eapply gcpn8_step; [eauto with paco|]
  | [|- context[gcpn9]] => eapply gcpn9_step; [eauto with paco|]
  | [|- context[gcpn10]] => eapply gcpn10_step; [eauto with paco|]
  | [|- context[gcpn11]] => eapply gcpn11_step; [eauto with paco|]
  | [|- context[gcpn12]] => eapply gcpn12_step; [eauto with paco|]
  | [|- context[gcpn13]] => eapply gcpn13_step; [eauto with paco|]
  | [|- context[gcpn14]] => eapply gcpn14_step; [eauto with paco|]
  end.
Ltac gstep := repeat red; under_forall ltac:(gstep_).

(** ** gclo H
*)

Tactic Notation "gclo_" constr(H) :=
  match goal with
  | [|- context[gcpn0]]  => eapply gcpn0_clo; [|eapply H|]; [eauto with paco|]
  | [|- context[gcpn1]]  => eapply gcpn1_clo; [|eapply H|]; [eauto with paco|]
  | [|- context[gcpn2]]  => eapply gcpn2_clo; [|eapply H|]; [eauto with paco|]
  | [|- context[gcpn3]]  => eapply gcpn3_clo; [|eapply H|]; [eauto with paco|]
  | [|- context[gcpn4]]  => eapply gcpn4_clo; [|eapply H|]; [eauto with paco|]
  | [|- context[gcpn5]]  => eapply gcpn5_clo; [|eapply H|]; [eauto with paco|]
  | [|- context[gcpn6]]  => eapply gcpn6_clo; [|eapply H|]; [eauto with paco|]
  | [|- context[gcpn7]]  => eapply gcpn7_clo; [|eapply H|]; [eauto with paco|]
  | [|- context[gcpn8]]  => eapply gcpn8_clo; [|eapply H|]; [eauto with paco|]
  | [|- context[gcpn9]]  => eapply gcpn9_clo; [|eapply H|]; [eauto with paco|]
  | [|- context[gcpn10]]  => eapply gcpn10_clo; [|eapply H|]; [eauto with paco|]
  | [|- context[gcpn11]]  => eapply gcpn11_clo; [|eapply H|]; [eauto with paco|]
  | [|- context[gcpn12]]  => eapply gcpn12_clo; [|eapply H|]; [eauto with paco|]
  | [|- context[gcpn13]]  => eapply gcpn13_clo; [|eapply H|]; [eauto with paco|]
  | [|- context[gcpn14]]  => eapply gcpn14_clo; [|eapply H|]; [eauto with paco|]
  end.
Ltac gclo H := repeat red; under_forall ltac:(gclo_ H).

(** ** gcofix CIH [with r]
*)

Tactic Notation "gcofix" ident(CIH) "with" ident(r) :=
  repeat red;
  generalize _paco_mark_cons; intros;
  match goal with
  | [|- context[gcpn0]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using @gcpn0_cofix with r; [eauto with paco|eauto with paco; try contradiction|]
  | [|- context[gcpn1]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using @gcpn1_cofix with r; [eauto with paco|eauto with paco; try contradiction|]
  | [|- context[gcpn2]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using @gcpn2_cofix with r; [eauto with paco|eauto with paco; try contradiction|]
  | [|- context[gcpn3]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using @gcpn3_cofix with r; [eauto with paco|eauto with paco; try contradiction|]
  | [|- context[gcpn4]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using @gcpn4_cofix with r; [eauto with paco|eauto with paco; try contradiction|]
  | [|- context[gcpn5]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using @gcpn5_cofix with r; [eauto with paco|eauto with paco; try contradiction|]
  | [|- context[gcpn6]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using @gcpn6_cofix with r; [eauto with paco|eauto with paco; try contradiction|]
  | [|- context[gcpn7]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using @gcpn7_cofix with r; [eauto with paco|eauto with paco; try contradiction|]
  | [|- context[gcpn8]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using @gcpn8_cofix with r; [eauto with paco|eauto with paco; try contradiction|]
  | [|- context[gcpn9]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using @gcpn9_cofix with r; [eauto with paco|eauto with paco; try contradiction|]
  | [|- context[gcpn10]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using @gcpn10_cofix with r; [eauto with paco|eauto with paco; try contradiction|]
  | [|- context[gcpn11]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using @gcpn11_cofix with r; [eauto with paco|eauto with paco; try contradiction|]
  | [|- context[gcpn12]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using @gcpn12_cofix with r; [eauto with paco|eauto with paco; try contradiction|]
  | [|- context[gcpn13]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using @gcpn13_cofix with r; [eauto with paco|eauto with paco; try contradiction|]
  | [|- context[gcpn14]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using @gcpn14_cofix with r; [eauto with paco|eauto with paco; try contradiction|]
  end.
Tactic Notation "gcofix" ident(CIH) := gcofix CIH with r.

