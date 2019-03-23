Require Import pacotac_internal pacotac pacoall cpnall wcpnall.

(** ** winit
*)

Tactic Notation "winit_" :=
  match goal with
  | [|- context[cpn0]] => eapply wcpn0_init; [eauto with paco|]
  | [|- context[cpn1]] => eapply wcpn1_init; [eauto with paco|]
  | [|- context[cpn2]] => eapply wcpn2_init; [eauto with paco|]
  | [|- context[cpn3]] => eapply wcpn3_init; [eauto with paco|]
  | [|- context[cpn4]] => eapply wcpn4_init; [eauto with paco|]
  | [|- context[cpn5]] => eapply wcpn5_init; [eauto with paco|]
  | [|- context[cpn6]] => eapply wcpn6_init; [eauto with paco|]
  | [|- context[cpn7]] => eapply wcpn7_init; [eauto with paco|]
  | [|- context[cpn8]] => eapply wcpn8_init; [eauto with paco|]
  | [|- context[cpn9]] => eapply wcpn9_init; [eauto with paco|]
  | [|- context[cpn10]] => eapply wcpn10_init; [eauto with paco|]
  | [|- context[cpn11]] => eapply wcpn11_init; [eauto with paco|]
  | [|- context[cpn12]] => eapply wcpn12_init; [eauto with paco|]
  | [|- context[cpn13]] => eapply wcpn13_init; [eauto with paco|]
  | [|- context[cpn14]] => eapply wcpn14_init; [eauto with paco|]
  | [|- context[cpn15]] => eapply wcpn15_init; [eauto with paco|]
  end.
Ltac winit := repeat red; under_forall ltac:(winit_).

(** ** wfinal
*)

Tactic Notation "wfinal_" :=
  match goal with
  | [|- context[wcpn0]]  => eapply wcpn0_final
  | [|- context[wcpn1]]  => eapply wcpn1_final
  | [|- context[wcpn2]]  => eapply wcpn2_final
  | [|- context[wcpn3]]  => eapply wcpn3_final
  | [|- context[wcpn4]]  => eapply wcpn4_final
  | [|- context[wcpn5]]  => eapply wcpn5_final
  | [|- context[wcpn6]]  => eapply wcpn6_final
  | [|- context[wcpn7]]  => eapply wcpn7_final
  | [|- context[wcpn8]]  => eapply wcpn8_final
  | [|- context[wcpn9]]  => eapply wcpn9_final
  | [|- context[wcpn10]]  => eapply wcpn10_final
  | [|- context[wcpn11]]  => eapply wcpn11_final
  | [|- context[wcpn12]]  => eapply wcpn12_final
  | [|- context[wcpn13]]  => eapply wcpn13_final
  | [|- context[wcpn14]]  => eapply wcpn14_final
  | [|- context[wcpn15]]  => eapply wcpn15_final
  end.
Ltac wfinal := repeat red; under_forall ltac:(wfinal_).

(** ** wunfold H
*)

Ltac wunfold H :=
  repeat red in H;
  let G := type of H in
  match G with
  | context[wcpn0] => eapply wcpn0_unfold in H; [|eauto with paco]
  | context[wcpn1] => eapply wcpn1_unfold in H; [|eauto with paco]
  | context[wcpn2] => eapply wcpn2_unfold in H; [|eauto with paco]
  | context[wcpn3] => eapply wcpn3_unfold in H; [|eauto with paco]
  | context[wcpn4] => eapply wcpn4_unfold in H; [|eauto with paco]
  | context[wcpn5] => eapply wcpn5_unfold in H; [|eauto with paco]
  | context[wcpn6] => eapply wcpn6_unfold in H; [|eauto with paco]
  | context[wcpn7] => eapply wcpn7_unfold in H; [|eauto with paco]
  | context[wcpn8] => eapply wcpn8_unfold in H; [|eauto with paco]
  | context[wcpn9] => eapply wcpn9_unfold in H; [|eauto with paco]
  | context[wcpn10] => eapply wcpn10_unfold in H; [|eauto with paco]
  | context[wcpn11] => eapply wcpn11_unfold in H; [|eauto with paco]
  | context[wcpn12] => eapply wcpn12_unfold in H; [|eauto with paco]
  | context[wcpn13] => eapply wcpn13_unfold in H; [|eauto with paco]
  | context[wcpn14] => eapply wcpn14_unfold in H; [|eauto with paco]
  | context[wcpn15] => eapply wcpn15_unfold in H; [|eauto with paco]
  end.

(** ** wbase
*)

Tactic Notation "wbase_" :=
  match goal with
  | [|- context[wcpn0]] => eapply wcpn0_base
  | [|- context[wcpn1]] => eapply wcpn1_base
  | [|- context[wcpn2]] => eapply wcpn2_base
  | [|- context[wcpn3]] => eapply wcpn3_base
  | [|- context[wcpn4]] => eapply wcpn4_base
  | [|- context[wcpn5]] => eapply wcpn5_base
  | [|- context[wcpn6]] => eapply wcpn6_base
  | [|- context[wcpn7]] => eapply wcpn7_base
  | [|- context[wcpn8]] => eapply wcpn8_base
  | [|- context[wcpn9]] => eapply wcpn9_base
  | [|- context[wcpn10]] => eapply wcpn10_base
  | [|- context[wcpn11]] => eapply wcpn11_base
  | [|- context[wcpn12]] => eapply wcpn12_base
  | [|- context[wcpn13]] => eapply wcpn13_base
  | [|- context[wcpn14]] => eapply wcpn14_base
  | [|- context[wcpn15]] => eapply wcpn15_base
  end.
Ltac wbase := repeat red; under_forall ltac:(wbase_).

(** ** wcpn
*)

Tactic Notation "wcpn_" :=
  match goal with
  | [|- context[wcpn0]] => eapply wcpn0_cpn; [eauto with paco|]
  | [|- context[wcpn1]] => eapply wcpn1_cpn; [eauto with paco|]
  | [|- context[wcpn2]] => eapply wcpn2_cpn; [eauto with paco|]
  | [|- context[wcpn3]] => eapply wcpn3_cpn; [eauto with paco|]
  | [|- context[wcpn4]] => eapply wcpn4_cpn; [eauto with paco|]
  | [|- context[wcpn5]] => eapply wcpn5_cpn; [eauto with paco|]
  | [|- context[wcpn6]] => eapply wcpn6_cpn; [eauto with paco|]
  | [|- context[wcpn7]] => eapply wcpn7_cpn; [eauto with paco|]
  | [|- context[wcpn8]] => eapply wcpn8_cpn; [eauto with paco|]
  | [|- context[wcpn9]] => eapply wcpn9_cpn; [eauto with paco|]
  | [|- context[wcpn10]] => eapply wcpn10_cpn; [eauto with paco|]
  | [|- context[wcpn11]] => eapply wcpn11_cpn; [eauto with paco|]
  | [|- context[wcpn12]] => eapply wcpn12_cpn; [eauto with paco|]
  | [|- context[wcpn13]] => eapply wcpn13_cpn; [eauto with paco|]
  | [|- context[wcpn14]] => eapply wcpn14_cpn; [eauto with paco|]
  | [|- context[wcpn15]] => eapply wcpn15_cpn; [eauto with paco|]
  end.
Ltac wcpn := repeat red; under_forall ltac:(wcpn_).

(** ** wstep
*)

Tactic Notation "wstep_" :=
  match goal with
  | [|- context[wcpn0]] => eapply wcpn0_step; [eauto with paco|]
  | [|- context[wcpn1]] => eapply wcpn1_step; [eauto with paco|]
  | [|- context[wcpn2]] => eapply wcpn2_step; [eauto with paco|]
  | [|- context[wcpn3]] => eapply wcpn3_step; [eauto with paco|]
  | [|- context[wcpn4]] => eapply wcpn4_step; [eauto with paco|]
  | [|- context[wcpn5]] => eapply wcpn5_step; [eauto with paco|]
  | [|- context[wcpn6]] => eapply wcpn6_step; [eauto with paco|]
  | [|- context[wcpn7]] => eapply wcpn7_step; [eauto with paco|]
  | [|- context[wcpn8]] => eapply wcpn8_step; [eauto with paco|]
  | [|- context[wcpn9]] => eapply wcpn9_step; [eauto with paco|]
  | [|- context[wcpn10]] => eapply wcpn10_step; [eauto with paco|]
  | [|- context[wcpn11]] => eapply wcpn11_step; [eauto with paco|]
  | [|- context[wcpn12]] => eapply wcpn12_step; [eauto with paco|]
  | [|- context[wcpn13]] => eapply wcpn13_step; [eauto with paco|]
  | [|- context[wcpn14]] => eapply wcpn14_step; [eauto with paco|]
  | [|- context[wcpn15]] => eapply wcpn15_step; [eauto with paco|]
  end.
Ltac wstep := repeat red; under_forall ltac:(wstep_).

(** ** wclo H
*)

Tactic Notation "wclo_" constr(H) :=
  match goal with
  | [|- context[wcpn0]]  => eapply wcpn0_clo; [|eapply H|]; [eauto with paco|]
  | [|- context[wcpn1]]  => eapply wcpn1_clo; [|eapply H|]; [eauto with paco|]
  | [|- context[wcpn2]]  => eapply wcpn2_clo; [|eapply H|]; [eauto with paco|]
  | [|- context[wcpn3]]  => eapply wcpn3_clo; [|eapply H|]; [eauto with paco|]
  | [|- context[wcpn4]]  => eapply wcpn4_clo; [|eapply H|]; [eauto with paco|]
  | [|- context[wcpn5]]  => eapply wcpn5_clo; [|eapply H|]; [eauto with paco|]
  | [|- context[wcpn6]]  => eapply wcpn6_clo; [|eapply H|]; [eauto with paco|]
  | [|- context[wcpn7]]  => eapply wcpn7_clo; [|eapply H|]; [eauto with paco|]
  | [|- context[wcpn8]]  => eapply wcpn8_clo; [|eapply H|]; [eauto with paco|]
  | [|- context[wcpn9]]  => eapply wcpn9_clo; [|eapply H|]; [eauto with paco|]
  | [|- context[wcpn10]]  => eapply wcpn10_clo; [|eapply H|]; [eauto with paco|]
  | [|- context[wcpn11]]  => eapply wcpn11_clo; [|eapply H|]; [eauto with paco|]
  | [|- context[wcpn12]]  => eapply wcpn12_clo; [|eapply H|]; [eauto with paco|]
  | [|- context[wcpn13]]  => eapply wcpn13_clo; [|eapply H|]; [eauto with paco|]
  | [|- context[wcpn14]]  => eapply wcpn14_clo; [|eapply H|]; [eauto with paco|]
  | [|- context[wcpn15]]  => eapply wcpn15_clo; [|eapply H|]; [eauto with paco|]
  end.
Ltac wclo H := repeat red; under_forall ltac:(wclo_ H).

(** ** wcofix CIH [with r]
*)

Tactic Notation "wcofix" ident(CIH) "with" ident(r) :=
  repeat red;
  generalize _paco_mark_cons; intros;
  match goal with
  | [|- context[wcpn0]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using @wcpn0_cofix with r; [eauto with paco|eauto with paco|]
  | [|- context[wcpn1]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using @wcpn1_cofix with r; [eauto with paco|eauto with paco|]
  | [|- context[wcpn2]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using @wcpn2_cofix with r; [eauto with paco|eauto with paco|]
  | [|- context[wcpn3]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using @wcpn3_cofix with r; [eauto with paco|eauto with paco|]
  | [|- context[wcpn4]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using @wcpn4_cofix with r; [eauto with paco|eauto with paco|]
  | [|- context[wcpn5]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using @wcpn5_cofix with r; [eauto with paco|eauto with paco|]
  | [|- context[wcpn6]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using @wcpn6_cofix with r; [eauto with paco|eauto with paco|]
  | [|- context[wcpn7]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using @wcpn7_cofix with r; [eauto with paco|eauto with paco|]
  | [|- context[wcpn8]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using @wcpn8_cofix with r; [eauto with paco|eauto with paco|]
  | [|- context[wcpn9]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using @wcpn9_cofix with r; [eauto with paco|eauto with paco|]
  | [|- context[wcpn10]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using @wcpn10_cofix with r; [eauto with paco|eauto with paco|]
  | [|- context[wcpn11]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using @wcpn11_cofix with r; [eauto with paco|eauto with paco|]
  | [|- context[wcpn12]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using @wcpn12_cofix with r; [eauto with paco|eauto with paco|]
  | [|- context[wcpn13]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using @wcpn13_cofix with r; [eauto with paco|eauto with paco|]
  | [|- context[wcpn14]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using @wcpn14_cofix with r; [eauto with paco|eauto with paco|]
  | [|- context[wcpn15]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using @wcpn15_cofix with r; [eauto with paco|eauto with paco|]
  end.
Tactic Notation "wcofix" ident(CIH) := wcofix CIH with r.

