Require Import pacotac_internal pacotac pacoall cpacoall.

(** ** cinit
*)

Tactic Notation "cinit_" :=
  match goal with
  | [|- context[paco0]] => eapply cpaco0_init; [eauto with paco|eauto with paco|]
  | [|- context[paco1]] => eapply cpaco1_init; [eauto with paco|eauto with paco|]
  | [|- context[paco2]] => eapply cpaco2_init; [eauto with paco|eauto with paco|]
  | [|- context[paco3]] => eapply cpaco3_init; [eauto with paco|eauto with paco|]
  | [|- context[paco4]] => eapply cpaco4_init; [eauto with paco|eauto with paco|]
  | [|- context[paco5]] => eapply cpaco5_init; [eauto with paco|eauto with paco|]
  | [|- context[paco6]] => eapply cpaco6_init; [eauto with paco|eauto with paco|]
  | [|- context[paco7]] => eapply cpaco7_init; [eauto with paco|eauto with paco|]
  | [|- context[paco8]] => eapply cpaco8_init; [eauto with paco|eauto with paco|]
  | [|- context[paco9]] => eapply cpaco9_init; [eauto with paco|eauto with paco|]
  | [|- context[paco10]] => eapply cpaco10_init; [eauto with paco|eauto with paco|]
  | [|- context[paco11]] => eapply cpaco11_init; [eauto with paco|eauto with paco|]
  | [|- context[paco12]] => eapply cpaco12_init; [eauto with paco|eauto with paco|]
  | [|- context[paco13]] => eapply cpaco13_init; [eauto with paco|eauto with paco|]
  | [|- context[paco14]] => eapply cpaco14_init; [eauto with paco|eauto with paco|]
  end.
Ltac cinit := repeat red; under_forall ltac:(cinit_).

(** ** cunfold H
*)

Ltac cunfold H :=
  repeat red in H;
  let G := type of H in
  match G with
  | context[cpaco0] => eapply cpaco0_unfold in H; [|eauto with paco|eauto with paco]
  | context[cpaco1] => eapply cpaco1_unfold in H; [|eauto with paco|eauto with paco]
  | context[cpaco2] => eapply cpaco2_unfold in H; [|eauto with paco|eauto with paco]
  | context[cpaco3] => eapply cpaco3_unfold in H; [|eauto with paco|eauto with paco]
  | context[cpaco4] => eapply cpaco4_unfold in H; [|eauto with paco|eauto with paco]
  | context[cpaco5] => eapply cpaco5_unfold in H; [|eauto with paco|eauto with paco]
  | context[cpaco6] => eapply cpaco6_unfold in H; [|eauto with paco|eauto with paco]
  | context[cpaco7] => eapply cpaco7_unfold in H; [|eauto with paco|eauto with paco]
  | context[cpaco8] => eapply cpaco8_unfold in H; [|eauto with paco|eauto with paco]
  | context[cpaco9] => eapply cpaco9_unfold in H; [|eauto with paco|eauto with paco]
  | context[cpaco10] => eapply cpaco10_unfold in H; [|eauto with paco|eauto with paco]
  | context[cpaco11] => eapply cpaco11_unfold in H; [|eauto with paco|eauto with paco]
  | context[cpaco12] => eapply cpaco12_unfold in H; [|eauto with paco|eauto with paco]
  | context[cpaco13] => eapply cpaco13_unfold in H; [|eauto with paco|eauto with paco]
  | context[cpaco14] => eapply cpaco14_unfold in H; [|eauto with paco|eauto with paco]
  end.

(** ** cbase
*)

Tactic Notation "cbase_" :=
  match goal with
  | [|- context[cpaco0]] => eapply cpaco0_base
  | [|- context[cpaco1]] => eapply cpaco1_base
  | [|- context[cpaco2]] => eapply cpaco2_base
  | [|- context[cpaco3]] => eapply cpaco3_base
  | [|- context[cpaco4]] => eapply cpaco4_base
  | [|- context[cpaco5]] => eapply cpaco5_base
  | [|- context[cpaco6]] => eapply cpaco6_base
  | [|- context[cpaco7]] => eapply cpaco7_base
  | [|- context[cpaco8]] => eapply cpaco8_base
  | [|- context[cpaco9]] => eapply cpaco9_base
  | [|- context[cpaco10]] => eapply cpaco10_base
  | [|- context[cpaco11]] => eapply cpaco11_base
  | [|- context[cpaco12]] => eapply cpaco12_base
  | [|- context[cpaco13]] => eapply cpaco13_base
  | [|- context[cpaco14]] => eapply cpaco14_base
  end.
Ltac cbase := repeat red; under_forall ltac:(cbase_).

(** ** cstep
*)

Tactic Notation "cstep_" :=
  match goal with
  | [|- context[cpaco0]] => eapply cpaco0_step; [eauto with paco|]
  | [|- context[cpaco1]] => eapply cpaco1_step; [eauto with paco|]
  | [|- context[cpaco2]] => eapply cpaco2_step; [eauto with paco|]
  | [|- context[cpaco3]] => eapply cpaco3_step; [eauto with paco|]
  | [|- context[cpaco4]] => eapply cpaco4_step; [eauto with paco|]
  | [|- context[cpaco5]] => eapply cpaco5_step; [eauto with paco|]
  | [|- context[cpaco6]] => eapply cpaco6_step; [eauto with paco|]
  | [|- context[cpaco7]] => eapply cpaco7_step; [eauto with paco|]
  | [|- context[cpaco8]] => eapply cpaco8_step; [eauto with paco|]
  | [|- context[cpaco9]] => eapply cpaco9_step; [eauto with paco|]
  | [|- context[cpaco10]] => eapply cpaco10_step; [eauto with paco|]
  | [|- context[cpaco11]] => eapply cpaco11_step; [eauto with paco|]
  | [|- context[cpaco12]] => eapply cpaco12_step; [eauto with paco|]
  | [|- context[cpaco13]] => eapply cpaco13_step; [eauto with paco|]
  | [|- context[cpaco14]] => eapply cpaco14_step; [eauto with paco|]
  end.
Ltac cstep := repeat red; under_forall ltac:(cstep_).

(** ** cupaco
*)

Tactic Notation "cupaco_" :=
  match goal with
  | [|- context[cpaco0]] => eapply cpaco0_cupaco; [eauto with paco|eauto with paco|]
  | [|- context[cpaco1]] => eapply cpaco1_cupaco; [eauto with paco|eauto with paco|]
  | [|- context[cpaco2]] => eapply cpaco2_cupaco; [eauto with paco|eauto with paco|]
  | [|- context[cpaco3]] => eapply cpaco3_cupaco; [eauto with paco|eauto with paco|]
  | [|- context[cpaco4]] => eapply cpaco4_cupaco; [eauto with paco|eauto with paco|]
  | [|- context[cpaco5]] => eapply cpaco5_cupaco; [eauto with paco|eauto with paco|]
  | [|- context[cpaco6]] => eapply cpaco6_cupaco; [eauto with paco|eauto with paco|]
  | [|- context[cpaco7]] => eapply cpaco7_cupaco; [eauto with paco|eauto with paco|]
  | [|- context[cpaco8]] => eapply cpaco8_cupaco; [eauto with paco|eauto with paco|]
  | [|- context[cpaco9]] => eapply cpaco9_cupaco; [eauto with paco|eauto with paco|]
  | [|- context[cpaco10]] => eapply cpaco10_cupaco; [eauto with paco|eauto with paco|]
  | [|- context[cpaco11]] => eapply cpaco11_cupaco; [eauto with paco|eauto with paco|]
  | [|- context[cpaco12]] => eapply cpaco12_cupaco; [eauto with paco|eauto with paco|]
  | [|- context[cpaco13]] => eapply cpaco13_cupaco; [eauto with paco|eauto with paco|]
  | [|- context[cpaco14]] => eapply cpaco14_cupaco; [eauto with paco|eauto with paco|]
  end.
Ltac cupaco := repeat red; under_forall ltac:(cupaco_).

(** ** cclo H
*)

Tactic Notation "cclo_" constr(H) :=
  match goal with
  | [|- context[cpaco0]]  => eapply cpaco0_uclo; [| |eapply H|]; [eauto with paco|eauto with paco|..]
  | [|- context[cpaco1]]  => eapply cpaco1_uclo; [| |eapply H|]; [eauto with paco|eauto with paco|..]
  | [|- context[cpaco2]]  => eapply cpaco2_uclo; [| |eapply H|]; [eauto with paco|eauto with paco|..]
  | [|- context[cpaco3]]  => eapply cpaco3_uclo; [| |eapply H|]; [eauto with paco|eauto with paco|..]
  | [|- context[cpaco4]]  => eapply cpaco4_uclo; [| |eapply H|]; [eauto with paco|eauto with paco|..]
  | [|- context[cpaco5]]  => eapply cpaco5_uclo; [| |eapply H|]; [eauto with paco|eauto with paco|..]
  | [|- context[cpaco6]]  => eapply cpaco6_uclo; [| |eapply H|]; [eauto with paco|eauto with paco|..]
  | [|- context[cpaco7]]  => eapply cpaco7_uclo; [| |eapply H|]; [eauto with paco|eauto with paco|..]
  | [|- context[cpaco8]]  => eapply cpaco8_uclo; [| |eapply H|]; [eauto with paco|eauto with paco|..]
  | [|- context[cpaco9]]  => eapply cpaco9_uclo; [| |eapply H|]; [eauto with paco|eauto with paco|..]
  | [|- context[cpaco10]]  => eapply cpaco10_uclo; [| |eapply H|]; [eauto with paco|eauto with paco|..]
  | [|- context[cpaco11]]  => eapply cpaco11_uclo; [| |eapply H|]; [eauto with paco|eauto with paco|..]
  | [|- context[cpaco12]]  => eapply cpaco12_uclo; [| |eapply H|]; [eauto with paco|eauto with paco|..]
  | [|- context[cpaco13]]  => eapply cpaco13_uclo; [| |eapply H|]; [eauto with paco|eauto with paco|..]
  | [|- context[cpaco14]]  => eapply cpaco14_uclo; [| |eapply H|]; [eauto with paco|eauto with paco|..]
  end.
Ltac cclo H := repeat red; under_forall ltac:(cclo_ H).

(** ** ccofix CIH [with r]
*)

Tactic Notation "ccofix" ident(CIH) "with" ident(r) :=
  repeat red;
  generalize _paco_mark_cons; intros;
  match goal with
  | [|- context[cpaco0]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using @cpaco0_cofix with r; [eauto with paco|eauto with paco|eauto with paco; try contradiction|]
  | [|- context[cpaco1]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using @cpaco1_cofix with r; [eauto with paco|eauto with paco|eauto with paco; try contradiction|]
  | [|- context[cpaco2]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using @cpaco2_cofix with r; [eauto with paco|eauto with paco|eauto with paco; try contradiction|]
  | [|- context[cpaco3]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using @cpaco3_cofix with r; [eauto with paco|eauto with paco|eauto with paco; try contradiction|]
  | [|- context[cpaco4]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using @cpaco4_cofix with r; [eauto with paco|eauto with paco|eauto with paco; try contradiction|]
  | [|- context[cpaco5]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using @cpaco5_cofix with r; [eauto with paco|eauto with paco|eauto with paco; try contradiction|]
  | [|- context[cpaco6]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using @cpaco6_cofix with r; [eauto with paco|eauto with paco|eauto with paco; try contradiction|]
  | [|- context[cpaco7]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using @cpaco7_cofix with r; [eauto with paco|eauto with paco|eauto with paco; try contradiction|]
  | [|- context[cpaco8]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using @cpaco8_cofix with r; [eauto with paco|eauto with paco|eauto with paco; try contradiction|]
  | [|- context[cpaco9]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using @cpaco9_cofix with r; [eauto with paco|eauto with paco|eauto with paco; try contradiction|]
  | [|- context[cpaco10]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using @cpaco10_cofix with r; [eauto with paco|eauto with paco|eauto with paco; try contradiction|]
  | [|- context[cpaco11]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using @cpaco11_cofix with r; [eauto with paco|eauto with paco|eauto with paco; try contradiction|]
  | [|- context[cpaco12]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using @cpaco12_cofix with r; [eauto with paco|eauto with paco|eauto with paco; try contradiction|]
  | [|- context[cpaco13]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using @cpaco13_cofix with r; [eauto with paco|eauto with paco|eauto with paco; try contradiction|]
  | [|- context[cpaco14]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using @cpaco14_cofix with r; [eauto with paco|eauto with paco|eauto with paco; try contradiction|]
  end.
Tactic Notation "ccofix" ident(CIH) := ccofix CIH with r.

