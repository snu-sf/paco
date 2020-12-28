From Paco Require Import pacotac_internal pacotac pacoall gpacoall.

(** ** ginit
*)

Tactic Notation "ginit_" :=
  match goal with
  | [|- context[paco0]] => eapply gpaco0_init; [eauto with paco|eauto with paco|]
  | [|- context[paco1]] => eapply gpaco1_init; [eauto with paco|eauto with paco|]
  | [|- context[paco2]] => eapply gpaco2_init; [eauto with paco|eauto with paco|]
  | [|- context[paco3]] => eapply gpaco3_init; [eauto with paco|eauto with paco|]
  | [|- context[paco4]] => eapply gpaco4_init; [eauto with paco|eauto with paco|]
  | [|- context[paco5]] => eapply gpaco5_init; [eauto with paco|eauto with paco|]
  | [|- context[paco6]] => eapply gpaco6_init; [eauto with paco|eauto with paco|]
  | [|- context[paco7]] => eapply gpaco7_init; [eauto with paco|eauto with paco|]
  | [|- context[paco8]] => eapply gpaco8_init; [eauto with paco|eauto with paco|]
  | [|- context[paco9]] => eapply gpaco9_init; [eauto with paco|eauto with paco|]
  | [|- context[paco10]] => eapply gpaco10_init; [eauto with paco|eauto with paco|]
  | [|- context[paco11]] => eapply gpaco11_init; [eauto with paco|eauto with paco|]
  | [|- context[paco12]] => eapply gpaco12_init; [eauto with paco|eauto with paco|]
  | [|- context[paco13]] => eapply gpaco13_init; [eauto with paco|eauto with paco|]
  | [|- context[paco14]] => eapply gpaco14_init; [eauto with paco|eauto with paco|]
  end.
Ltac ginit := repeat red; under_forall ltac:(ginit_).

(** ** gfinal
*)

Tactic Notation "gfinal_" :=
  match goal with
  | [|- context[gpaco0]] => eapply gpaco0_final; [eauto with paco|]
  | [|- context[gpaco1]] => eapply gpaco1_final; [eauto with paco|]
  | [|- context[gpaco2]] => eapply gpaco2_final; [eauto with paco|]
  | [|- context[gpaco3]] => eapply gpaco3_final; [eauto with paco|]
  | [|- context[gpaco4]] => eapply gpaco4_final; [eauto with paco|]
  | [|- context[gpaco5]] => eapply gpaco5_final; [eauto with paco|]
  | [|- context[gpaco6]] => eapply gpaco6_final; [eauto with paco|]
  | [|- context[gpaco7]] => eapply gpaco7_final; [eauto with paco|]
  | [|- context[gpaco8]] => eapply gpaco8_final; [eauto with paco|]
  | [|- context[gpaco9]] => eapply gpaco9_final; [eauto with paco|]
  | [|- context[gpaco10]] => eapply gpaco10_final; [eauto with paco|]
  | [|- context[gpaco11]] => eapply gpaco11_final; [eauto with paco|]
  | [|- context[gpaco12]] => eapply gpaco12_final; [eauto with paco|]
  | [|- context[gpaco13]] => eapply gpaco13_final; [eauto with paco|]
  | [|- context[gpaco14]] => eapply gpaco14_final; [eauto with paco|]
  end.
Ltac gfinal := repeat red; under_forall ltac:(gfinal_).

(** ** gunfold H
*)

Ltac gunfold H :=
  repeat red in H;
  let G := type of H in
  match G with
  | context[gpaco0] => eapply gpaco0_unfold in H; [|eauto with paco]
  | context[gpaco1] => eapply gpaco1_unfold in H; [|eauto with paco]
  | context[gpaco2] => eapply gpaco2_unfold in H; [|eauto with paco]
  | context[gpaco3] => eapply gpaco3_unfold in H; [|eauto with paco]
  | context[gpaco4] => eapply gpaco4_unfold in H; [|eauto with paco]
  | context[gpaco5] => eapply gpaco5_unfold in H; [|eauto with paco]
  | context[gpaco6] => eapply gpaco6_unfold in H; [|eauto with paco]
  | context[gpaco7] => eapply gpaco7_unfold in H; [|eauto with paco]
  | context[gpaco8] => eapply gpaco8_unfold in H; [|eauto with paco]
  | context[gpaco9] => eapply gpaco9_unfold in H; [|eauto with paco]
  | context[gpaco10] => eapply gpaco10_unfold in H; [|eauto with paco]
  | context[gpaco11] => eapply gpaco11_unfold in H; [|eauto with paco]
  | context[gpaco12] => eapply gpaco12_unfold in H; [|eauto with paco]
  | context[gpaco13] => eapply gpaco13_unfold in H; [|eauto with paco]
  | context[gpaco14] => eapply gpaco14_unfold in H; [|eauto with paco]
  end.

(** ** gunfoldbot H
*)

Ltac gunfoldbot H :=
  repeat red in H;
  let G := type of H in
  match G with
  | context[gpaco0] => eapply gpaco0_unfold_bot in H; [|eauto with paco|eauto with paco]
  | context[gpaco1] => eapply gpaco1_unfold_bot in H; [|eauto with paco|eauto with paco]
  | context[gpaco2] => eapply gpaco2_unfold_bot in H; [|eauto with paco|eauto with paco]
  | context[gpaco3] => eapply gpaco3_unfold_bot in H; [|eauto with paco|eauto with paco]
  | context[gpaco4] => eapply gpaco4_unfold_bot in H; [|eauto with paco|eauto with paco]
  | context[gpaco5] => eapply gpaco5_unfold_bot in H; [|eauto with paco|eauto with paco]
  | context[gpaco6] => eapply gpaco6_unfold_bot in H; [|eauto with paco|eauto with paco]
  | context[gpaco7] => eapply gpaco7_unfold_bot in H; [|eauto with paco|eauto with paco]
  | context[gpaco8] => eapply gpaco8_unfold_bot in H; [|eauto with paco|eauto with paco]
  | context[gpaco9] => eapply gpaco9_unfold_bot in H; [|eauto with paco|eauto with paco]
  | context[gpaco10] => eapply gpaco10_unfold_bot in H; [|eauto with paco|eauto with paco]
  | context[gpaco11] => eapply gpaco11_unfold_bot in H; [|eauto with paco|eauto with paco]
  | context[gpaco12] => eapply gpaco12_unfold_bot in H; [|eauto with paco|eauto with paco]
  | context[gpaco13] => eapply gpaco13_unfold_bot in H; [|eauto with paco|eauto with paco]
  | context[gpaco14] => eapply gpaco14_unfold_bot in H; [|eauto with paco|eauto with paco]
  end.

(** ** gbase
*)

Tactic Notation "gbase_" :=
  match goal with
  | [|- context[gpaco0]] => eapply gpaco0_base
  | [|- context[gpaco1]] => eapply gpaco1_base
  | [|- context[gpaco2]] => eapply gpaco2_base
  | [|- context[gpaco3]] => eapply gpaco3_base
  | [|- context[gpaco4]] => eapply gpaco4_base
  | [|- context[gpaco5]] => eapply gpaco5_base
  | [|- context[gpaco6]] => eapply gpaco6_base
  | [|- context[gpaco7]] => eapply gpaco7_base
  | [|- context[gpaco8]] => eapply gpaco8_base
  | [|- context[gpaco9]] => eapply gpaco9_base
  | [|- context[gpaco10]] => eapply gpaco10_base
  | [|- context[gpaco11]] => eapply gpaco11_base
  | [|- context[gpaco12]] => eapply gpaco12_base
  | [|- context[gpaco13]] => eapply gpaco13_base
  | [|- context[gpaco14]] => eapply gpaco14_base
  end.
Ltac gbase := repeat red; under_forall ltac:(gbase_).

(** ** gstep
*)

Tactic Notation "gstep_" :=
  match goal with
  | [|- context[gpaco0]] => eapply gpaco0_step; [eauto with paco|]
  | [|- context[gpaco1]] => eapply gpaco1_step; [eauto with paco|]
  | [|- context[gpaco2]] => eapply gpaco2_step; [eauto with paco|]
  | [|- context[gpaco3]] => eapply gpaco3_step; [eauto with paco|]
  | [|- context[gpaco4]] => eapply gpaco4_step; [eauto with paco|]
  | [|- context[gpaco5]] => eapply gpaco5_step; [eauto with paco|]
  | [|- context[gpaco6]] => eapply gpaco6_step; [eauto with paco|]
  | [|- context[gpaco7]] => eapply gpaco7_step; [eauto with paco|]
  | [|- context[gpaco8]] => eapply gpaco8_step; [eauto with paco|]
  | [|- context[gpaco9]] => eapply gpaco9_step; [eauto with paco|]
  | [|- context[gpaco10]] => eapply gpaco10_step; [eauto with paco|]
  | [|- context[gpaco11]] => eapply gpaco11_step; [eauto with paco|]
  | [|- context[gpaco12]] => eapply gpaco12_step; [eauto with paco|]
  | [|- context[gpaco13]] => eapply gpaco13_step; [eauto with paco|]
  | [|- context[gpaco14]] => eapply gpaco14_step; [eauto with paco|]
  end.
Ltac gstep := repeat red; under_forall ltac:(gstep_).

(** ** gupaco
*)

Tactic Notation "gupaco_" :=
  match goal with
  | [|- context[gpaco0]] => eapply gpaco0_gupaco; [eauto with paco|]
  | [|- context[gpaco1]] => eapply gpaco1_gupaco; [eauto with paco|]
  | [|- context[gpaco2]] => eapply gpaco2_gupaco; [eauto with paco|]
  | [|- context[gpaco3]] => eapply gpaco3_gupaco; [eauto with paco|]
  | [|- context[gpaco4]] => eapply gpaco4_gupaco; [eauto with paco|]
  | [|- context[gpaco5]] => eapply gpaco5_gupaco; [eauto with paco|]
  | [|- context[gpaco6]] => eapply gpaco6_gupaco; [eauto with paco|]
  | [|- context[gpaco7]] => eapply gpaco7_gupaco; [eauto with paco|]
  | [|- context[gpaco8]] => eapply gpaco8_gupaco; [eauto with paco|]
  | [|- context[gpaco9]] => eapply gpaco9_gupaco; [eauto with paco|]
  | [|- context[gpaco10]] => eapply gpaco10_gupaco; [eauto with paco|]
  | [|- context[gpaco11]] => eapply gpaco11_gupaco; [eauto with paco|]
  | [|- context[gpaco12]] => eapply gpaco12_gupaco; [eauto with paco|]
  | [|- context[gpaco13]] => eapply gpaco13_gupaco; [eauto with paco|]
  | [|- context[gpaco14]] => eapply gpaco14_gupaco; [eauto with paco|]
  end.
Ltac gupaco := repeat red; under_forall ltac:(gupaco_).

(** ** gpaco
*)

Tactic Notation "gpaco_" :=
  match goal with
  | [|- context[gpaco0]] => eapply gpaco0_gpaco; [eauto with paco|]
  | [|- context[gpaco1]] => eapply gpaco1_gpaco; [eauto with paco|]
  | [|- context[gpaco2]] => eapply gpaco2_gpaco; [eauto with paco|]
  | [|- context[gpaco3]] => eapply gpaco3_gpaco; [eauto with paco|]
  | [|- context[gpaco4]] => eapply gpaco4_gpaco; [eauto with paco|]
  | [|- context[gpaco5]] => eapply gpaco5_gpaco; [eauto with paco|]
  | [|- context[gpaco6]] => eapply gpaco6_gpaco; [eauto with paco|]
  | [|- context[gpaco7]] => eapply gpaco7_gpaco; [eauto with paco|]
  | [|- context[gpaco8]] => eapply gpaco8_gpaco; [eauto with paco|]
  | [|- context[gpaco9]] => eapply gpaco9_gpaco; [eauto with paco|]
  | [|- context[gpaco10]] => eapply gpaco10_gpaco; [eauto with paco|]
  | [|- context[gpaco11]] => eapply gpaco11_gpaco; [eauto with paco|]
  | [|- context[gpaco12]] => eapply gpaco12_gpaco; [eauto with paco|]
  | [|- context[gpaco13]] => eapply gpaco13_gpaco; [eauto with paco|]
  | [|- context[gpaco14]] => eapply gpaco14_gpaco; [eauto with paco|]
  end.
Ltac gpaco := repeat red; under_forall ltac:(gpaco_).

(** ** gclo
*)

Tactic Notation "gclo_" :=
  match goal with
  | [|- context[gpaco0]]  => eapply gpaco0_gupaco, gpaco0_clo; [eauto with paco|]
  | [|- context[gpaco1]]  => eapply gpaco1_gupaco, gpaco1_clo; [eauto with paco|]
  | [|- context[gpaco2]]  => eapply gpaco2_gupaco, gpaco2_clo; [eauto with paco|]
  | [|- context[gpaco3]]  => eapply gpaco3_gupaco, gpaco3_clo; [eauto with paco|]
  | [|- context[gpaco4]]  => eapply gpaco4_gupaco, gpaco4_clo; [eauto with paco|]
  | [|- context[gpaco5]]  => eapply gpaco5_gupaco, gpaco5_clo; [eauto with paco|]
  | [|- context[gpaco6]]  => eapply gpaco6_gupaco, gpaco6_clo; [eauto with paco|]
  | [|- context[gpaco7]]  => eapply gpaco7_gupaco, gpaco7_clo; [eauto with paco|]
  | [|- context[gpaco8]]  => eapply gpaco8_gupaco, gpaco8_clo; [eauto with paco|]
  | [|- context[gpaco9]]  => eapply gpaco9_gupaco, gpaco9_clo; [eauto with paco|]
  | [|- context[gpaco10]]  => eapply gpaco10_gupaco, gpaco10_clo; [eauto with paco|]
  | [|- context[gpaco11]]  => eapply gpaco11_gupaco, gpaco11_clo; [eauto with paco|]
  | [|- context[gpaco12]]  => eapply gpaco12_gupaco, gpaco12_clo; [eauto with paco|]
  | [|- context[gpaco13]]  => eapply gpaco13_gupaco, gpaco13_clo; [eauto with paco|]
  | [|- context[gpaco14]]  => eapply gpaco14_gupaco, gpaco14_clo; [eauto with paco|]
  end.
Ltac gclo := repeat red; under_forall ltac:(gclo_).

(** ** grclo
*)

Tactic Notation "grclo_" :=
  match goal with
  | [|- context[gpaco0]]  => eapply gpaco0_gupaco, gpaco0_rclo; [eauto with paco|]
  | [|- context[gpaco1]]  => eapply gpaco1_gupaco, gpaco1_rclo; [eauto with paco|]
  | [|- context[gpaco2]]  => eapply gpaco2_gupaco, gpaco2_rclo; [eauto with paco|]
  | [|- context[gpaco3]]  => eapply gpaco3_gupaco, gpaco3_rclo; [eauto with paco|]
  | [|- context[gpaco4]]  => eapply gpaco4_gupaco, gpaco4_rclo; [eauto with paco|]
  | [|- context[gpaco5]]  => eapply gpaco5_gupaco, gpaco5_rclo; [eauto with paco|]
  | [|- context[gpaco6]]  => eapply gpaco6_gupaco, gpaco6_rclo; [eauto with paco|]
  | [|- context[gpaco7]]  => eapply gpaco7_gupaco, gpaco7_rclo; [eauto with paco|]
  | [|- context[gpaco8]]  => eapply gpaco8_gupaco, gpaco8_rclo; [eauto with paco|]
  | [|- context[gpaco9]]  => eapply gpaco9_gupaco, gpaco9_rclo; [eauto with paco|]
  | [|- context[gpaco10]]  => eapply gpaco10_gupaco, gpaco10_rclo; [eauto with paco|]
  | [|- context[gpaco11]]  => eapply gpaco11_gupaco, gpaco11_rclo; [eauto with paco|]
  | [|- context[gpaco12]]  => eapply gpaco12_gupaco, gpaco12_rclo; [eauto with paco|]
  | [|- context[gpaco13]]  => eapply gpaco13_gupaco, gpaco13_rclo; [eauto with paco|]
  | [|- context[gpaco14]]  => eapply gpaco14_gupaco, gpaco14_rclo; [eauto with paco|]
  end.
Ltac grclo := repeat red; under_forall ltac:(grclo_).

(** ** guclo H
*)

Tactic Notation "guclo_" constr(H) :=
  match goal with
  | [|- context[gpaco0]]  => eapply gpaco0_uclo; [|eapply H|]; eauto with paco
  | [|- context[gpaco1]]  => eapply gpaco1_uclo; [|eapply H|]; eauto with paco
  | [|- context[gpaco2]]  => eapply gpaco2_uclo; [|eapply H|]; eauto with paco
  | [|- context[gpaco3]]  => eapply gpaco3_uclo; [|eapply H|]; eauto with paco
  | [|- context[gpaco4]]  => eapply gpaco4_uclo; [|eapply H|]; eauto with paco
  | [|- context[gpaco5]]  => eapply gpaco5_uclo; [|eapply H|]; eauto with paco
  | [|- context[gpaco6]]  => eapply gpaco6_uclo; [|eapply H|]; eauto with paco
  | [|- context[gpaco7]]  => eapply gpaco7_uclo; [|eapply H|]; eauto with paco
  | [|- context[gpaco8]]  => eapply gpaco8_uclo; [|eapply H|]; eauto with paco
  | [|- context[gpaco9]]  => eapply gpaco9_uclo; [|eapply H|]; eauto with paco
  | [|- context[gpaco10]]  => eapply gpaco10_uclo; [|eapply H|]; eauto with paco
  | [|- context[gpaco11]]  => eapply gpaco11_uclo; [|eapply H|]; eauto with paco
  | [|- context[gpaco12]]  => eapply gpaco12_uclo; [|eapply H|]; eauto with paco
  | [|- context[gpaco13]]  => eapply gpaco13_uclo; [|eapply H|]; eauto with paco
  | [|- context[gpaco14]]  => eapply gpaco14_uclo; [|eapply H|]; eauto with paco
  end.
Ltac guclo H := repeat red; under_forall ltac:(guclo_ H).

(** ** glecpn
*)

Tactic Notation "glecpn" :=
  repeat red;
  match goal with
  | [|- context[gpaco0]]  => eapply cpn0_uclo; [eauto with paco| |]
  | [|- context[gpaco1]]  => eapply cpn1_uclo; [eauto with paco| |]
  | [|- context[gpaco2]]  => eapply cpn2_uclo; [eauto with paco| |]
  | [|- context[gpaco3]]  => eapply cpn3_uclo; [eauto with paco| |]
  | [|- context[gpaco4]]  => eapply cpn4_uclo; [eauto with paco| |]
  | [|- context[gpaco5]]  => eapply cpn5_uclo; [eauto with paco| |]
  | [|- context[gpaco6]]  => eapply cpn6_uclo; [eauto with paco| |]
  | [|- context[gpaco7]]  => eapply cpn7_uclo; [eauto with paco| |]
  | [|- context[gpaco8]]  => eapply cpn8_uclo; [eauto with paco| |]
  | [|- context[gpaco9]]  => eapply cpn9_uclo; [eauto with paco| |]
  | [|- context[gpaco10]]  => eapply cpn10_uclo; [eauto with paco| |]
  | [|- context[gpaco11]]  => eapply cpn11_uclo; [eauto with paco| |]
  | [|- context[gpaco12]]  => eapply cpn12_uclo; [eauto with paco| |]
  | [|- context[gpaco13]]  => eapply cpn13_uclo; [eauto with paco| |]
  | [|- context[gpaco14]]  => eapply cpn14_uclo; [eauto with paco| |]
  end.

(** ** gcofix CIH [with r]
*)

Tactic Notation "gcofix" ident(CIH) "with" ident(r) :=
  repeat red;
  generalize _paco_mark_cons; intros;
  match goal with
  | [|- context[@gpaco0 ?gf]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using (@gpaco0_cofix gf) with r; [eauto with paco|]
  | [|- context[@gpaco1 _ ?gf]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using (@gpaco1_cofix _ gf) with r; [eauto with paco|]
  | [|- context[@gpaco2 _ _ ?gf]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using (@gpaco2_cofix _ _ gf) with r; [eauto with paco|]
  | [|- context[@gpaco3 _ _ _ ?gf]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using (@gpaco3_cofix _ _ _ gf) with r; [eauto with paco|]
  | [|- context[@gpaco4 _ _ _ _ ?gf]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using (@gpaco4_cofix _ _ _ _ gf) with r; [eauto with paco|]
  | [|- context[@gpaco5 _ _ _ _ _ ?gf]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using (@gpaco5_cofix _ _ _ _ _ gf) with r; [eauto with paco|]
  | [|- context[@gpaco6 _ _ _ _ _ _ ?gf]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using (@gpaco6_cofix _ _ _ _ _ _ gf) with r; [eauto with paco|]
  | [|- context[@gpaco7 _ _ _ _ _ _ _ ?gf]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using (@gpaco7_cofix _ _ _ _ _ _ _ gf) with r; [eauto with paco|]
  | [|- context[@gpaco8 _ _ _ _ _ _ _ _ ?gf]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using (@gpaco8_cofix _ _ _ _ _ _ _ _ gf) with r; [eauto with paco|]
  | [|- context[@gpaco9 _ _ _ _ _ _ _ _ _ ?gf]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using (@gpaco9_cofix _ _ _ _ _ _ _ _ _ gf) with r; [eauto with paco|]
  | [|- context[@gpaco10 _ _ _ _ _ _ _ _ _ _ ?gf]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using (@gpaco10_cofix _ _ _ _ _ _ _ _ _ _ gf) with r; [eauto with paco|]
  | [|- context[@gpaco11 _ _ _ _ _ _ _ _ _ _ _ ?gf]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using (@gpaco11_cofix _ _ _ _ _ _ _ _ _ _ _ gf) with r; [eauto with paco|]
  | [|- context[@gpaco12 _ _ _ _ _ _ _ _ _ _ _ _ ?gf]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using (@gpaco12_cofix _ _ _ _ _ _ _ _ _ _ _ _ gf) with r; [eauto with paco|]
  | [|- context[@gpaco13 _ _ _ _ _ _ _ _ _ _ _ _ _ ?gf]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using (@gpaco13_cofix _ _ _ _ _ _ _ _ _ _ _ _ _ gf) with r; [eauto with paco|]
  | [|- context[@gpaco14 _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?gf]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using (@gpaco14_cofix _ _ _ _ _ _ _ _ _ _ _ _ _ _ gf) with r; [eauto with paco|]
  end.
Tactic Notation "gcofix_old" ident(CIH) "with" ident(r) :=
  repeat red;
  generalize _paco_mark_cons; intros;
  match goal with
  | [|- context[gpaco0]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using @gpaco0_cofix with r; [eauto with paco|]
  | [|- context[gpaco1]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using @gpaco1_cofix with r; [eauto with paco|]
  | [|- context[gpaco2]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using @gpaco2_cofix with r; [eauto with paco|]
  | [|- context[gpaco3]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using @gpaco3_cofix with r; [eauto with paco|]
  | [|- context[gpaco4]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using @gpaco4_cofix with r; [eauto with paco|]
  | [|- context[gpaco5]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using @gpaco5_cofix with r; [eauto with paco|]
  | [|- context[gpaco6]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using @gpaco6_cofix with r; [eauto with paco|]
  | [|- context[gpaco7]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using @gpaco7_cofix with r; [eauto with paco|]
  | [|- context[gpaco8]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using @gpaco8_cofix with r; [eauto with paco|]
  | [|- context[gpaco9]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using @gpaco9_cofix with r; [eauto with paco|]
  | [|- context[gpaco10]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using @gpaco10_cofix with r; [eauto with paco|]
  | [|- context[gpaco11]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using @gpaco11_cofix with r; [eauto with paco|]
  | [|- context[gpaco12]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using @gpaco12_cofix with r; [eauto with paco|]
  | [|- context[gpaco13]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using @gpaco13_cofix with r; [eauto with paco|]
  | [|- context[gpaco14]]  =>
    paco_revert_hyp _paco_mark;
    pcofix CIH using @gpaco14_cofix with r; [eauto with paco|]
  end.
Tactic Notation "gcofix" ident(CIH) := first [gcofix CIH with r | gcofix_old CIH with r].

