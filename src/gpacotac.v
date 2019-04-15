Require Import pacotac_internal pacotac pacoall gpacoall.

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

(** ** gclo H
*)

Tactic Notation "gclo_" constr(H) :=
  match goal with
  | [|- context[gpaco0]]  => eapply gpaco0_uclo; [|eapply H|]; [eauto with paco|..]
  | [|- context[gpaco1]]  => eapply gpaco1_uclo; [|eapply H|]; [eauto with paco|..]
  | [|- context[gpaco2]]  => eapply gpaco2_uclo; [|eapply H|]; [eauto with paco|..]
  | [|- context[gpaco3]]  => eapply gpaco3_uclo; [|eapply H|]; [eauto with paco|..]
  | [|- context[gpaco4]]  => eapply gpaco4_uclo; [|eapply H|]; [eauto with paco|..]
  | [|- context[gpaco5]]  => eapply gpaco5_uclo; [|eapply H|]; [eauto with paco|..]
  | [|- context[gpaco6]]  => eapply gpaco6_uclo; [|eapply H|]; [eauto with paco|..]
  | [|- context[gpaco7]]  => eapply gpaco7_uclo; [|eapply H|]; [eauto with paco|..]
  | [|- context[gpaco8]]  => eapply gpaco8_uclo; [|eapply H|]; [eauto with paco|..]
  | [|- context[gpaco9]]  => eapply gpaco9_uclo; [|eapply H|]; [eauto with paco|..]
  | [|- context[gpaco10]]  => eapply gpaco10_uclo; [|eapply H|]; [eauto with paco|..]
  | [|- context[gpaco11]]  => eapply gpaco11_uclo; [|eapply H|]; [eauto with paco|..]
  | [|- context[gpaco12]]  => eapply gpaco12_uclo; [|eapply H|]; [eauto with paco|..]
  | [|- context[gpaco13]]  => eapply gpaco13_uclo; [|eapply H|]; [eauto with paco|..]
  | [|- context[gpaco14]]  => eapply gpaco14_uclo; [|eapply H|]; [eauto with paco|..]
  end.
Ltac gclo H := repeat red; under_forall ltac:(gclo_ H).

(** ** gcofix CIH [with r]
*)

Tactic Notation "gcofix" ident(CIH) "with" ident(r) :=
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
Tactic Notation "gcofix" ident(CIH) := gcofix CIH with r.

