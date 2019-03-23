
Require Import Program.Tactics.
Require Export paconotation.
Require Import pacotac_internal pacoall.
Set Implicit Arguments.

Ltac under_forall tac := generalize _paco_mark_cons; intros; tac; paco_revert_hyp _paco_mark.

Definition get_paco_cls {A} {cls: paco_class A} (a: A) := cls.

Ltac paco_class TGT method :=
  let typ := fresh "_typ_" in let lem := fresh "_lem_" in
  let TMP := fresh "_tmp_" in let X := fresh "_X_" in
  let CLS := fresh "_CLS_" in
  evar (typ: Type); evar (lem: typ);
  assert(TMP: TGT -> True) by (
    intros X; set (CLS := method _ (get_paco_cls X));
    repeat red in CLS; clear X; revert lem;
    match goal with [CLS := ?v |-_] => instantiate (1:= v) end;
    clear CLS; exact I);
  clear TMP; unfold typ in *; clear typ; revert lem.

(** ** pfold tactic
  - [pfold] = [pstep]
*)

Tactic Notation "pfold_" := let x := fresh "_x_" in
  repeat red;
  match goal with [|- ?G] => paco_class G (@pacofold) end;
  intro x; match goal with [x:=?lem|-_] => clear x; eapply lem end.
Ltac pfold := under_forall ltac:(pfold_).
Ltac pstep := pfold.

(** ** punfold tactic
  - [punfold H]
*)

Ltac _punfold H := let x := fresh "_x_" in
  repeat red in H;
  let G := type of H in paco_class G (@pacounfold);
  intro x; match goal with [x:=?lem|-_] => clear x; eapply lem in H end.
Ltac punfold H := _punfold H; eauto with paco.

(** ** pmult tactic
  - [pmult]
*)

Ltac pmult := let x := fresh "_x_" in
  repeat red;
  match goal with [|- ?G] => paco_class G (@pacomult) end;
  intro x; match goal with [x:=?lem|-_] => clear x; eapply lem end.

(** ** pcofix tactic
  - [pcofix CIH [with r]]
*)

Tactic Notation "pcofix" ident(CIH) "with" ident(r) :=
  let x := fresh "_x_" in
  generalize _paco_mark_cons; repeat intro; repeat red;
  match goal with [|- ?G] =>
  paco_class G (@pacoacc); intro x;
  match goal with [x:=?lem|-_] => clear x;
    paco_revert_hyp _paco_mark;
    pcofix CIH using lem with r
  end end.

Tactic Notation "pcofix" ident(CIH) := pcofix CIH with r.

(** ** [pclearbot] simplifies all hypotheses of the form [upaco{n} gf bot{n}] to [paco{n} gf bot{n}].
*)

Definition pclearbot_or (P Q: Prop) := P.

Ltac pclearbot :=
  generalize _paco_mark_cons;
  repeat(
    match goal with [H: context [pacoid] |- _] =>
      let NH := fresh H in
      revert_until H; repeat red in H;
      match goal with [Hcrr: context f [or] |- _] =>
        match Hcrr with H =>
          let P := context f [pclearbot_or] in
          assert (NH: P) by (repeat intro; edestruct H ; [eassumption|contradiction]);
          clear H; rename NH into H; unfold pclearbot_or in H
        end
      end
    end);
  intros; paco_revert_hyp _paco_mark.

(** ** [pdestruct H] and [pinversion H]
*)

Ltac pdestruct H := punfold H; destruct H; pclearbot.

Ltac pinversion H := punfold H; inversion H; pclearbot.

(** ** pmonauto tactic
  - [pmonauto]
*)

Ltac pmonauto :=
  let IN := fresh "IN" in try (repeat intro; destruct IN; eauto; fail).


(** ** pfold_reverse 
*)

Tactic Notation "pfold_reverse_" :=
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
  end;
  eauto with paco.
Ltac pfold_reverse := under_forall ltac:(pfold_reverse_).

(** ** punfold_reverse H 
*)

Ltac punfold_reverse H :=
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
  end;
  eauto with paco.

