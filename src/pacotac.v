
Require Import Program.Tactics.
From Paco Require Export paconotation.
From Paco Require Import pacotac_internal pacoall.
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

Definition pclearbot_orL (P Q: Prop) := P.
Definition pclearbot_orR (P Q: Prop) := Q.

Ltac pclearbot :=
  generalize _paco_mark_cons;
  repeat(
    let H := match goal with
             | [H: context [bot0] |- _] => H
             | [H: context [bot1] |- _] => H
             | [H: context [bot2] |- _] => H
             | [H: context [bot3] |- _] => H
             | [H: context [bot4] |- _] => H
             end in
    let NH := fresh H in
    revert_until H;
    repeat (
      repeat red in H;
      match goal with [Hcrr: context f [or] |- _] =>
        match Hcrr with H =>
        first[(
          let P := context f [pclearbot_orL] in
          assert (NH: P) by (repeat intro; edestruct H ; [eassumption|repeat (match goal with [X: _ \/ _ |- _] => destruct X end); contradiction]);
          clear H; rename NH into H; unfold pclearbot_orL in H
        ) | (
          let P := context f [pclearbot_orR] in
          assert (NH: P) by (repeat intro; edestruct H ; [repeat (match goal with [X: _ \/ _ |- _] => destruct X end); contradiction|eassumption]);
          clear H; rename NH into H; unfold pclearbot_orR in H
        )]
        end
      end);
    revert H);
  intros; paco_revert_hyp _paco_mark.

(** ** [pdestruct H] and [pinversion H]
*)

Ltac pdestruct H := punfold H; destruct H; pclearbot.

Ltac pinversion H := punfold H; inversion H; pclearbot.

(** ** pmonauto tactic
  - [pmonauto]
*)

Ltac pmonauto :=
  let IN := fresh "IN" in try (repeat intro; destruct IN; eauto with paco; fail).


(** ** [pfold_reverse] = [pstep_reverse] 
*)

Tactic Notation "pfold_reverse_" :=
  match goal with
  | [|- _ (upaco0 ?gf _)] => eapply (paco0_unfold (gf := gf))
  | [|- _ (upaco1 ?gf _) _] => eapply (paco1_unfold (gf := gf))
  | [|- _ (upaco2 ?gf _) _ _] => eapply (paco2_unfold (gf := gf))
  | [|- _ (upaco3 ?gf _) _ _ _] => eapply (paco3_unfold (gf := gf))
  | [|- _ (upaco4 ?gf _) _ _ _ _] => eapply (paco4_unfold (gf := gf))
  end;
  eauto with paco.
Ltac pfold_reverse := under_forall ltac:(pfold_reverse_).
Ltac pstep_reverse := pfold_reverse.

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
  end;
  eauto with paco.

