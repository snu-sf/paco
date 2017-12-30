Require Export paconotation pacotac.
Set Implicit Arguments.

(** ** Type Class for acc, mult, fold and unfold
*)

Class paco_class (A : Prop) :=
{ pacoacctyp: Type
; pacoacc : pacoacctyp
; pacomulttyp: Type
; pacomult : pacomulttyp
; pacofoldtyp: Type
; pacofold : pacofoldtyp
; pacounfoldtyp: Type
; pacounfold : pacounfoldtyp
}.

Definition get_paco_cls {A} {cls: paco_class A} (a: A) := cls.

Create HintDb paco.

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
  - [pfold]
*)

Ltac pfold := let x := fresh "_x_" in
  repeat red;
  match goal with [|- ?G] => paco_class G (@pacofold) end;
  intro x; match goal with [x:=?lem|-_] => clear x; eapply lem end.

(** ** punfold tactic
  - [punfold H]
*)

Ltac punfold H := let x := fresh "_x_" in
  repeat red in H;
  let G := type of H in paco_class G (@pacounfold);
  intro x; match goal with [x:=?lem|-_] => clear x; eapply lem in H end;
  eauto with paco.

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

Ltac pclearbot :=
  let X := fresh "_X" in
  repeat match goal with
  | [H: appcontext[pacoid] |- _] => red in H; destruct H as [H|X]; [|contradiction X]
  end.

(** ** [pdestruct H] and [pinversion H]
*)

Ltac pdestruct H := punfold H; destruct H; pclearbot.

Ltac pinversion H := punfold H; inversion H; pclearbot.

(** ** pmonauto tactic
  - [pmonauto]
*)

Ltac pmonauto :=
  let IN := fresh "IN" in try (repeat intro; destruct IN; eauto; fail).

