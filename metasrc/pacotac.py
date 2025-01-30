from __future__ import print_function
import sys
from pacolib import *

if len(sys.argv) < 2:
    sys.stderr.write('\nUsage: '+sys.argv[0]+' relsize\n\n')
    sys.exit(1)

relsize = int(sys.argv[1])
n = relsize

print ("""
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

Ltac pclearbotH H :=
  generalize _paco_mark_cons;
  let NH := fresh H in
  revert_until H;
  repeat red in H;
  match goal with [Hcrr: context f [or] |- _] =>
    match Hcrr with H =>
    first[(
      let P := context f [pclearbot_orL] in
      assert (NH: P) by (repeat intro; edestruct H ; try eassumption; repeat (match goal with [X: _ \/ _ |- _] => destruct X end); contradiction);
      clear H; rename NH into H; unfold pclearbot_orL in H
    ) | (
      let P := context f [pclearbot_orR] in
      assert (NH: P) by (repeat intro; edestruct H ; try eassumption; repeat (match goal with [X: _ \/ _ |- _] => destruct X end); contradiction);
      clear H; rename NH into H; unfold pclearbot_orR in H
    )]
    end
  end;
  intros; paco_revert_hyp _paco_mark.

Ltac pclearbot :=
  repeat (
    match goal with
""",end="")
for i in range(n+1):
    print ("    | [H: context [bot"+str(i)+"] |- _] => pclearbotH H")
print ("""    end).


(** ** [pdestruct H] and [pinversion H]
*)

Ltac pdestruct H := punfold H; destruct H; pclearbot.

Ltac pinversion H := punfold H; inversion H; pclearbot.

(** ** pmonauto tactic
  - [pmonauto]
*)

Ltac pmonauto :=
  let IN := fresh "IN" in try (repeat intro; destruct IN; eauto with paco; fail).
""")
print ()

print ("(** ** [pfold_reverse] = [pstep_reverse] ")
print ("*)")
print ()
print ('Tactic Notation "pfold_reverse_" :=')
print ("  match goal with")
for n in range(relsize+1):
    print ("  | [|- _ (upaco"+str(n)+" ?gf _)"+n*" _"+"] => eapply (paco"+str(n)+"_unfold (gf := gf))")
print ("  end;")
print ("  eauto with paco.")
print ("Ltac pfold_reverse := under_forall ltac:(pfold_reverse_).")
print ("Ltac pstep_reverse := pfold_reverse.")
print ()

print ("(** ** punfold_reverse H ")
print ("*)")
print ()
print ("Ltac punfold_reverse H :=")
print ("  let PP := type of H in")
print ("  match PP with")
for n in range(relsize+1):
    print ("  | _ (upaco"+str(n)+" ?gf _)"+n*" _"+" => eapply (paco"+str(n)+"_fold gf) in H")
print ("  end;")
print ("  eauto with paco.")
print ()
