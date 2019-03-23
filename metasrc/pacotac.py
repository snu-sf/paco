from __future__ import print_function
import sys
from pacolib import *

if len(sys.argv) < 2:
    sys.stderr.write('\nUsage: '+sys.argv[0]+' relsize\n\n')
    sys.exit(1)

relsize = int(sys.argv[1])

print ("""
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
""")
print ()

print ("(** ** pfold_reverse ")
print ("*)")
print ()
print ('Tactic Notation "pfold_reverse_" :=')
print ("  match goal with")
for n in range(relsize+1):
    print ("  | [|- _ (upaco"+str(n)+" ?gf _)"+n*" _"+"] => eapply (paco"+str(n)+"_unfold (gf := gf))")
print ("  end;")
print ("  eauto with paco.")
print ("Ltac pfold_reverse := under_forall ltac:(pfold_reverse_).")
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
