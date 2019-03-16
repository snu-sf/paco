from __future__ import print_function
import sys
from pacolib import *

if len(sys.argv) < 2:
    sys.stderr.write('\nUsage: '+sys.argv[0]+' relsize\n\n')
    sys.exit(1)

relsize = int(sys.argv[1])

print ("Require Import pacotac_internal pacotac pacoall cpnall.")
print ()

print ("(** ** uinit")
print ("*)")
print ()
print ('Tactic Notation "uinit_" :=')
print ("  match goal with")
for n in range(relsize+1):
    print ("  | [|- context[paco"+str(n)+"]] => eapply cpn"+str(n)+"_init; [eauto with paco|]")
print ("  end.")
print ("Ltac uinit := repeat red; under_forall ltac:(uinit_).")
print ()

print ("(** ** ufinal")
print ("*)")
print ()
print ('Tactic Notation "ufinal_" :=')
print ("  match goal with")
for n in range(relsize+1):
    print ("  | [|- context[cpn"+str(n)+"]]  => eapply cpn"+str(n)+"_final; [eauto with paco|]")
    print ("  | [|- context[gcpn"+str(n)+"]] => eapply gcpn"+str(n)+"_final; [eauto with paco|]")
print ("  end.")
print ("Ltac ufinal := under_forall ltac:(ufinal_).")
print ()

print ("(** ** gcpn_fold")
print ("*)")
print ()
print ("Ltac gcpn_fold :=")
print ("  match goal with")
for n in range(relsize+1):
    print ("  | [|- ?gf (cpn"+str(n)+" _ ?r)"+n*" _"+"] => change (gf (cpn"+str(n)+" gf r)) with (gcpn"+str(n)+" gf r)")
print ("  end.")
print ()

print ("(** ** ucompat")
print ("*)")
print ()
print ("Ltac ucompat :=")
print ("  match goal with")
for n in range(relsize+1):
    print ("  | [|- context[cpn"+str(n)+"]] => eapply wcompat"+str(n)+"_sound; eauto with paco")
print ("  end.")
print ()

print ("(** ** ubase")
print ("*)")
print ()
print ('Tactic Notation "ubase_" :=')
print ("  match goal with")
for n in range(relsize+1):
    print ("  | [|- context[cpn"+str(n)+"]] => eapply cpn"+str(n)+"_base")
print ("  end.")
print ("Ltac ubase := under_forall ltac:(ubase_).")
print ()

print ("(** ** ustep")
print ("*)")
print ()
print ('Tactic Notation "ustep_" :=')
print ("  match goal with")
for n in range(relsize+1):
    print ("  | [|- context[cpn"+str(n)+"]] => eapply cpn"+str(n)+"_step; [eauto with paco|]")
print ("  end.")
print ("Ltac ustep := under_forall ltac:(ustep_).")
print ()

print ("(** ** uclo H")
print ("*)")
print ()
print ('Tactic Notation "uclo_" constr(H) :=')
print ("  match goal with")
for n in range(relsize+1):
    print ("  | [|- context[cpn"+str(n)+"]]  => eapply cpn"+str(n)+"_clo; [|eapply H|]; [eauto with paco|]")
    print ("  | [|- context[gcpn"+str(n)+"]] => eapply gcpn"+str(n)+"_clo; [|eapply H|]; [eauto with paco|]")
print ("  end.")
print ("Ltac uclo H := under_forall ltac:(uclo_ H).")
print ()

print ("(** ** ucofix CIH [with r]")
print ("*)")
print ()
print ('Tactic Notation "ucofix" ident(CIH) "with" ident(r) :=')
print ("  generalize _paco_mark_cons; intros;")
print ("  match goal with")
for n in range(relsize+1):
    print ("  | [|- context[cpn"+str(n)+"]]  =>")
    print ("    (eapply cpn"+str(n)+"_from_paco; [eauto with paco|]); paco_revert_hyp _paco_mark;")
    print ("    pcofix CIH with r;")
    print ("    under_forall ltac:(eapply gcpn"+str(n)+"_to_paco; [eauto with paco|])")
    print ("  | [|- context[gcpn"+str(n)+"]] =>")
    print ("    (eapply gcpn"+str(n)+"_from_paco; [eauto with paco|]); paco_revert_hyp _paco_mark;")
    print ("    pcofix CIH with r;")
    print ("    under_forall ltac:(eapply gcpn"+str(n)+"_to_paco; [eauto with paco|])")
print ("  end.")
print ('Tactic Notation "ucofix" ident(CIH) := ucofix CIH with r.')
print ()
