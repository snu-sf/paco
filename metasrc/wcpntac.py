from __future__ import print_function
import sys
from pacolib import *

if len(sys.argv) < 2:
    sys.stderr.write('\nUsage: '+sys.argv[0]+' relsize\n\n')
    sys.exit(1)

relsize = int(sys.argv[1])

print ("Require Import pacotac_internal pacotac pacoall cpnall wcpnall.")
print ()

print ("(** ** winit")
print ("*)")
print ()
print ('Tactic Notation "winit_" :=')
print ("  match goal with")
for n in range(relsize+1):
    print ("  | [|- context[cpn"+str(n)+"]] => eapply wcpn"+str(n)+"_init; [eauto with paco|]")
print ("  end.")
print ("Ltac winit := repeat red; under_forall ltac:(winit_).")
print ()

print ("(** ** wfinal")
print ("*)")
print ()
print ('Tactic Notation "wfinal_" :=')
print ("  match goal with")
for n in range(relsize+1):
    print ("  | [|- context[wcpn"+str(n)+"]]  => eapply wcpn"+str(n)+"_final")
print ("  end.")
print ("Ltac wfinal := repeat red; under_forall ltac:(wfinal_).")
print ()

print ("(** ** wbase")
print ("*)")
print ()
print ('Tactic Notation "wbase_" :=')
print ("  match goal with")
for n in range(relsize+1):
    print ("  | [|- context[wcpn"+str(n)+"]] => eapply wcpn"+str(n)+"_base")
print ("  end.")
print ("Ltac wbase := repeat red; under_forall ltac:(wbase_).")
print ()

print ("(** ** wcpn")
print ("*)")
print ()
print ('Tactic Notation "wcpn_" :=')
print ("  match goal with")
for n in range(relsize+1):
    print ("  | [|- context[wcpn"+str(n)+"]] => eapply wcpn"+str(n)+"_cpn; [eauto with paco|]")
print ("  end.")
print ("Ltac wcpn := repeat red; under_forall ltac:(wcpn_).")
print ()

print ("(** ** wstep")
print ("*)")
print ()
print ('Tactic Notation "wstep_" :=')
print ("  match goal with")
for n in range(relsize+1):
    print ("  | [|- context[wcpn"+str(n)+"]] => eapply wcpn"+str(n)+"_step; [eauto with paco|]")
print ("  end.")
print ("Ltac wstep := repeat red; under_forall ltac:(wstep_).")
print ()

print ("(** ** wclo H")
print ("*)")
print ()
print ('Tactic Notation "wclo_" constr(H) :=')
print ("  match goal with")
for n in range(relsize+1):
    print ("  | [|- context[wcpn"+str(n)+"]]  => eapply wcpn"+str(n)+"_clo; [|eapply H|]; [eauto with paco|]")
print ("  end.")
print ("Ltac wclo H := repeat red; under_forall ltac:(wclo_ H).")
print ()

print ("(** ** wcofix CIH [with r]")
print ("*)")
print ()
print ('Tactic Notation "wcofix" ident(CIH) "with" ident(r) :=')
print ("  repeat red;")
print ("  generalize _paco_mark_cons; intros;")
print ("  match goal with")
for n in range(relsize+1):
    print ("  | [|- context[wcpn"+str(n)+"]]  =>")
    print ("    paco_revert_hyp _paco_mark;")
    print ("    pcofix CIH using @wcpn"+str(n)+"_cofix with r; [eauto with paco|eauto with paco|]")
print ("  end.")
print ('Tactic Notation "wcofix" ident(CIH) := wcofix CIH with r.')
print ()
