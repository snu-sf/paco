from __future__ import print_function
import sys
from pacolib import *

if len(sys.argv) < 2:
    sys.stderr.write('\nUsage: '+sys.argv[0]+' relsize\n\n')
    sys.exit(1)

relsize = int(sys.argv[1])

print ("Require Import pacotac_internal pacotac pacoall cpacoall.")
print ()

print ("(** ** cinit")
print ("*)")
print ()
print ('Tactic Notation "cinit_" :=')
print ("  match goal with")
for n in range(relsize+1):
    print ("  | [|- context[paco"+str(n)+"]] => eapply cpaco"+str(n)+"_init; [eauto with paco|eauto with paco|]")
print ("  end.")
print ("Ltac cinit := repeat red; under_forall ltac:(cinit_).")
print ()

print ("(** ** cunfold H")
print ("*)")
print ()
print ('Ltac cunfold H :=')
print ("  repeat red in H;")
print ("  let G := type of H in");
print ("  match G with")
for n in range(relsize+1):
    print ("  | context[cpaco"+str(n)+"] => eapply cpaco"+str(n)+"_unfold in H; [|eauto with paco|eauto with paco]")
print ("  end.")
print ()

print ("(** ** cbase")
print ("*)")
print ()
print ('Tactic Notation "cbase_" :=')
print ("  match goal with")
for n in range(relsize+1):
    print ("  | [|- context[cpaco"+str(n)+"]] => eapply cpaco"+str(n)+"_base")
print ("  end.")
print ("Ltac cbase := repeat red; under_forall ltac:(cbase_).")
print ()

print ("(** ** cstep")
print ("*)")
print ()
print ('Tactic Notation "cstep_" :=')
print ("  match goal with")
for n in range(relsize+1):
    print ("  | [|- context[cpaco"+str(n)+"]] => eapply cpaco"+str(n)+"_step; [eauto with paco|]")
print ("  end.")
print ("Ltac cstep := repeat red; under_forall ltac:(cstep_).")
print ()

print ("(** ** cupaco")
print ("*)")
print ()
print ('Tactic Notation "cupaco_" :=')
print ("  match goal with")
for n in range(relsize+1):
    print ("  | [|- context[cpaco"+str(n)+"]] => eapply cpaco"+str(n)+"_cupaco; [eauto with paco|eauto with paco|]")
print ("  end.")
print ("Ltac cupaco := repeat red; under_forall ltac:(cupaco_).")
print ()

print ("(** ** cclo H")
print ("*)")
print ()
print ('Tactic Notation "cclo_" constr(H) :=')
print ("  match goal with")
for n in range(relsize+1):
    print ("  | [|- context[cpaco"+str(n)+"]]  => eapply cpaco"+str(n)+"_uclo; [| |eapply H|]; [eauto with paco|eauto with paco|..]")
print ("  end.")
print ("Ltac cclo H := repeat red; under_forall ltac:(cclo_ H).")
print ()

print ("(** ** ccofix CIH [with r]")
print ("*)")
print ()
print ('Tactic Notation "ccofix" ident(CIH) "with" ident(r) :=')
print ("  repeat red;")
print ("  generalize _paco_mark_cons; intros;")
print ("  match goal with")
for n in range(relsize+1):
    print ("  | [|- context[cpaco"+str(n)+"]]  =>")
    print ("    paco_revert_hyp _paco_mark;")
    print ("    pcofix CIH using @cpaco"+str(n)+"_cofix with r; [eauto with paco|eauto with paco|eauto with paco; try contradiction|]")
print ("  end.")
print ('Tactic Notation "ccofix" ident(CIH) := ccofix CIH with r.')
print ()

