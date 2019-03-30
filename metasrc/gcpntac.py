from __future__ import print_function
import sys
from pacolib import *

if len(sys.argv) < 2:
    sys.stderr.write('\nUsage: '+sys.argv[0]+' relsize\n\n')
    sys.exit(1)

relsize = int(sys.argv[1])

print ("Require Import pacotac_internal pacotac pacoall cpnall gcpnall.")
print ()

print ("(** ** ginit")
print ("*)")
print ()
print ('Tactic Notation "ginit_" :=')
print ("  match goal with")
for n in range(relsize+1):
    print ("  | [|- context[cpn"+str(n)+"]] => eapply gcpn"+str(n)+"_init; [eauto with paco|]")
print ("  end.")
print ("Ltac ginit := repeat red; under_forall ltac:(ginit_).")
print ()

print ("(** ** gfinal")
print ("*)")
print ()
print ('Tactic Notation "gfinal_" :=')
print ("  match goal with")
for n in range(relsize+1):
    print ("  | [|- context[gcpn"+str(n)+"]]  => eapply gcpn"+str(n)+"_final")
print ("  end.")
print ("Ltac gfinal := repeat red; under_forall ltac:(gfinal_).")
print ()

print ("(** ** gunfold H")
print ("*)")
print ()
print ('Ltac gunfold H :=')
print ("  repeat red in H;")
print ("  let G := type of H in");
print ("  match G with")
for n in range(relsize+1):
    print ("  | context[gcpn"+str(n)+"] => eapply gcpn"+str(n)+"_unfold in H; [|eauto with paco]")
print ("  end.")
print ()

print ("(** ** gbase")
print ("*)")
print ()
print ('Tactic Notation "gbase_" :=')
print ("  match goal with")
for n in range(relsize+1):
    print ("  | [|- context[gcpn"+str(n)+"]] => eapply gcpn"+str(n)+"_base")
print ("  end.")
print ("Ltac gbase := repeat red; under_forall ltac:(gbase_).")
print ()

print ("(** ** gcpn")
print ("*)")
print ()
print ('Tactic Notation "gcpn_" :=')
print ("  match goal with")
for n in range(relsize+1):
    print ("  | [|- context[gcpn"+str(n)+"]] => eapply gcpn"+str(n)+"_cpn; [eauto with paco|]")
print ("  end.")
print ("Ltac gcpn := repeat red; under_forall ltac:(gcpn_).")
print ()

print ("(** ** gstep")
print ("*)")
print ()
print ('Tactic Notation "gstep_" :=')
print ("  match goal with")
for n in range(relsize+1):
    print ("  | [|- context[gcpn"+str(n)+"]] => eapply gcpn"+str(n)+"_step; [eauto with paco|]")
print ("  end.")
print ("Ltac gstep := repeat red; under_forall ltac:(gstep_).")
print ()

print ("(** ** gclo H")
print ("*)")
print ()
print ('Tactic Notation "gclo_" constr(H) :=')
print ("  match goal with")
for n in range(relsize+1):
    print ("  | [|- context[gcpn"+str(n)+"]]  => eapply gcpn"+str(n)+"_clo; [|eapply H|]; [eauto with paco|]")
print ("  end.")
print ("Ltac gclo H := repeat red; under_forall ltac:(gclo_ H).")
print ()

print ("(** ** gcofix CIH [with r]")
print ("*)")
print ()
print ('Tactic Notation "gcofix" ident(CIH) "with" ident(r) :=')
print ("  repeat red;")
print ("  generalize _paco_mark_cons; intros;")
print ("  match goal with")
for n in range(relsize+1):
    print ("  | [|- context[gcpn"+str(n)+"]]  =>")
    print ("    paco_revert_hyp _paco_mark;")
    print ("    pcofix CIH using @gcpn"+str(n)+"_cofix with r; [eauto with paco|eauto with paco; try contradiction|]")
print ("  end.")
print ('Tactic Notation "gcofix" ident(CIH) := gcofix CIH with r.')
print ()

