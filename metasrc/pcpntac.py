from __future__ import print_function
import sys
from pacolib import *

if len(sys.argv) < 2:
    sys.stderr.write('\nUsage: '+sys.argv[0]+' relsize\n\n')
    sys.exit(1)

relsize = int(sys.argv[1])

print ("Require Import pacotac_internal pacotac pacoall pcpnall.")
print ()

print ("(** ** uinit")
print ("*)")
print ()
print ('Tactic Notation "uinit_" :=')
print ("  match goal with")
for n in range(relsize+1):
    print ("  | [|- context[paco"+str(n)+"]] => eapply ucpn"+str(n)+"_init; [eauto with paco|]")
print ("  end.")
print ('Tactic Notation "uinit" := repeat red; under_forall ltac:(uinit_).')
print ()

print ("(** ** ufinal")
print ("*)")
print ()
print ('Tactic Notation "ufinal_" :=')
print ("  match goal with")
for n in range(relsize+1):
    print ("  | [|- context[dcpn"+str(n)+"]] => first[eapply ucpn"+str(n)+"_final | eapply pcpn"+str(n)+"_final]")
print ("  end.")
print ('Tactic Notation "ufinal" := repeat red; under_forall ltac:(ufinal_).')
print ()

print ("(** ** ucpn_fold")
print ("*)")
print ()
print ('Tactic Notation "ucpn_fold_" :=')
print ("  match goal with")
for n in range(relsize+1):
    print ("  | [|- context[dcpn"+str(n)+" ?gf ?r]] => first [apply ucpn"+str(n)+"_id | apply pcpn"+str(n)+"_id]")
print ("  end.")
print ('Tactic Notation "ucpn_fold" := repeat red; under_forall ltac:(ucpn_fold_).')
print ()

print ("(** ** uunfold H")
print ("*)")
print ()
print ('Ltac uunfold H :=')
print ("  repeat red in H;")
print ("  let G := type of H in");
print ("  match G with")
for n in range(relsize+1):
    print ("  | context[dcpn"+str(n)+"] => first[eapply pcpn"+str(n)+"_unfold in H | eapply ucpn"+str(n)+"_unfold in H]; [|eauto with paco]")
print ("  end.")
print ()

print ("(** ** ubase")
print ("*)")
print ()
print ('Tactic Notation "ubase_" :=')
print ("  match goal with")
for n in range(relsize+1):
    print ("  | [|- context[dcpn"+str(n)+"]] => eapply ucpn"+str(n)+"_base")
print ("  end.")
print ("Ltac ubase := repeat red; under_forall ltac:(ubase_).")
print ()

print ("(** ** ucpn")
print ("*)")
print ()
print ('Tactic Notation "ucpn_" :=')
print ("  match goal with")
for n in range(relsize+1):
    print ("  | [|- context[dcpn"+str(n)+"]] => eapply ucpn"+str(n)+"_ucpn; [eauto with paco|]")
print ("  end.")
print ("Ltac ucpn := repeat red; under_forall ltac:(ucpn_).")
print ()

print ("(** ** ustep")
print ("*)")
print ()
print ('Tactic Notation "ustep_" :=')
print ("  match goal with")
for n in range(relsize+1):
    print ("  | [|- context[dcpn"+str(n)+"]] => first[eapply ucpn"+str(n)+"_step | eapply pcpn"+str(n)+"_step]")
print ("  end.")
print ("Ltac ustep := repeat red; under_forall ltac:(ustep_).")
print ()

print ("(** ** uclo H")
print ("*)")
print ()
print ('Tactic Notation "uclo_" constr(H) :=')
print ("  match goal with")
for n in range(relsize+1):
    print ("  | [|- context[dcpn"+str(n)+"]]  => first[eapply ucpn"+str(n)+"_clo; [|eapply H|]; [eauto with paco|..] | eapply pcpn"+str(n)+"_clo; [|eapply H|]; [eauto with paco|..]]")
print ("  end.")
print ("Ltac uclo H := repeat red; under_forall ltac:(uclo_ H).")
print ()

print ("(** ** ucofix CIH [with r]")
print ("*)")
print ()
print ('Tactic Notation "ucofix" ident(CIH) "with" ident(r) :=')
print ("  repeat red;")
print ("  generalize _paco_mark_cons; intros;")
print ("  match goal with")
for n in range(relsize+1):
    print ("  | [|- context[dcpn"+str(n)+"]] =>")
    print ("    try left;")
    print ("    paco_revert_hyp _paco_mark;")
    print ("    pcofix CIH using @pcpn"+str(n)+"_cofix with r; [eauto with paco|]")
print ("  end.")
print ('Tactic Notation "ucofix" ident(CIH) := ucofix CIH with r.')
print ()
