from __future__ import print_function
import sys
from pacolib import *

if len(sys.argv) < 2: 
    sys.stderr.write('\nUsage: '+sys.argv[0]+' relsize\n\n') 
    sys.exit(1) 

relsize = int(sys.argv[1])

print ("Require Import pacoall.")
print ()

print ("(** ** gcpn_fold")
print ("*)")
print ()
print ("Ltac gcpn_fold :=")
print ("  match goal with ")
for n in range(relsize+1):
    print ("  | [|- ?gf (cpn"+str(n)+" _ ?r)"+n*" _"+"] => change (gf (cpn"+str(n)+" gf r)) with (gcpn"+str(n)+" gf r)")
print ("  end.")
print ()

print ("(** ** ucompat")
print ("*)")
print ()
print ("Ltac ucompat :=")
print ("  match goal with ")
for n in range(relsize+1):
    print ("  | [|- context[cpn"+str(n)+"]] => eapply wcompat"+str(n)+"_sound; eauto with paco")
print ("  end.")
print ()

print ("(** ** uinit")
print ("*)")
print ()
print ("Ltac uinit :=")
print ("  repeat red;")
print ("  match goal with ")
for n in range(relsize+1):
    print ("  | [|- context[paco"+str(n)+"]] => under_forall ltac:(eapply cpn"+str(n)+"_init; [eauto with paco|])")
print ("  end.")
print ()

print ("(** ** ustep")
print ("*)")
print ()
print ("Ltac ustep :=")
print ("  match goal with ")
for n in range(relsize+1):
    print ("  | [|- context[cpn"+str(n)+"]] => under_forall ltac:(eapply cpn"+str(n)+"_step; [eauto with paco|])")
print ("  end.")
print ()

print ("(** ** uclo H")
print ("*)")
print ()
print ("Ltac uclo H :=")
print ("  match goal with ")
for n in range(relsize+1):
    print ("  | [|- context[cpn"+str(n)+"]]  => under_forall ltac:(eapply cpn"+str(n)+"_clo; [|eapply H|]; [eauto with paco|])")
    print ("  | [|- context[gcpn"+str(n)+"]] => under_forall ltac:(eapply gcpn"+str(n)+"_clo; [|eapply H|]; [eauto with paco|])")
print ("  end.")
print ()

print ("(** ** ufinal")
print ("*)")
print ()
print ("Ltac ufinal :=")
print ("  match goal with ")
for n in range(relsize+1):
    print ("  | [|- context[cpn"+str(n)+"]]  => under_forall ltac:(eapply cpn"+str(n)+"_final; [eauto with paco|])")
    print ("  | [|- context[gcpn"+str(n)+"]] => under_forall ltac:(eapply gcpn"+str(n)+"_final; [eauto with paco|])")
print ("  end.")
print ()

print ("(** ** ucofix CIH")
print ("*)")
print ()
print ("Ltac ucofix CIH :=")
print ("  match goal with ")
for n in range(relsize+1):
    print ("  | [|- context[cpn"+str(n)+"]]  =>")
    print ("    under_forall ltac:(eapply cpn"+str(n)+"_from_paco; [eauto with paco|]);")
    print ("    pcofix CIH;")
    print ("    under_forall ltac:(eapply gcpn"+str(n)+"_to_paco; [eauto with paco|])")
    print ("  | [|- context[gcpn"+str(n)+"]] =>")
    print ("    under_forall ltac:(eapply gcpn"+str(n)+"_from_paco; [eauto with paco|]);")
    print ("    pcofix CIH;")
    print ("    under_forall ltac:(eapply gcpn"+str(n)+"_to_paco; [eauto with paco|])")
print ("  end.")
print ()

print ("(** ** pfold_reverse ")
print ("*)")
print ()
print ("Ltac pfold_reverse :=")
print ("  repeat red;")
print ("  match goal with ")
for n in range(relsize+1):
    print ("  | [|- _ (upaco"+str(n)+" ?gf _)"+n*" _"+"] => eapply (paco"+str(n)+"_unfold (gf := gf))")
print ("  end;")
print ("  eauto with paco.")
print ()

print ("(** ** punfold_reverse H ")
print ("*)")
print ()
print ("Ltac punfold_reverse H :=")
print ("  repeat red in H;")
print ("  let PP := type of H in")
print ("  match PP with")
for n in range(relsize+1):
    print ("  | _ (upaco"+str(n)+" ?gf _)"+n*" _"+" => eapply (paco"+str(n)+"_fold gf) in H")
print ("  end;")
print ("  eauto with paco.")
print ()
