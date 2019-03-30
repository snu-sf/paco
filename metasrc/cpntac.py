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
    print ("  | [|- context[fcpn"+str(n)+"]] => eapply fcpn"+str(n)+"_final; [eauto with paco|]")
    print ("  | [|- context[cpn"+str(n)+"]]  => eapply cpn"+str(n)+"_final; [eauto with paco|]")
print ("  end.")
print ("Ltac ufinal := under_forall ltac:(ufinal_).")
print ()

print ("(** ** fcpn_fold")
print ("*)")
print ()
print ("Ltac fcpn_fold :=")
print ("  match goal with")
for n in range(relsize+1):
    print ("  | [|- ?gf (cpn"+str(n)+" _ ?r)"+n*" _"+"] => change (gf (cpn"+str(n)+" gf r)) with (fcpn"+str(n)+" gf r)")
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

print ("(** ** uunfold H")
print ("*)")
print ()
print ('Ltac uunfold H :=')
print ("  repeat red in H;")
print ("  let G := type of H in");
print ("  match G with")
for n in range(relsize+1):
    print ("  | context[cpn"+str(n)+"] => eapply cpn"+str(n)+"_unfold in H; [|eauto with paco]")
print ("  end.")
print ()

print ("(** ** ucpn")
print ("*)")
print ()
print ('Tactic Notation "ucpn_" :=')
print ("  match goal with")
for n in range(relsize+1):
    print ("  | [|- context[cpn"+str(n)+"]] => eapply cpn"+str(n)+"_cpn; [eauto with paco|]")
print ("  end.")
print ("Ltac ucpn := repeat red; under_forall ltac:(ucpn_).")
print ()

print ("(** ** ustep")
print ("*)")
print ()
print ('Tactic Notation "ustep_" :=')
print ("  match goal with")
for n in range(relsize+1):
    print ("  | [|- context[cpn"+str(n)+"]] => eapply cpn"+str(n)+"_step; [eauto with paco|]")
print ("  end.")
print ("Ltac ustep := repeat red; under_forall ltac:(ustep_).")
print ()

print ("(** ** uclo H")
print ("*)")
print ()
print ('Tactic Notation "guclo__" constr(H) :=')
print ("  match goal with")
for n in range(relsize+1):
    print ("  | [|- context[fcpn"+str(n)+"]] => eapply fcpn"+str(n)+"_clo; [|eapply H|]; [eauto with paco|]")
print ("  end.")
print ("Ltac guclo_ H := under_forall ltac:(guclo__ H).")
print ('Tactic Notation "uclo__" constr(H) :=')
print ("  match goal with")
for n in range(relsize+1):
    print ("  | [|- context[cpn"+str(n)+"]]  => eapply cpn"+str(n)+"_clo; [|eapply H|]; [eauto with paco|]")
print ("  end.")
print ("Ltac uclo_ H := repeat red; under_forall ltac:(uclo__ H).")
print ("Ltac uclo H := first[ guclo_ H | uclo_ H ].")
print ()

print ("(** ** ucofix CIH [with r]")
print ("*)")
print ()
print ('Tactic Notation "gucofix_" ident(CIH) "with" ident(r) :=')
print ("  generalize _paco_mark_cons; intros;")
print ("  match goal with")
for n in range(relsize+1):
    print ("  | [|- context[fcpn"+str(n)+"]] =>")
    print ("    (eapply fcpn"+str(n)+"_from_paco; [eauto with paco|]); paco_revert_hyp _paco_mark;")
    print ("    pcofix CIH with r;")
    print ("    under_forall ltac:(eapply fcpn"+str(n)+"_to_paco; [eauto with paco|])")
print ("  end.")
print ('Tactic Notation "ucofix_" ident(CIH) "with" ident(r) :=')
print ("  repeat red;")
print ("  generalize _paco_mark_cons; intros;")
print ("  match goal with")
for n in range(relsize+1):
    print ("  | [|- context[cpn"+str(n)+"]]  =>")
    print ("    (eapply cpn"+str(n)+"_from_paco; [eauto with paco|]); paco_revert_hyp _paco_mark;")
    print ("    pcofix CIH with r;")
    print ("    under_forall ltac:(eapply fcpn"+str(n)+"_to_paco; [eauto with paco|])")
print ("  end.")
print ('Tactic Notation "ucofix" ident(CIH) "with" ident(r) :=')
print ("  first[ gucofix_ CIH with r | ucofix_ CIH with r ].")
print ('Tactic Notation "ucofix" ident(CIH) := ucofix CIH with r.')
print ()
