from __future__ import print_function
import sys
from pacolib import *

if len(sys.argv) < 2:
    sys.stderr.write('\nUsage: '+sys.argv[0]+' relsize\n\n')
    sys.exit(1)

relsize = int(sys.argv[1])

print ("From Paco Require Import pacotac_internal pacotac pacoall gpacoall.")
print ()

print ("(** ** ginit")
print ("*)")
print ()
print ('Tactic Notation "ginit_" :=')
print ("  match goal with")
for n in range(relsize+1):
    print ("  | [|- context[paco"+str(n)+"]] => eapply gpaco"+str(n)+"_init; [eauto with paco|eauto with paco|]")
print ("  end.")
print ("Ltac ginit := repeat red; under_forall ltac:(ginit_).")
print ()

print ("(** ** gfinal")
print ("*)")
print ()
print ('Tactic Notation "gfinal_" :=')
print ("  match goal with")
for n in range(relsize+1):
    print ("  | [|- context[gpaco"+str(n)+"]] => eapply gpaco"+str(n)+"_final; [eauto with paco|]")
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
    print ("  | context[gpaco"+str(n)+"] => eapply gpaco"+str(n)+"_unfold in H; [|eauto with paco]")
print ("  end.")
print ()

print ("(** ** gunfoldbot H")
print ("*)")
print ()
print ('Ltac gunfoldbot H :=')
print ("  repeat red in H;")
print ("  let G := type of H in");
print ("  match G with")
for n in range(relsize+1):
    print ("  | context[gpaco"+str(n)+"] => eapply gpaco"+str(n)+"_unfold_bot in H; [|eauto with paco|eauto with paco]")
print ("  end.")
print ()

print ("(** ** gbase")
print ("*)")
print ()
print ('Tactic Notation "gbase_" :=')
print ("  match goal with")
for n in range(relsize+1):
    print ("  | [|- context[gpaco"+str(n)+"]] => eapply gpaco"+str(n)+"_base")
print ("  end.")
print ("Ltac gbase := repeat red; under_forall ltac:(gbase_).")
print ()

print ("(** ** gstep")
print ("*)")
print ()
print ('Tactic Notation "gstep_" :=')
print ("  match goal with")
for n in range(relsize+1):
    print ("  | [|- context[gpaco"+str(n)+"]] => eapply gpaco"+str(n)+"_step; [eauto with paco|]")
print ("  end.")
print ("Ltac gstep := repeat red; under_forall ltac:(gstep_).")
print ()

print ("(** ** gupaco")
print ("*)")
print ()
print ('Tactic Notation "gupaco_" :=')
print ("  match goal with")
for n in range(relsize+1):
    print ("  | [|- context[gpaco"+str(n)+"]] => eapply gpaco"+str(n)+"_gupaco; [eauto with paco|]")
print ("  end.")
print ("Ltac gupaco := repeat red; under_forall ltac:(gupaco_).")
print ()

print ("(** ** gpaco")
print ("*)")
print ()
print ('Tactic Notation "gpaco_" :=')
print ("  match goal with")
for n in range(relsize+1):
    print ("  | [|- context[gpaco"+str(n)+"]] => eapply gpaco"+str(n)+"_gpaco; [eauto with paco|]")
print ("  end.")
print ("Ltac gpaco := repeat red; under_forall ltac:(gpaco_).")
print ()

print ("(** ** gclo")
print ("*)")
print ()
print ('Tactic Notation "gclo_" :=')
print ("  match goal with")
for n in range(relsize+1):
    print ("  | [|- context[gpaco"+str(n)+"]]  => eapply gpaco"+str(n)+"_gupaco, gpaco"+str(n)+"_clo; [eauto with paco|]")
print ("  end.")
print ("Ltac gclo := repeat red; under_forall ltac:(gclo_).")
print ()

print ("(** ** grclo")
print ("*)")
print ()
print ('Tactic Notation "grclo_" :=')
print ("  match goal with")
for n in range(relsize+1):
    print ("  | [|- context[gpaco"+str(n)+"]]  => eapply gpaco"+str(n)+"_gupaco, gpaco"+str(n)+"_rclo; [eauto with paco|]")
print ("  end.")
print ("Ltac grclo := repeat red; under_forall ltac:(grclo_).")
print ()

print ("(** ** guclo H")
print ("*)")
print ()
print ('Tactic Notation "guclo_" constr(H) :=')
print ("  match goal with")
for n in range(relsize+1):
    print ("  | [|- context[gpaco"+str(n)+"]]  => eapply gpaco"+str(n)+"_uclo; [|eapply H|]; eauto with paco")
print ("  end.")
print ("Ltac guclo H := repeat red; under_forall ltac:(guclo_ H).")
print ()

print ("(** ** glecpn")
print ("*)")
print ()
print ('Tactic Notation "glecpn" :=')
print ("  repeat red;")
print ("  match goal with")
for n in range(relsize+1):
    print ("  | [|- context[gpaco"+str(n)+"]]  => eapply cpn"+str(n)+"_uclo; [eauto with paco| |]")
print ("  end.")
print ()

print ("(** ** gcofix CIH [with r]")
print ("*)")
print ()
print ('Tactic Notation "gcofix" ident(CIH) "with" ident(r) :=')
print ("  repeat red;")
print ("  generalize _paco_mark_cons; intros;")
print ("  match goal with")
for n in range(relsize+1):
    print ("  | [|- context[@gpaco"+str(n)+n*" _"+" ?gf]]  =>")
    print ("    paco_revert_hyp _paco_mark;")
    print ("    pcofix CIH using (@gpaco"+str(n)+"_cofix"+n*" _"+" gf) with r; [eauto with paco|]")
print ("  end.")
print ('Tactic Notation "gcofix_old" ident(CIH) "with" ident(r) :=')
print ("  repeat red;")
print ("  generalize _paco_mark_cons; intros;")
print ("  match goal with")
for n in range(relsize+1):
    print ("  | [|- context[gpaco"+str(n)+"]]  =>")
    print ("    paco_revert_hyp _paco_mark;")
    print ("    pcofix CIH using @gpaco"+str(n)+"_cofix with r; [eauto with paco|]")
print ("  end.")

print ('Tactic Notation "gcofix" ident(CIH) := first [gcofix CIH with r | gcofix_old CIH with r].')
print ()

