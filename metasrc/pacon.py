from __future__ import print_function
import sys
from pacolib import *

if len(sys.argv) < 2: 
    sys.stderr.write('\nUsage: '+sys.argv[0]+' relsize mutsize\n\n') 
    sys.exit(1) 

mutsize = int(sys.argv[1])

print ('Require Export paconotation pacotacuser.')
print ('Require Import pacotac paconotation_internal.')
print ('Set Implicit Arguments.')
print ('')

n = 1

print ('(** ** Predicates of Arity '+str(n))
print ('*)')
print ('')

for m in range(1,mutsize+1):
    print ('Section Arg'+str(n)+lev(m)+'_def.')
    for i in range(n):
        print ('Variable T'+str(i)+' : '+ifpstr(i,'forall'),end='')
        for j in range(i):
            print (' (x'+str(j)+': @T'+str(j)+itrstr(" x",j)+')',end='')
        print (ifpstr(i,', ')+'Type.')
    print ('Variable'+itridx(" gf",m)+' : '+m*('rel'+str(n)+itrstr(" T",n)+' -> ')+'rel'+str(n)+itrstr(" T",n)+'.')
    for i in range(m):
        print ('Arguments gf'+idx(m,i)+' : clear implicits.')
    print ('')
    print ('CoInductive ',end='')
    for i in range(m):
        print (ifpstr(i,"with ")+'paco'+lev(m)+idx(m,i)+'('+itridx(' r',m)+': rel'+str(n)+itrstr(' T',n)+')'+itrstr(" x",n)+' : Prop :=')
        print ('| paco'+lev(m)+idx(m,i)+'_pfold'+itridx(' pco',m))
        for j in range(m):
            print ('    (LE : pco'+idx(m,j)+' <'+str(n)+'= (paco'+lev(m)+idx(m,j)+itridx(' r',m)+' \\'+str(n)+'/ r'+idx(m,j)+'))')
        print ('    (SIM: gf'+idx(m,i)+itridx(' pco',m)+itrstr(" x",n)+')')
    print ('.')
    for i in range(m):
        print ('Definition ',end='')
        print ('upaco'+lev(m)+idx(m,i)+'('+itridx(' r',m)+': rel'+str(n)+itrstr(' T',n)+')'+' := '+'paco'+lev(m)+idx(m,i)+itridx(' r',m)+' \\'+str(n)+'/ r'+idx(m,i),end='')
        print ('.')
    print ('End Arg'+str(n)+lev(m)+'_def.')
    for i in range(m):
        print ('Arguments paco'+lev(m)+idx(m,i)+ifpstr(n,' ['+itrstr(" T",n)+' ].'," : clear implicits."))
        print ('Arguments upaco'+lev(m)+idx(m,i)+ifpstr(n,' ['+itrstr(" T",n)+' ].'," : clear implicits."))
        print ('Hint Unfold upaco'+lev(m)+idx(m,i)+'.')
    print ('')

print ("(* Less than or equal - internal use only *)")
print ("Notation \"p <_paco_"+str(n)+"= q\" :=")
print ("  (forall"+itrstr(" _paco_x",n)+" (PR: p"+itrstr(" _paco_x",n)+" : Prop), q"+itrstr(" _paco_x",n)+" : Prop)")
print ("  (at level 50, no associativity).")
print ('')

for m in range (1,mutsize+1):
    print ('(** '+str(m)+' Mutual Coinduction *)')
    print ('')
    print ('Section Arg'+str(n)+'_'+str(m)+'.')
    print ('')
    print ("Definition monotone"+lev(m)+itrstr(" T",n)+" (gf: "+m*("rel"+str(n)+itrstr(" T",n)+" -> ")+"rel"+str(n)+itrstr(" T",n)+") :=")
    print ("  forall"+itrstr(" x",n)+itridx(" r",m)+itridx(" r'",m)+" (IN: gf"+itridx(" r",m)+itrstr(" x",n)+") ",end='')
    for i in range(m):
        print ("(LE"+idx(m,i)+": r"+idx(m,i)+" <"+str(n)+"= r'"+idx(m,i)+")",end='')
    print (", gf"+itridx(" r'",m)+itrstr(" x",n)+".")
    print ('')
    print ("Definition _monotone"+lev(m)+itrstr(" T",n)+" (gf: "+m*("rel"+str(n)+itrstr(" T",n)+" -> ")+"rel"+str(n)+itrstr(" T",n)+") :=")
    print ("  forall"+itridx(" r",m)+itridx(" r'",m),end='')
    for i in range(m):
        print ("(LE"+idx(m,i)+": r"+idx(m,i)+" <"+str(n)+"= r'"+idx(m,i)+")",end='')
    print (", gf"+itridx(" r",m)+' <'+str(n)+'== gf'+itridx(" r'",m)+'.')
    print ('')
    print ("Lemma monotone"+lev(m)+'_eq'+itrstr(" T",n)+" (gf: "+m*("rel"+str(n)+itrstr(" T",n)+" -> ")+"rel"+str(n)+itrstr(" T",n)+") :")
    print ("  monotone"+lev(m)+' gf <-> _monotone'+lev(m)+' gf.')
    print ("Proof. unfold monotone"+lev(m)+', _monotone'+lev(m)+', le'+str(n)+'. split; eauto. Qed.')
    print ('')

    for i in range(n):
        print ('Variable T'+str(i)+' : '+ifpstr(i,'forall'),end='')
        for j in range(i):
            print (' (x'+str(j)+': @T'+str(j)+itrstr(" x",j)+')',end='')
        print (ifpstr(i,', ')+'Type.')
    print ('Variable'+itridx(" gf",m)+' : '+m*('rel'+str(n)+itrstr(" T",n)+' -> ')+'rel'+str(n)+itrstr(" T",n)+'.')
    for i in range(m):
        print ('Arguments gf'+idx(m,i)+' : clear implicits.')
    print ('')
    for i in range(m):
        print ('Theorem paco'+lev(m)+idx(m,i)+'_acc: forall')
        print ('  l'+itridx(' r',m)+' (OBG: forall rr (INC: r'+idx(m,i)+' <'+str(n)+'= rr) (CIH: l <'+str(n)+'= rr), l <'+str(n)+'= paco'+lev(m)+idx(m,i)+itridx(" gf",m),end='')
        for j in range(m):
            if j == i:
                print (' rr',end='')
            else:
                print (' r'+idx(m,j),end='')
        print ('),')
        print ('  l <'+str(n)+'= paco'+lev(m)+idx(m,i)+itridx(" gf",m)+itridx(' r',m)+'.')
        print ('Proof.')
        print ('  intros; assert (SIM: paco'+lev(m)+idx(m,i)+itridx(" gf",m),end='')
        for j in range(m):
            if j == i:
                print (' (r'+idx(m,j)+' \\'+str(n)+'/ l)',end='')
            else:
                print (' r'+idx(m,j),end='')
        print (itrstr(" x",n)+') by eauto.')
        print ('  clear PR; repeat (try left; do '+str(n+1)+' paco_revert; paco_cofix_auto).')
        print ('Qed.')
        print ('')
    for i in range(m):
        print ('Theorem paco'+lev(m)+idx(m,i)+'_mon: monotone'+lev(m)+' (paco'+lev(m)+idx(m,i)+itridx(" gf",m)+').')
        print ('Proof. paco_cofix_auto; repeat (left; do '+str(n+1)+' paco_revert; paco_cofix_auto). Qed.')
        print ('')
    for i in range(m):
        print ('Theorem paco'+lev(m)+idx(m,i)+'_mult_strong: forall'+itridx(' r',m)+',')
        print ('  paco'+lev(m)+idx(m,i)+itridx(" gf",m),end='')
        for j in range(m):
            print (' (upaco'+lev(m)+idx(m,j)+itridx(" gf",m)+itridx(' r',m)+')',end='')
        print (' <'+str(n)+'= paco'+lev(m)+idx(m,i)+itridx(" gf",m)+itridx(' r',m)+'.')
        print ('Proof. paco_cofix_auto; repeat (left; do '+str(n+1)+' paco_revert; paco_cofix_auto). Qed.')
        print ('')
    for i in range(m):
        print ('Corollary paco'+lev(m)+idx(m,i)+'_mult: forall'+itridx(' r',m)+',')
        print ('  paco'+lev(m)+idx(m,i)+itridx(" gf",m)+itridx(' (paco'+lev(m),m,itridx(" gf",m)+itridx(' r',m)+')')+' <'+str(n)+'= paco'+lev(m)+idx(m,i)+itridx(" gf",m)+itridx(' r',m)+'.')
        print ('Proof. intros; eapply paco'+lev(m)+idx(m,i)+'_mult_strong, paco'+lev(m)+idx(m,i)+'_mon; eauto. Qed.')
        print ('')
    for i in range(m):
        print ('Theorem paco'+lev(m)+idx(m,i)+'_fold: forall'+itridx(' r',m)+',')
        print ('  gf'+idx(m,i),end='')
        for j in range(m):
            print (' (upaco'+lev(m)+idx(m,j)+itridx(" gf",m)+itridx(' r',m)+')',end='')
        print (' <'+str(n)+'= paco'+lev(m)+idx(m,i)+itridx(" gf",m)+itridx(' r',m)+'.')
        print ('Proof. intros; econstructor; ['+m*' |'+'eauto]; eauto. Qed.')
        print ('')
    for i in range(m):
        print ('Theorem paco'+lev(m)+idx(m,i)+'_unfold: forall'+itridx(' (MON: monotone'+lev(m)+' gf',m,')')+itridx(' r',m)+',')
        print ('  paco'+lev(m)+idx(m,i)+itridx(" gf",m)+itridx(' r',m)+' <'+str(n)+'= gf'+idx(m,i),end='')
        for j in range(m):
            print (' (upaco'+lev(m)+idx(m,j)+itridx(" gf",m)+itridx(' r',m)+')',end='')
        print ('.')
        print ('Proof. unfold monotone'+lev(m)+'; intros; destruct PR; eauto. Qed.')
        print ('')

    for i in range(m):
        print ('Theorem _paco'+lev(m)+idx(m,i)+'_acc: forall')
        print ('  l'+itridx(' r',m)+' (OBG: forall rr (INC: r'+idx(m,i)+' <'+str(n)+'== rr) (CIH: l <'+str(n)+'== rr), l <'+str(n)+'== paco'+lev(m)+idx(m,i)+itridx(" gf",m),end='')
        for j in range(m):
            if j == i:
                print (' rr',end='')
            else:
                print (' r'+idx(m,j),end='')
        print ('),')
        print ('  l <'+str(n)+'== paco'+lev(m)+idx(m,i)+itridx(" gf",m)+itridx(' r',m)+'.')
        print ('Proof. unfold le1. eapply paco'+lev(m)+idx(m,i)+'_acc. Qed.')
        print ('')
    for i in range(m):
        print ('Theorem _paco'+lev(m)+idx(m,i)+'_mon: _monotone'+lev(m)+' (paco'+lev(m)+idx(m,i)+itridx(" gf",m)+').')
        print ('Proof. apply monotone'+lev(m)+'_eq. eapply paco'+lev(m)+idx(m,i)+'_mon. Qed.')
        print ('')
    for i in range(m):
        print ('Theorem _paco'+lev(m)+idx(m,i)+'_mult_strong: forall'+itridx(' r',m)+',')
        print ('  paco'+lev(m)+idx(m,i)+itridx(" gf",m),end='')
        for j in range(m):
            print (' (upaco'+lev(m)+idx(m,j)+itridx(" gf",m)+itridx(' r',m)+')',end='')
        print (' <'+str(n)+'== paco'+lev(m)+idx(m,i)+itridx(" gf",m)+itridx(' r',m)+'.')
        print ('Proof. unfold le1. eapply paco'+lev(m)+idx(m,i)+'_mult_strong. Qed.')
        print ('')
    for i in range(m):
        print ('Theorem _paco'+lev(m)+idx(m,i)+'_fold: forall'+itridx(' r',m)+',')
        print ('  gf'+idx(m,i),end='')
        for j in range(m):
            print (' (upaco'+lev(m)+idx(m,j)+itridx(" gf",m)+itridx(' r',m)+')',end='')
        print (' <'+str(n)+'== paco'+lev(m)+idx(m,i)+itridx(" gf",m)+itridx(' r',m)+'.')
        print ('Proof. unfold le1. eapply paco'+lev(m)+idx(m,i)+'_fold. Qed.')
        print ('')
    for i in range(m):
        print ('Theorem _paco'+lev(m)+idx(m,i)+'_unfold: forall'+itridx(' (MON: _monotone'+lev(m)+' gf',m,')')+itridx(' r',m)+',')
        print ('  paco'+lev(m)+idx(m,i)+itridx(" gf",m)+itridx(' r',m)+' <'+str(n)+'== gf'+idx(m,i),end='')
        for j in range(m):
            print (' (upaco'+lev(m)+idx(m,j)+itridx(" gf",m)+itridx(' r',m)+')',end='')
        print ('.')
        print ('Proof.')
        print ('  unfold le1. repeat_intros '+str(m)+'.')
        print ('  eapply paco'+lev(m)+idx(m,i)+'_unfold; apply monotone'+lev(m)+'_eq; eauto.')
        print ('Qed.')
        print ('')

    print ('End Arg'+str(n)+'_'+str(m)+'.')
    print ('')
    print ('Hint Unfold monotone'+lev(m)+'.')
    for i in range(m):
        print ('Hint Resolve paco'+lev(m)+idx(m,i)+'_fold.')
    print ('')
    for i in range(m):
        print ('Arguments paco'+lev(m)+idx(m,i)+'_acc'+ifpstr(n,'            ['+itrstr(" T",n)+' ].'," : clear implicits."))
    for i in range(m):
        print ('Arguments paco'+lev(m)+idx(m,i)+'_mon'+ifpstr(n,'            ['+itrstr(" T",n)+' ].'," : clear implicits."))
    for i in range(m):
        print ('Arguments paco'+lev(m)+idx(m,i)+'_mult_strong'+ifpstr(n,'    ['+itrstr(" T",n)+' ].'," : clear implicits."))
    for i in range(m):
        print ('Arguments paco'+lev(m)+idx(m,i)+'_mult'+ifpstr(n,'           ['+itrstr(" T",n)+' ].'," : clear implicits."))
    for i in range(m):
        print ('Arguments paco'+lev(m)+idx(m,i)+'_fold'+ifpstr(n,'           ['+itrstr(" T",n)+' ].'," : clear implicits."))
    for i in range(m):
        print ('Arguments paco'+lev(m)+idx(m,i)+'_unfold'+ifpstr(n,'         ['+itrstr(" T",n)+' ].'," : clear implicits."))
    print ('')
