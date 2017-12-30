from __future__ import print_function
import sys
from pacolib import *

if len(sys.argv) < 3: 
    sys.stderr.write('\nUsage: '+sys.argv[0]+' relsize mutsize\n\n') 
    sys.exit(1) 

relsize = int(sys.argv[1])
mutsize = int(sys.argv[2])

print ('Require Export paconotation pacotac pacotacuser.')
print ('Set Implicit Arguments.')
print ('')

n = relsize

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
        print ('Implicit Arguments gf'+idx(m,i)+' [].')
    print ('')
    print ('CoInductive ',end='')
    for i in range(m):
        print (ifpstr(i,"with ")+'paco'+str(n)+lev(m)+idx(m,i)+'('+itridx(' r',m)+': rel'+str(n)+itrstr(' T',n)+')'+itrstr(" x",n)+' : Prop :=')
        print ('| paco'+str(n)+lev(m)+idx(m,i)+'_pfold'+itridx(' pco',m))
        for j in range(m):
            print ('    (LE : pco'+idx(m,j)+' <'+str(n)+'= (paco'+str(n)+lev(m)+idx(m,j)+itridx(' r',m)+' \\'+str(n)+'/ r'+idx(m,j)+'))')
        print ('    (SIM: gf'+idx(m,i)+itridx(' pco',m)+itrstr(" x",n)+')')
    print ('.')
    for i in range(m):
        print ('Definition ',end='')
        print ('upaco'+str(n)+lev(m)+idx(m,i)+'('+itridx(' r',m)+': rel'+str(n)+itrstr(' T',n)+')'+' := '+'paco'+str(n)+lev(m)+idx(m,i)+itridx(' r',m)+' \\'+str(n)+'/ r'+idx(m,i),end='')
        print ('.')
    print ('End Arg'+str(n)+lev(m)+'_def.')
    for i in range(m):
        print ('Implicit Arguments paco'+str(n)+lev(m)+idx(m,i)+' ['+itrstr(" T",n)+' ].')
        print ('Implicit Arguments upaco'+str(n)+lev(m)+idx(m,i)+' ['+itrstr(" T",n)+' ].')
        print ('Hint Unfold upaco'+str(n)+lev(m)+idx(m,i)+'.')
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
    print ("Definition monotone"+str(n)+lev(m)+itrstr(" T",n)+" (gf: "+m*("rel"+str(n)+itrstr(" T",n)+" -> ")+"rel"+str(n)+itrstr(" T",n)+") :=")
    print ("  forall"+itrstr(" x",n)+itridx(" r",m)+itridx(" r'",m)+" (IN: gf"+itridx(" r",m)+itrstr(" x",n)+") ",end='')
    for i in range(m):
        print ("(LE"+idx(m,i)+": r"+idx(m,i)+" <"+str(n)+"= r'"+idx(m,i)+")",end='')
    print (", gf"+itridx(" r'",m)+itrstr(" x",n)+".")
    print ('')
    for i in range(n):
        print ('Variable T'+str(i)+' : '+ifpstr(i,'forall'),end='')
        for j in range(i):
            print (' (x'+str(j)+': @T'+str(j)+itrstr(" x",j)+')',end='')
        print (ifpstr(i,', ')+'Type.')
    print ('Variable'+itridx(" gf",m)+' : '+m*('rel'+str(n)+itrstr(" T",n)+' -> ')+'rel'+str(n)+itrstr(" T",n)+'.')
    for i in range(m):
        print ('Implicit Arguments gf'+idx(m,i)+' [].')
    print ('')
    for i in range(m):
        print ('Theorem paco'+str(n)+lev(m)+idx(m,i)+'_acc: forall')
        print ('  l'+itridx(' r',m)+' (OBG: forall rr (INC: r'+idx(m,i)+' <'+str(n)+'= rr) (CIH: l <_paco_'+str(n)+'= rr), l <_paco_'+str(n)+'= paco'+str(n)+lev(m)+idx(m,i)+itridx(" gf",m),end='')
        for j in range(m):
            if j == i:
                print (' rr',end='')
            else:
                print (' r'+idx(m,j),end='')
        print ('),')
        print ('  l <'+str(n)+'= paco'+str(n)+lev(m)+idx(m,i)+itridx(" gf",m)+itridx(' r',m)+'.')
        print ('Proof.')
        print ('  intros; assert (SIM: paco'+str(n)+lev(m)+idx(m,i)+itridx(" gf",m),end='')
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
        print ('Theorem paco'+str(n)+lev(m)+idx(m,i)+'_mon: monotone'+str(n)+lev(m)+' (paco'+str(n)+lev(m)+idx(m,i)+itridx(" gf",m)+').')
        print ('Proof. paco_cofix_auto; repeat (left; do '+str(n+1)+' paco_revert; paco_cofix_auto). Qed.')
        print ('')
    for i in range(m):
        print ('Theorem paco'+str(n)+lev(m)+idx(m,i)+'_mult_strong: forall'+itridx(' r',m)+',')
        print ('  paco'+str(n)+lev(m)+idx(m,i)+itridx(" gf",m),end='')
        for j in range(m):
            print (' (upaco'+str(n)+lev(m)+idx(m,j)+itridx(" gf",m)+itridx(' r',m)+')',end='')
        print (' <'+str(n)+'= paco'+str(n)+lev(m)+idx(m,i)+itridx(" gf",m)+itridx(' r',m)+'.')
        print ('Proof. paco_cofix_auto; repeat (left; do '+str(n+1)+' paco_revert; paco_cofix_auto). Qed.')
        print ('')
    for i in range(m):
        print ('Corollary paco'+str(n)+lev(m)+idx(m,i)+'_mult: forall'+itridx(' r',m)+',')
        print ('  paco'+str(n)+lev(m)+idx(m,i)+itridx(" gf",m)+itridx(' (paco'+str(n)+lev(m),m,itridx(" gf",m)+itridx(' r',m)+')')+' <'+str(n)+'= paco'+str(n)+lev(m)+idx(m,i)+itridx(" gf",m)+itridx(' r',m)+'.')
        print ('Proof. intros; eapply paco'+str(n)+lev(m)+idx(m,i)+'_mult_strong, paco'+str(n)+lev(m)+idx(m,i)+'_mon; eauto. Qed.')
        print ('')
    for i in range(m):
        print ('Theorem paco'+str(n)+lev(m)+idx(m,i)+'_fold: forall'+itridx(' r',m)+',')
        print ('  gf'+idx(m,i),end='')
        for j in range(m):
            print (' (upaco'+str(n)+lev(m)+idx(m,j)+itridx(" gf",m)+itridx(' r',m)+')',end='')
        print (' <'+str(n)+'= paco'+str(n)+lev(m)+idx(m,i)+itridx(" gf",m)+itridx(' r',m)+'.')
        print ('Proof. intros; econstructor; ['+m*' |'+'eauto]; eauto. Qed.')
        print ('')
    for i in range(m):
        print ('Theorem paco'+str(n)+lev(m)+idx(m,i)+'_unfold: forall'+itridx(' (MON: monotone'+str(n)+lev(m)+' gf',m,')')+itridx(' r',m)+',')
        print ('  paco'+str(n)+lev(m)+idx(m,i)+itridx(" gf",m)+itridx(' r',m)+' <'+str(n)+'= gf'+idx(m,i),end='')
        for j in range(m):
            print (' (upaco'+str(n)+lev(m)+idx(m,j)+itridx(" gf",m)+itridx(' r',m)+')',end='')
        print ('.')
        print ('Proof. unfold monotone'+str(n)+lev(m)+'; intros; destruct PR; eauto. Qed.')
        print ('')
    print ('End Arg'+str(n)+'_'+str(m)+'.')
    print ('')
    print ('Hint Unfold monotone'+str(n)+lev(m)+'.')
    for i in range(m):
        print ('Hint Resolve paco'+str(n)+lev(m)+idx(m,i)+'_fold.')
    print ('')
    for i in range(m):
        print ('Implicit Arguments paco'+str(n)+lev(m)+idx(m,i)+'_acc            ['+itrstr(" T",n)+' ].')
    for i in range(m):
        print ('Implicit Arguments paco'+str(n)+lev(m)+idx(m,i)+'_mon            ['+itrstr(" T",n)+' ].')
    for i in range(m):
        print ('Implicit Arguments paco'+str(n)+lev(m)+idx(m,i)+'_mult_strong    ['+itrstr(" T",n)+' ].')
    for i in range(m):
        print ('Implicit Arguments paco'+str(n)+lev(m)+idx(m,i)+'_mult           ['+itrstr(" T",n)+' ].')
    for i in range(m):
        print ('Implicit Arguments paco'+str(n)+lev(m)+idx(m,i)+'_fold           ['+itrstr(" T",n)+' ].')
    for i in range(m):
        print ('Implicit Arguments paco'+str(n)+lev(m)+idx(m,i)+'_unfold         ['+itrstr(" T",n)+' ].')
    print ('')

    for i in range(m):
        print ("Instance paco"+str(n)+lev(m)+idx(m,i)+"_inst "+itrstr(" T",n)+" ("+itridx("gf",m," ")+": rel"+str(n)+itrstr(" T",n)+"->_)"+itridx(" r",m)+itrstr(" x",n)+" : paco_class (paco"+str(n)+lev(m)+idx(m,i)+itridx(" gf",m)+itridx(" r",m)+itrstr(" x",n)+") :=")
        print ("{ pacoacc    := paco"+str(n)+lev(m)+idx(m,i)+"_acc"+itridx(" gf",m)+";")
        print ("  pacomult   := paco"+str(n)+lev(m)+idx(m,i)+"_mult"+itridx(" gf",m)+";")
        print ("  pacofold   := paco"+str(n)+lev(m)+idx(m,i)+"_fold"+itridx(" gf",m)+";")
        print ("  pacounfold := paco"+str(n)+lev(m)+idx(m,i)+"_unfold"+itridx(" gf",m)+" }.")
        print ('')
