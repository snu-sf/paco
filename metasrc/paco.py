from __future__ import print_function
import sys
from pacolib import *

if len(sys.argv) < 3:
    sys.stderr.write('\nUsage: '+sys.argv[0]+' relsize mutsize\n\n')
    sys.exit(1)

relsize = int(sys.argv[1])
mutsize = int(sys.argv[2])

print ('Require Export paconotation pacotacuser.')
print ('Require Import paconotation_internal pacotac pacon.')
print ('Set Implicit Arguments.')
print ('')

n = relsize

print ('Section PACO'+str(n)+'.')
print ('')

for i in range(n):
    print ('Variable T'+str(i)+' : '+ifpstr(i,'forall'),end='')
    for j in range(i):
        print (' (x'+str(j)+': @T'+str(j)+itrstr(" x",j)+')',end='')
    print (ifpstr(i,', ')+'Type.')
print ('')

print ('Record sig'+str(n)+'T :=')
print ('  exist'+str(n)+'T { ')
for i in range(n):
    print ('      proj'+str(n)+'T'+str(i)+': @T'+str(i)+itrstr(' proj'+str(n)+'T', i)+';')
print ('    }.')
print ('')

print ('Definition uncurry'+str(n)+' (R: rel'+str(n)+itrstr(' T',n)+'): rel1 sig'+str(n)+'T := fun x => R'+itrstr(' (proj'+str(n)+'T', n, ' x)')+'.')
print ('')

print ('Definition curry'+str(n)+' (R: rel1 sig'+str(n)+'T): rel'+str(n)+itrstr(' T', n)+' :=')
print ('  '+ifpstr(n, 'fun'+itrstr(' x', n)+' => ')+'R (exist'+str(n)+'T'+ifpstr(n, ' x'+str(n-1))+').')
print ('')

print ('Lemma uncurry_map'+str(n)+' r0 r1 (LE : r0 <'+str(n)+'== r1) : uncurry'+str(n)+' r0 <1== uncurry'+str(n)+' r1.')
print ('Proof. intros [] H. apply LE. apply H. Qed.')
print ('')

print ('Lemma uncurry_map_rev'+str(n)+' r0 r1 (LE: uncurry'+str(n)+' r0 <1== uncurry'+str(n)+' r1) : r0 <'+str(n)+'== r1.')
print ('Proof.')
print ('  repeat_intros '+str(n)+'. intros H. apply (LE (exist'+str(n)+'T'+ifpstr(n, ' x'+str(n-1))+') H).')
print ('Qed.')
print ('')

print ('Lemma curry_map'+str(n)+' r0 r1 (LE: r0 <1== r1) : curry'+str(n)+' r0 <'+str(n)+'== curry'+str(n)+' r1.')
print ('Proof. ')
print ('  repeat_intros '+str(n)+'. intros H. apply (LE (exist'+str(n)+'T'+ifpstr(n, ' x'+str(n-1))+') H).')
print ('Qed.')
print ('')

print ('Lemma curry_map_rev'+str(n)+' r0 r1 (LE: curry'+str(n)+' r0 <'+str(n)+'== curry'+str(n)+' r1) : r0 <1== r1.')
print ('Proof. ')
print ('  intros [] H. apply LE. apply H.')
print ('Qed.')
print ('')

print ('Lemma uncurry_bij1_'+str(n)+' r : curry'+str(n)+' (uncurry'+str(n)+' r) <'+str(n)+'== r.')
print ('Proof. unfold le'+str(n)+'. repeat_intros '+str(n)+'. intros H. apply H. Qed.')
print ('')

print ('Lemma uncurry_bij2_'+str(n)+' r : r <'+str(n)+'== curry'+str(n)+' (uncurry'+str(n)+' r).')
print ('Proof. unfold le'+str(n)+'. repeat_intros '+str(n)+'. intros H. apply H. Qed.')
print ('')

print ('Lemma curry_bij1_'+str(n)+' r : uncurry'+str(n)+' (curry'+str(n)+' r) <1== r.')
print ('Proof. intros []. intro H. apply H. Qed.')
print ('')

print ('Lemma curry_bij2_'+str(n)+' r : r <1== uncurry'+str(n)+' (curry'+str(n)+' r).')
print ('Proof. intros []. intro H. apply H. Qed.')
print ('')

print ('Lemma uncurry_adjoint1_'+str(n)+' r0 r1 (LE: uncurry'+str(n)+' r0 <1== r1) : r0 <'+str(n)+'== curry'+str(n)+' r1.')
print ('Proof.')
print ('  apply uncurry_map_rev'+str(n)+'. eapply le1_trans; [apply LE|]. apply curry_bij2_'+str(n)+'.')
print ('Qed.')
print ('')

print ('Lemma uncurry_adjoint2_'+str(n)+' r0 r1 (LE: r0 <'+str(n)+'== curry'+str(n)+' r1) : uncurry'+str(n)+' r0 <1== r1.')
print ('Proof.')
print ('  apply curry_map_rev'+str(n)+'. eapply le'+str(n)+'_trans; [|apply LE]. apply uncurry_bij2_'+str(n)+'.')
print ('Qed.')
print ('')

print ('Lemma curry_adjoint1_'+str(n)+' r0 r1 (LE: curry'+str(n)+' r0 <'+str(n)+'== r1) : r0 <1== uncurry'+str(n)+' r1.')
print ('Proof.')
print ('  apply curry_map_rev'+str(n)+'. eapply le'+str(n)+'_trans; [apply LE|]. apply uncurry_bij2_'+str(n)+'.')
print ('Qed.')
print ('')

print ('Lemma curry_adjoint2_'+str(n)+' r0 r1 (LE: r0 <1== uncurry'+str(n)+' r1) : curry'+str(n)+' r0 <'+str(n)+'== r1.')
print ('Proof.')
print ('  apply uncurry_map_rev'+str(n)+'. eapply le1_trans; [|apply LE]. apply curry_bij1_'+str(n)+'.')
print ('Qed.')
print ('')

print ('(** ** Predicates of Arity '+str(n))
print ('*)')
print ('')

for m in range(1,mutsize+1):
    print ('Section Arg'+str(n)+lev(m)+'_def.')
    print ('Variable'+itridx(" gf",m)+' : '+m*('rel'+str(n)+itrstr(" T",n)+' -> ')+'rel'+str(n)+itrstr(" T",n)+'.')
    for i in range(m):
        print ('Arguments gf'+idx(m,i)+' : clear implicits.')
    print ('')

    for i in range(m):
        print ('Definition ',end='')
        print ('paco'+str(n)+lev(m)+idx(m,i)+'('+itridx(' r',m)+': rel'+str(n)+itrstr(' T',n)+')'+' : rel'+str(n)+itrstr(' T',n)+' :=')
        print ('  curry'+str(n)+' (paco'+lev(m)+idx(m,i), end='')
        for j in range(m):
            print (' (fun'+itrstr(' R', m)+' => uncurry'+str(n)+' (gf'+idx(m, j)+itrstr(' (curry'+str(n)+' R', m, ')')+'))', end='')
        print (itridx(' (uncurry'+str(n)+' r', m,')')+').')
        print ('')

    for i in range(m):
        print ('Definition ',end='')
        print ('upaco'+str(n)+lev(m)+idx(m,i)+'('+itridx(' r',m)+': rel'+str(n)+itrstr(' T',n)+')'+' := '+'paco'+str(n)+lev(m)+idx(m,i)+itridx(' r',m)+' \\'+str(n)+'/ r'+idx(m,i),end='')
        print ('.')
    print ('End Arg'+str(n)+lev(m)+'_def.')
    for i in range(m):
        print ('Arguments paco'+str(n)+lev(m)+idx(m,i)+' : clear implicits.')
        print ('Arguments upaco'+str(n)+lev(m)+idx(m,i)+' : clear implicits.')
        print ('Hint Unfold upaco'+str(n)+lev(m)+idx(m,i)+'.')
    print ('')

for m in range (1,mutsize+1):
    print ('(** '+str(m)+' Mutual Coinduction *)')
    print ('')
    print ('Section Arg'+str(n)+'_'+str(m)+'.')
    print ('')
    print ("Definition monotone"+str(n)+lev(m)+" (gf: "+m*("rel"+str(n)+itrstr(" T",n)+" -> ")+"rel"+str(n)+itrstr(" T",n)+") :=")
    print ("  forall"+itrstr(" x",n)+itridx(" r",m)+itridx(" r'",m)+" (IN: gf"+itridx(" r",m)+itrstr(" x",n)+") ",end='')
    for i in range(m):
        print ("(LE"+idx(m,i)+": r"+idx(m,i)+" <"+str(n)+"= r'"+idx(m,i)+")",end='')
    print (", gf"+itridx(" r'",m)+itrstr(" x",n)+".")
    print ('')
    print ("Definition _monotone"+str(n)+lev(m)+" (gf: "+m*("rel"+str(n)+itrstr(" T",n)+" -> ")+"rel"+str(n)+itrstr(" T",n)+") :=")
    print ("  forall"+itridx(" r",m)+itridx(" r'",m),end='')
    for i in range(m):
        print ("(LE"+idx(m,i)+": r"+idx(m,i)+" <"+str(n)+"= r'"+idx(m,i)+")",end='')
    print (", gf"+itridx(" r",m)+' <'+str(n)+'== gf'+itridx(" r'",m)+'.')
    print ('')
    print ("Lemma monotone"+str(n)+lev(m)+'_eq'+" (gf: "+m*("rel"+str(n)+itrstr(" T",n)+" -> ")+"rel"+str(n)+itrstr(" T",n)+") :")
    print ("  monotone"+str(n)+lev(m)+' gf <-> _monotone'+str(n)+lev(m)+' gf.')
    print ("Proof. unfold monotone"+str(n)+lev(m)+', _monotone'+str(n)+lev(m)+', le'+str(n)+'. split; intros; eapply H; eassumption. Qed.')
    print ('')
    print ("Lemma monotone"+str(n)+lev(m)+'_map'+" (gf: "+m*("rel"+str(n)+itrstr(" T",n)+" -> ")+"rel"+str(n)+itrstr(" T",n)+")")
    print ("      (MON: _monotone"+str(n)+lev(m)+' gf) :')
    print ("  _monotone"+lev(m)+' (fun'+itrstr(' R', m)+' => uncurry'+str(n)+' (gf'+itrstr(' (curry'+str(n)+' R', m, ')')+')).')
    print ('Proof.')
    print ('  repeat_intros '+str(3*m)+'. apply uncurry_map'+str(n)+'. apply MON; apply curry_map'+str(n)+'; assumption.')
    print ('Qed.')
    print ('')

    print ('Variable'+itridx(" gf",m)+' : '+m*('rel'+str(n)+itrstr(" T",n)+' -> ')+'rel'+str(n)+itrstr(" T",n)+'.')
    for i in range(m):
        print ('Arguments gf'+idx(m,i)+' : clear implicits.')
    print ('')
    for i in range(m):
        print ('Theorem _paco'+str(n)+lev(m)+idx(m,i)+'_mon: _monotone'+str(n)+lev(m)+' (paco'+str(n)+lev(m)+idx(m,i)+itridx(" gf",m)+').')
        print ('Proof.')
        print ('  repeat_intros '+str(m*3)+'. eapply curry_map'+str(n)+', _paco'+lev(m)+idx(m,i)+'_mon; apply uncurry_map'+str(n)+'; assumption.')
        print ('Qed.')
        print ('')
    for i in range(m):
        print ('Theorem _paco'+str(n)+lev(m)+idx(m,i)+'_acc: forall')
        print ('  l'+itridx(' r',m)+' (OBG: forall rr (INC: r'+idx(m,i)+' <'+str(n)+'== rr) (CIH: l <'+str(n)+'== rr), l <'+str(n)+'== paco'+str(n)+lev(m)+idx(m,i)+itridx(" gf",m),end='')
        for j in range(m):
            if j == i:
                print (' rr',end='')
            else:
                print (' r'+idx(m,j),end='')
        print ('),')
        print ('  l <'+str(n)+'== paco'+str(n)+lev(m)+idx(m,i)+itridx(" gf",m)+itridx(' r',m)+'.')
        print ('Proof.')
        print ('  intros. apply uncurry_adjoint1_'+str(n)+'.')
        print ('  eapply _paco'+lev(m)+idx(m,i)+'_acc. intros.')
        print ('  apply uncurry_adjoint1_'+str(n)+' in INC. apply uncurry_adjoint1_'+str(n)+' in CIH.')
        print ('  apply uncurry_adjoint2_'+str(n)+'.')
        print ('  eapply le'+str(n)+'_trans. eapply (OBG _ INC CIH).')
        print ('  apply curry_map'+str(n)+'.')
        print ('  apply _paco'+lev(m)+idx(m,i)+'_mon; try apply le1_refl; apply curry_bij1_'+str(n)+'.')
        print ('Qed.')
        print ('')
    for i in range(m):
        print ('Theorem _paco'+str(n)+lev(m)+idx(m,i)+'_mult_strong: forall'+itridx(' r',m)+',')
        print ('  paco'+str(n)+lev(m)+idx(m,i)+itridx(" gf",m),end='')
        for j in range(m):
            print (' (upaco'+str(n)+lev(m)+idx(m,j)+itridx(" gf",m)+itridx(' r',m)+')',end='')
        print (' <'+str(n)+'== paco'+str(n)+lev(m)+idx(m,i)+itridx(" gf",m)+itridx(' r',m)+'.')
        print ('Proof.')
        print ('  intros. apply curry_map'+str(n)+'.')
        print ('  eapply le1_trans; [| eapply _paco'+lev(m)+idx(m,i)+'_mult_strong].')
        print ('  apply _paco'+lev(m)+idx(m,i)+'_mon; intros []; intros H; apply H.')
        print ('Qed.')
        print ('')
    for i in range(m):
        print ('Theorem _paco'+str(n)+lev(m)+idx(m,i)+'_fold: forall'+itridx(' r',m)+',')
        print ('  gf'+idx(m,i),end='')
        for j in range(m):
            print (' (upaco'+str(n)+lev(m)+idx(m,j)+itridx(" gf",m)+itridx(' r',m)+')',end='')
        print (' <'+str(n)+'== paco'+str(n)+lev(m)+idx(m,i)+itridx(" gf",m)+itridx(' r',m)+'.')
        print ('Proof.')
        print ('  intros. apply uncurry_adjoint1_'+str(n)+'.')
        print ('  eapply le1_trans; [| apply _paco'+lev(m)+idx(m,i)+'_fold]. apply le1_refl.')
        print ('Qed.')
        print ('')
    for i in range(m):
        print ('Theorem _paco'+str(n)+lev(m)+idx(m,i)+'_unfold: forall'+itridx(' (MON: _monotone'+str(n)+lev(m)+' gf',m,')')+itridx(' r',m)+',')
        print ('  paco'+str(n)+lev(m)+idx(m,i)+itridx(" gf",m)+itridx(' r',m)+' <'+str(n)+'== gf'+idx(m,i),end='')
        for j in range(m):
            print (' (upaco'+str(n)+lev(m)+idx(m,j)+itridx(" gf",m)+itridx(' r',m)+')',end='')
        print ('.')
        print ('Proof.')
        print ('  intros. apply curry_adjoint2_'+str(n)+'.')
        print ('  eapply _paco'+lev(m)+idx(m,i)+'_unfold; apply monotone'+str(n)+lev(m)+'_map; assumption.')
        print ('Qed.')
        print ('')

    for i in range(m):
        print ('Theorem paco'+str(n)+lev(m)+idx(m,i)+'_acc: forall')
        print ('  l'+itridx(' r',m)+' (OBG: forall rr (INC: r'+idx(m,i)+' <'+str(n)+'= rr) (CIH: l <'+str(n)+'= rr), l <'+str(n)+'= paco'+str(n)+lev(m)+idx(m,i)+itridx(" gf",m),end='')
        for j in range(m):
            if j == i:
                print (' rr',end='')
            else:
                print (' r'+idx(m,j),end='')
        print ('),')
        print ('  l <'+str(n)+'= paco'+str(n)+lev(m)+idx(m,i)+itridx(" gf",m)+itridx(' r',m)+'.')
        print ('Proof.')
        print ('  apply _paco'+str(n)+lev(m)+idx(m,i)+'_acc.')
        print ('Qed.')
        print ('')
    for i in range(m):
        print ('Theorem paco'+str(n)+lev(m)+idx(m,i)+'_mon: monotone'+str(n)+lev(m)+' (paco'+str(n)+lev(m)+idx(m,i)+itridx(" gf",m)+').')
        print ('Proof.')
        print ('  apply monotone'+str(n)+lev(m)+'_eq.')
        print ('  apply _paco'+str(n)+lev(m)+idx(m,i)+'_mon.')
        print ('Qed.')
        print ('')
    for i in range(m):
        print ('Theorem upaco'+str(n)+lev(m)+idx(m,i)+'_mon: monotone'+str(n)+lev(m)+' (upaco'+str(n)+lev(m)+idx(m,i)+itridx(" gf",m)+').')
        print ('Proof.')
        print ('  repeat_intros '+str(n+2*m)+'. intros R '+itrstr(" LE",m)+'.')
        print ('  destruct R.')
        print ('  - left. eapply paco'+str(n)+lev(m)+idx(m,i)+'_mon. apply H.'+itrstr(" apply LE",m,'.'))
        print ('  - right. apply LE'+str(i)+', H.')
        print ('Qed.')
    for i in range(m):
        print ('Theorem paco'+str(n)+lev(m)+idx(m,i)+'_mult_strong: forall'+itridx(' r',m)+',')
        print ('  paco'+str(n)+lev(m)+idx(m,i)+itridx(" gf",m),end='')
        for j in range(m):
            print (' (upaco'+str(n)+lev(m)+idx(m,j)+itridx(" gf",m)+itridx(' r',m)+')',end='')
        print (' <'+str(n)+'= paco'+str(n)+lev(m)+idx(m,i)+itridx(" gf",m)+itridx(' r',m)+'.')
        print ('Proof.')
        print ('  apply _paco'+str(n)+lev(m)+idx(m,i)+'_mult_strong.')
        print ('Qed.')
        print ('')
    for i in range(m):
        print ('Corollary paco'+str(n)+lev(m)+idx(m,i)+'_mult: forall'+itridx(' r',m)+',')
        print ('  paco'+str(n)+lev(m)+idx(m,i)+itridx(" gf",m)+itridx(' (paco'+str(n)+lev(m),m,itridx(" gf",m)+itridx(' r',m)+')')+' <'+str(n)+'= paco'+str(n)+lev(m)+idx(m,i)+itridx(" gf",m)+itridx(' r',m)+'.')
        print ('Proof. intros; eapply paco'+str(n)+lev(m)+idx(m,i)+'_mult_strong, paco'+str(n)+lev(m)+idx(m,i)+'_mon; [apply PR|..]; intros; left; assumption. Qed.')
        print ('')
    for i in range(m):
        print ('Theorem paco'+str(n)+lev(m)+idx(m,i)+'_fold: forall'+itridx(' r',m)+',')
        print ('  gf'+idx(m,i),end='')
        for j in range(m):
            print (' (upaco'+str(n)+lev(m)+idx(m,j)+itridx(" gf",m)+itridx(' r',m)+')',end='')
        print (' <'+str(n)+'= paco'+str(n)+lev(m)+idx(m,i)+itridx(" gf",m)+itridx(' r',m)+'.')
        print ('Proof.')
        print ('  apply _paco'+str(n)+lev(m)+idx(m,i)+'_fold.')
        print ('Qed.')
        print ('')
    for i in range(m):
        print ('Theorem paco'+str(n)+lev(m)+idx(m,i)+'_unfold: forall'+itridx(' (MON: monotone'+str(n)+lev(m)+' gf',m,')')+itridx(' r',m)+',')
        print ('  paco'+str(n)+lev(m)+idx(m,i)+itridx(" gf",m)+itridx(' r',m)+' <'+str(n)+'= gf'+idx(m,i),end='')
        for j in range(m):
            print (' (upaco'+str(n)+lev(m)+idx(m,j)+itridx(" gf",m)+itridx(' r',m)+')',end='')
        print ('.')
        print ('Proof.')
        print ('  repeat_intros '+str(m)+'. eapply _paco'+str(n)+lev(m)+idx(m,i)+'_unfold; apply monotone'+str(n)+lev(m)+'_eq; assumption.')
        print ('Qed.')
        print ('')

    print ('End Arg'+str(n)+'_'+str(m)+'.')
    print ('')

    for i in range(m):
        print ('Arguments paco'+str(n)+lev(m)+idx(m,i)+'_acc'+" : clear implicits.")
    for i in range(m):
        print ('Arguments paco'+str(n)+lev(m)+idx(m,i)+'_mon'+" : clear implicits.")
    for i in range(m):
        print ('Arguments upaco'+str(n)+lev(m)+idx(m,i)+'_mon'+" : clear implicits.")
    for i in range(m):
        print ('Arguments paco'+str(n)+lev(m)+idx(m,i)+'_mult_strong'+" : clear implicits.")
    for i in range(m):
        print ('Arguments paco'+str(n)+lev(m)+idx(m,i)+'_mult'+" : clear implicits.")
    for i in range(m):
        print ('Arguments paco'+str(n)+lev(m)+idx(m,i)+'_fold'+" : clear implicits.")
    for i in range(m):
        print ('Arguments paco'+str(n)+lev(m)+idx(m,i)+'_unfold'+" : clear implicits.")
    print ('')

    for i in range(m):
        print ("Global Instance paco"+str(n)+lev(m)+idx(m,i)+"_inst "+" ("+itridx("gf",m," ")+": rel"+str(n)+itrstr(" T",n)+"->_)"+itridx(" r",m)+itrstr(" x",n)+" : paco_class (paco"+str(n)+lev(m)+idx(m,i)+itridx(" gf",m)+itridx(" r",m)+itrstr(" x",n)+") :=")
        print ("{ pacoacc    := paco"+str(n)+lev(m)+idx(m,i)+"_acc"+itridx(" gf",m)+";")
        print ("  pacomult   := paco"+str(n)+lev(m)+idx(m,i)+"_mult"+itridx(" gf",m)+";")
        print ("  pacofold   := paco"+str(n)+lev(m)+idx(m,i)+"_fold"+itridx(" gf",m)+";")
        print ("  pacounfold := paco"+str(n)+lev(m)+idx(m,i)+"_unfold"+itridx(" gf",m)+" }.")
        print ('')

print ('Lemma upaco'+str(n)+'_clear gf'+itrstr(' x', n)+':')
print ('  upaco'+str(n)+' gf bot'+str(n)+itrstr(' x', n)+' <-> paco'+str(n)+' gf bot'+str(n)+itrstr(' x', n)+'.')
print ('Proof. split; intros; [destruct H;[apply H|destruct H]|left; apply H]. Qed.')
print ('')

print ('End PACO'+str(n)+'.')
print ('')

for m in range(1,mutsize+1):
    for i in range(m):
        print ('Global Opaque paco'+str(n)+lev(m)+idx(m,i)+'.')
    print ('')

    for i in range(m):
        print ('Hint Unfold upaco'+str(n)+lev(m)+idx(m,i)+'.')
    for i in range(m):
        print ('Hint Resolve paco'+str(n)+lev(m)+idx(m,i)+'_fold.')
    print ('Hint Unfold monotone'+str(n)+lev(m)+'.')
    print ('')
