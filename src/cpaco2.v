Require Export Program.Basics. Open Scope program_scope.
Require Import paco2 pacotac cpn2.
Set Implicit Arguments.

Section CompatiblePaco2.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.

Local Notation rel := (rel2 T0 T1).

Section CompatiblePaco2_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone2 gf.

Variable clo : rel -> rel.
Hypothesis clo_compat: compatible2 gf clo.

Inductive cpaco2 r rg x0 x1 : Prop :=
| cpaco2_intro (IN: rclo2 clo (r \2/ paco2 (compose gf (rclo2 clo)) rg) x0 x1)
.

Definition cupaco2 r := cpaco2 r r.

Lemma cpaco2_def_mon : monotone2 (compose gf (rclo2 clo)).
Proof.
  eapply compose_monotone2. apply gf_mon. apply rclo2_mon.
Qed.

Hint Resolve cpaco2_def_mon : paco.

Lemma cpaco2_mon r r' rg rg' x0 x1
      (IN: @cpaco2 r rg x0 x1)
      (LEr: r <2= r')
      (LErg: rg <2= rg'):
  @cpaco2 r' rg' x0 x1.
Proof.
  destruct IN. econstructor.
  eapply rclo2_mon. apply IN.
  intros. destruct PR. left. apply LEr, H.
  right. eapply paco2_mon. apply H. apply LErg.
Qed.

Lemma cpaco2_base r rg: r <2= cpaco2 r rg.
Proof.
  econstructor. apply rclo2_base. left. apply PR.
Qed.

Lemma cpaco2_rclo r rg:
  rclo2 clo (cpaco2 r rg) <2= cpaco2 r rg.
Proof.
  intros. econstructor. apply rclo2_rclo.
  eapply rclo2_mon. apply PR.
  intros. apply PR0.
Qed.

Lemma cpaco2_clo r rg:
  clo (cpaco2 r rg) <2= cpaco2 r rg.
Proof.
  intros. apply cpaco2_rclo. apply rclo2_clo.
  eapply clo_compat. apply PR.
  intros. apply rclo2_base. apply PR0.
Qed.

Lemma cpaco2_step r rg:
  gf (cpaco2 rg rg) <2= cpaco2 r rg.
Proof.
  intros. econstructor. apply rclo2_base. right.
  pstep. eapply gf_mon. apply PR.
  intros. destruct PR0.
  eapply rclo2_mon. apply IN.
  intros. destruct PR0; [right|left]; apply H.
Qed.

Lemma cpaco2_init:
  cpaco2 bot2 bot2 <2= paco2 gf bot2.
Proof.
  intros. destruct PR. revert x0 x1 IN.
  pcofix CIH. intros.
  pstep. eapply gf_mon; [| right; apply CIH, rclo2_rclo, PR]. 
  apply compat2_compat. apply rclo2_compat. apply gf_mon. apply clo_compat.
  eapply rclo2_mon. apply IN.
  intros. destruct PR. contradiction.
  punfold H. eapply cpaco2_def_mon. apply H.
  intros. pclearbot. right. apply PR.
Qed.

Lemma cpaco2_final:
  paco2 gf bot2 <2= cpaco2 bot2 bot2.
Proof.
  intros. econstructor. apply rclo2_base.
  right. eapply paco2_mon_bot. apply PR.
  intros. eapply gf_mon. apply PR0.
  intros. apply rclo2_base. apply PR1.
Qed.

Lemma cpaco2_unfold:
  cpaco2 bot2 bot2 <2= gf (cpaco2 bot2 bot2).
Proof.
  intros. apply cpaco2_init in PR. punfold PR.
  eapply gf_mon. apply PR.
  intros. pclearbot. apply cpaco2_final, PR0.
Qed.

Lemma cpaco2_cofix
      r rg (LE: r <2= rg)
      l (OBG: forall rr (INC: rg <2= rr) (CIH: l <2= rr), l <2= cpaco2 r rr):
  l <2= cpaco2 r rg.
Proof.
  assert (IN: l <2= cpaco2 r (rg \2/ l)).
  { intros. apply OBG; [left; apply PR0 | right; apply PR0 | apply PR]. }
  clear OBG. intros. apply IN in PR.
  destruct PR. econstructor.
  eapply rclo2_mon. apply IN0.
  clear x0 x1 IN0.
  intros. destruct PR. left. apply H.
  right. revert x0 x1 H.
  pcofix CIH. intros.
  punfold H0. pstep.
  eapply gf_mon. apply H0. intros.
  apply rclo2_rclo. eapply rclo2_mon. apply PR.
  intros. destruct PR0.
  - apply rclo2_base. right. apply CIH. apply H.
  - destruct H.
    + apply rclo2_base. right. apply CIH0, H.
    + apply IN in H. destruct H.
      eapply rclo2_mon. apply IN0.
      intros. destruct PR0.
      * right. apply CIH0. apply LE, H.
      * right. apply CIH. apply H.
Qed.

Lemma cpaco2_cupaco
      r rg (LE: r <2= rg):
  cupaco2 (cpaco2 r rg) <2= cpaco2 r rg.
Proof.
  eapply cpaco2_cofix. apply LE.
  intros. destruct PR. econstructor.
  apply rclo2_rclo. eapply rclo2_mon. apply IN.
  intros. destruct PR.
  - destruct H.  eapply rclo2_mon. apply IN0.
    intros. destruct PR. left. apply H.
    right. eapply paco2_mon. apply H. apply INC.
  - apply rclo2_base. right.
    eapply paco2_mon. apply H.
    intros. apply CIH.
    econstructor. apply rclo2_base. left. apply PR.
Qed.

End CompatiblePaco2_main.

Lemma cpaco2_mon_gen (gf gf' clo clo': rel -> rel) x0 x1 r r' rg rg'
      (IN: @cpaco2 gf clo r rg x0 x1)
      (MON: monotone2 gf)
      (LEgf: gf <3= gf')
      (LEclo: clo <3= clo')
      (LEr: r <2= r')
      (LErg: rg <2= rg') :
  @cpaco2 gf' clo' r' rg' x0 x1.
Proof.
  eapply cpaco2_mon; [|apply LEr|apply LErg].
  destruct IN. econstructor.
  eapply rclo2_mon_gen, IN. apply LEclo.
  intros. destruct PR. left; apply H.
  right. eapply paco2_mon_gen. apply H.
  - intros. eapply LEgf.
    eapply MON. apply PR.
    eapply rclo2_mon_gen. apply LEclo. intros; apply PR0.
  - intros. apply PR.
Qed.

End CompatiblePaco2.

Hint Resolve cpaco2_base : paco.
Hint Resolve cpaco2_step : paco.
Hint Resolve rclo2_base : paco.
Hint Resolve rclo2_clo : paco.
