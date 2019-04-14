Require Export Program.Basics. Open Scope program_scope.
Require Import paco1 pacotac cpn1.
Set Implicit Arguments.

Section CompatiblePaco1.

Variable T0 : Type.

Local Notation rel := (rel1 T0).

Section CompatiblePaco1_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone1 gf.

Variable clo : rel -> rel.
Hypothesis clo_compat: compatible1 gf clo.

Inductive cpaco1 r rg x0 : Prop :=
| cpaco1_intro (IN: rclo1 clo (r \1/ paco1 (compose gf (rclo1 clo)) rg) x0)
.

Definition cupaco1 r := cpaco1 r r.

Lemma cpaco1_def_mon : monotone1 (compose gf (rclo1 clo)).
Proof.
  eapply compose_monotone1. apply gf_mon. apply rclo1_mon.
Qed.

Hint Resolve cpaco1_def_mon : paco.

Lemma cpaco1_mon r r' rg rg' x0
      (IN: @cpaco1 r rg x0)
      (LEr: r <1= r')
      (LErg: rg <1= rg'):
  @cpaco1 r' rg' x0.
Proof.
  destruct IN. econstructor.
  eapply rclo1_mon. apply IN.
  intros. destruct PR. left. apply LEr, H.
  right. eapply paco1_mon. apply H. apply LErg.
Qed.

Lemma cpaco1_base r rg: r <1= cpaco1 r rg.
Proof.
  econstructor. apply rclo1_base. left. apply PR.
Qed.

Lemma cpaco1_rclo r rg:
  rclo1 clo (cpaco1 r rg) <1= cpaco1 r rg.
Proof.
  intros. econstructor. apply rclo1_rclo.
  eapply rclo1_mon. apply PR.
  intros. apply PR0.
Qed.

Lemma cpaco1_clo r rg:
  clo (cpaco1 r rg) <1= cpaco1 r rg.
Proof.
  intros. apply cpaco1_rclo. apply rclo1_clo.
  eapply clo_compat. apply PR.
  intros. apply rclo1_base. apply PR0.
Qed.

Lemma cpaco1_step r rg:
  gf (cpaco1 rg rg) <1= cpaco1 r rg.
Proof.
  intros. econstructor. apply rclo1_base. right.
  pstep. eapply gf_mon. apply PR.
  intros. destruct PR0.
  eapply rclo1_mon. apply IN.
  intros. destruct PR0; [right|left]; apply H.
Qed.

Lemma cpaco1_init:
  cpaco1 bot1 bot1 <1= paco1 gf bot1.
Proof.
  intros. destruct PR. revert x0 IN.
  pcofix CIH. intros.
  pstep. eapply gf_mon; [| right; apply CIH, rclo1_rclo, PR]. 
  apply compat1_compat. apply rclo1_compat. apply gf_mon. apply clo_compat.
  eapply rclo1_mon. apply IN.
  intros. destruct PR. contradiction.
  punfold H. eapply cpaco1_def_mon. apply H.
  intros. pclearbot. right. apply PR.
Qed.

Lemma cpaco1_final:
  paco1 gf bot1 <1= cpaco1 bot1 bot1.
Proof.
  intros. econstructor. apply rclo1_base.
  right. eapply paco1_mon_bot. apply PR.
  intros. eapply gf_mon. apply PR0.
  intros. apply rclo1_base. apply PR1.
Qed.

Lemma cpaco1_unfold:
  cpaco1 bot1 bot1 <1= gf (cpaco1 bot1 bot1).
Proof.
  intros. apply cpaco1_init in PR. punfold PR.
  eapply gf_mon. apply PR.
  intros. pclearbot. apply cpaco1_final, PR0.
Qed.

Lemma cpaco1_cofix
      r rg (LE: r <1= rg)
      l (OBG: forall rr (INC: rg <1= rr) (CIH: l <1= rr), l <1= cpaco1 r rr):
  l <1= cpaco1 r rg.
Proof.
  assert (IN: l <1= cpaco1 r (rg \1/ l)).
  { intros. apply OBG; [left; apply PR0 | right; apply PR0 | apply PR]. }
  clear OBG. intros. apply IN in PR.
  destruct PR. econstructor.
  eapply rclo1_mon. apply IN0.
  clear x0 IN0.
  intros. destruct PR. left. apply H.
  right. revert x0 H.
  pcofix CIH. intros.
  punfold H0. pstep.
  eapply gf_mon. apply H0. intros.
  apply rclo1_rclo. eapply rclo1_mon. apply PR.
  intros. destruct PR0.
  - apply rclo1_base. right. apply CIH. apply H.
  - destruct H.
    + apply rclo1_base. right. apply CIH0, H.
    + apply IN in H. destruct H.
      eapply rclo1_mon. apply IN0.
      intros. destruct PR0.
      * right. apply CIH0. apply LE, H.
      * right. apply CIH. apply H.
Qed.

Lemma cpaco1_cupaco
      r rg (LE: r <1= rg):
  cupaco1 (cpaco1 r rg) <1= cpaco1 r rg.
Proof.
  eapply cpaco1_cofix. apply LE.
  intros. destruct PR. econstructor.
  apply rclo1_rclo. eapply rclo1_mon. apply IN.
  intros. destruct PR.
  - destruct H.  eapply rclo1_mon. apply IN0.
    intros. destruct PR. left. apply H.
    right. eapply paco1_mon. apply H. apply INC.
  - apply rclo1_base. right.
    eapply paco1_mon. apply H.
    intros. apply CIH.
    econstructor. apply rclo1_base. left. apply PR.
Qed.

End CompatiblePaco1_main.

Lemma cpaco1_mon_gen (gf gf' clo clo': rel -> rel) x0 r r' rg rg'
      (IN: @cpaco1 gf clo r rg x0)
      (MON: monotone1 gf)
      (LEgf: gf <2= gf')
      (LEclo: clo <2= clo')
      (LEr: r <1= r')
      (LErg: rg <1= rg') :
  @cpaco1 gf' clo' r' rg' x0.
Proof.
  eapply cpaco1_mon; [|apply LEr|apply LErg].
  destruct IN. econstructor.
  eapply rclo1_mon_gen, IN. apply LEclo.
  intros. destruct PR. left; apply H.
  right. eapply paco1_mon_gen. apply H.
  - intros. eapply LEgf.
    eapply MON. apply PR.
    eapply rclo1_mon_gen. apply LEclo. intros; apply PR0.
  - intros. apply PR.
Qed.

End CompatiblePaco1.

Hint Resolve cpaco1_base : paco.
Hint Resolve cpaco1_step : paco.
Hint Resolve rclo1_base : paco.
Hint Resolve rclo1_clo : paco.
