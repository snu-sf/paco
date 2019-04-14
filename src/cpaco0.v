Require Export Program.Basics. Open Scope program_scope.
Require Import paco0 pacotac cpn0.
Set Implicit Arguments.

Section CompatiblePaco0.


Local Notation rel := (rel0).

Section CompatiblePaco0_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone0 gf.

Variable clo : rel -> rel.
Hypothesis clo_compat: compatible0 gf clo.

Inductive cpaco0 r rg : Prop :=
| cpaco0_intro (IN: rclo0 clo (r \0/ paco0 (compose gf (rclo0 clo)) rg))
.

Definition cupaco0 r := cpaco0 r r.

Lemma cpaco0_def_mon : monotone0 (compose gf (rclo0 clo)).
Proof.
  eapply monotone0_compose. apply gf_mon. apply rclo0_mon.
Qed.

Hint Resolve cpaco0_def_mon : paco.

Lemma cpaco0_mon r r' rg rg'
      (IN: @cpaco0 r rg)
      (LEr: r <0= r')
      (LErg: rg <0= rg'):
  @cpaco0 r' rg'.
Proof.
  destruct IN. econstructor.
  eapply rclo0_mon. apply IN.
  intros. destruct PR. left. apply LEr, H.
  right. eapply paco0_mon. apply H. apply LErg.
Qed.

Lemma cpaco0_base r rg: r <0= cpaco0 r rg.
Proof.
  econstructor. apply rclo0_base. left. apply PR.
Qed.

Lemma cpaco0_rclo r rg:
  rclo0 clo (cpaco0 r rg) <0= cpaco0 r rg.
Proof.
  intros. econstructor. apply rclo0_rclo.
  eapply rclo0_mon. apply PR.
  intros. apply PR0.
Qed.

Lemma cpaco0_clo r rg:
  clo (cpaco0 r rg) <0= cpaco0 r rg.
Proof.
  intros. apply cpaco0_rclo. apply rclo0_clo.
  eapply clo_compat. apply PR.
  intros. apply rclo0_base. apply PR0.
Qed.

Lemma cpaco0_step r rg:
  gf (cpaco0 rg rg) <0= cpaco0 r rg.
Proof.
  intros. econstructor. apply rclo0_base. right.
  pstep. eapply gf_mon. apply PR.
  intros. destruct PR0.
  eapply rclo0_mon. apply IN.
  intros. destruct PR0; [right|left]; apply H.
Qed.

Lemma cpaco0_init:
  cpaco0 bot0 bot0 <0= paco0 gf bot0.
Proof.
  intros. destruct PR. revert IN.
  pcofix CIH. intros.
  pstep. eapply gf_mon; [| right; apply CIH, rclo0_rclo, PR]. 
  apply compat0_compat with (gf:=gf). apply rclo0_compat. apply gf_mon. apply clo_compat.
  eapply rclo0_mon. apply IN.
  intros. destruct PR. contradiction.
  _punfold H; [..|apply cpaco0_def_mon]. eapply cpaco0_def_mon. apply H.
  intros. pclearbot. right. apply PR.
Qed.

Lemma cpaco0_final:
  paco0 gf bot0 <0= cpaco0 bot0 bot0.
Proof.
  intros. econstructor. apply rclo0_base.
  right. eapply paco0_mon_bot. apply PR.
  intros. eapply gf_mon. apply PR0.
  intros. apply rclo0_base. apply PR1.
Qed.

Lemma cpaco0_unfold:
  cpaco0 bot0 bot0 <0= gf (cpaco0 bot0 bot0).
Proof.
  intros. apply cpaco0_init in PR. _punfold PR; [..|apply gf_mon].
  eapply gf_mon. apply PR.
  intros. pclearbot. apply cpaco0_final, PR0.
Qed.

Lemma cpaco0_cofix
      r rg (LE: r <0= rg)
      l (OBG: forall rr (INC: rg <0= rr) (CIH: l <0= rr), l <0= cpaco0 r rr):
  l <0= cpaco0 r rg.
Proof.
  assert (IN: l <0= cpaco0 r (rg \0/ l)).
  { intros. apply OBG; [left; apply PR0 | right; apply PR0 | apply PR]. }
  clear OBG. intros. apply IN in PR.
  destruct PR. econstructor.
  eapply rclo0_mon. apply IN0.
  clear IN0.
  intros. destruct PR. left. apply H.
  right. revert H.
  pcofix CIH. intros.
  _punfold H0; [..|apply cpaco0_def_mon]. pstep.
  eapply gf_mon. apply H0. intros.
  apply rclo0_rclo. eapply rclo0_mon. apply PR.
  intros. destruct PR0.
  - apply rclo0_base. right. apply CIH. apply H.
  - destruct H.
    + apply rclo0_base. right. apply CIH0, H.
    + apply IN in H. destruct H.
      eapply rclo0_mon. apply IN0.
      intros. destruct PR0.
      * right. apply CIH0. apply LE, H.
      * right. apply CIH. apply H.
Qed.

Lemma cpaco0_cupaco
      r rg (LEr: r <0= rg):
  cupaco0 (cpaco0 r rg) <0= cpaco0 r rg.
Proof.
  eapply cpaco0_cofix. apply LEr.
  intros. destruct PR. econstructor.
  apply rclo0_rclo. eapply rclo0_mon. apply IN.
  intros. destruct PR.
  - destruct H.  eapply rclo0_mon. apply IN0.
    intros. destruct PR. left. apply H.
    right. eapply paco0_mon. apply H. apply INC.
  - apply rclo0_base. right.
    eapply paco0_mon. apply H.
    intros. apply CIH.
    econstructor. apply rclo0_base. left. apply PR.
Qed.

Lemma cpaco0_uclo (uclo: rel -> rel)
      r rg (LEr: r <0= rg)
      (LEclo: uclo <1= cupaco0) :
  uclo (cpaco0 r rg) <0= cpaco0 r rg.
Proof.
  intros. apply cpaco0_cupaco. apply LEr. apply LEclo, PR.
Qed.

End CompatiblePaco0_main.

Lemma cpaco0_mon_gen (gf gf' clo clo': rel -> rel) r r' rg rg'
      (IN: @cpaco0 gf clo r rg)
      (MON: monotone0 gf)
      (LEgf: gf <1= gf')
      (LEclo: clo <1= clo')
      (LEr: r <0= r')
      (LErg: rg <0= rg') :
  @cpaco0 gf' clo' r' rg'.
Proof.
  eapply cpaco0_mon; [|apply LEr|apply LErg].
  destruct IN. econstructor.
  eapply rclo0_mon_gen. apply IN. apply LEclo.
  intros. destruct PR. left; apply H.
  right. eapply paco0_mon_gen. apply H.
  - intros. eapply LEgf.
    eapply MON. apply PR.
    intros. eapply rclo0_mon_gen. apply PR0. apply LEclo. intros; apply PR1.
  - intros. apply PR.
Qed.

End CompatiblePaco0.

Hint Resolve cpaco0_base : paco.
Hint Resolve cpaco0_step : paco.
Hint Resolve rclo0_base : paco.
Hint Resolve rclo0_clo : paco.
