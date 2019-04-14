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
| cpaco2_intro (IN: rclo2 clo (paco2 (compose gf (rclo2 clo)) (r \2/ rg) \2/ r) x0 x1)
.

Definition cupaco2 r := cpaco2 r r.

Lemma cpaco2_def_mon : monotone2 (compose gf (rclo2 clo)).
Proof.
  eapply monotone2_compose. apply gf_mon. apply rclo2_mon.
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
  intros. destruct PR; [|right; apply LEr, H].
  left. eapply paco2_mon. apply H.
  intros. destruct PR.
  - left. apply LEr, H0.
  - right. apply LErg, H0.
Qed.

Lemma cpaco2_cofix r rg 
      l (OBG: forall rr (INC: rg <2= rr) (CIH: l <2= rr), l <2= cpaco2 r rr):
  l <2= cpaco2 r rg.
Proof.
  assert (IN: l <2= cpaco2 r (rg \2/ l)).
  { intros. apply OBG; [left; apply PR0 | right; apply PR0 | apply PR]. }
  clear OBG. intros. apply IN in PR.
  destruct PR. econstructor.
  eapply rclo2_mon. apply IN0.
  clear x0 x1 IN0.
  intros. destruct PR; [|right; apply H].
  left. revert x0 x1 H.
  pcofix CIH. intros.
  _punfold H0; [..|apply cpaco2_def_mon]. pstep.
  eapply gf_mon. apply H0. intros.
  apply rclo2_rclo. eapply rclo2_mon. apply PR.
  intros. destruct PR0.
  - apply rclo2_base. right. apply CIH. apply H.
  - destruct H; [|destruct H].
    + apply rclo2_base. right. apply CIH0. left. apply H.
    + apply rclo2_base. right. apply CIH0. right. apply H.
    + apply IN in H. destruct H.
      eapply rclo2_mon. apply IN0.
      intros. destruct PR0.
      * right. apply CIH. apply H.      
      * right. apply CIH0. left. apply H.
Qed.

Lemma cpaco2_cupaco r rg:
  cupaco2 (cpaco2 r rg) <2= cpaco2 r rg.
Proof.
  eapply cpaco2_cofix.
  intros. destruct PR. econstructor.
  apply rclo2_rclo. eapply rclo2_mon. apply IN.
  intros. destruct PR.
  - apply rclo2_base. left.
    eapply paco2_mon. apply H.
    intros. right; apply CIH.
    econstructor. apply rclo2_base. right.
    destruct PR as [PR|PR]; apply PR.
  - destruct H. eapply rclo2_mon. apply IN0.
    intros. destruct PR; [| right; apply H].
    left. eapply paco2_mon. apply H.
    intros. destruct PR. left; apply H0.
    right. apply INC, H0.
Qed.

Lemma cpaco2_uclo (uclo: rel -> rel) r rg 
      (LEclo: uclo <3= cupaco2) :
  uclo (cpaco2 r rg) <2= cpaco2 r rg.
Proof.
  intros. apply cpaco2_cupaco. apply LEclo, PR.
Qed.

Lemma cpaco2_base r rg: r <2= cpaco2 r rg.
Proof.
  econstructor. apply rclo2_base. right. apply PR.
Qed.

Lemma cpaco2_rclo r:
  rclo2 clo r <2= cupaco2 r.
Proof.
  intros. econstructor.
  eapply rclo2_mon. apply PR.
  intros. right. apply PR0.
Qed.

Lemma cpaco2_clo r:
  clo r <2= cupaco2 r.
Proof.
  intros. apply cpaco2_rclo. apply rclo2_clo.
  eapply clo_compat. apply PR.
  intros. apply rclo2_base. apply PR0.
Qed.

Lemma cpaco2_step r rg:
  gf (cpaco2 rg rg) <2= cpaco2 r rg.
Proof.
  intros. econstructor. apply rclo2_base. left.
  pstep. eapply gf_mon. apply PR.
  intros. destruct PR0. eapply rclo2_mon. apply IN.
  intros. destruct PR0.
  - left. eapply paco2_mon. apply H. right. destruct PR0; apply H0.
  - right. right. apply H.
Qed.

Lemma cpaco2_init:
  cpaco2 bot2 bot2 <2= paco2 gf bot2.
Proof.
  intros. destruct PR. revert x0 x1 IN.
  pcofix CIH. intros.
  pstep. eapply gf_mon; [| right; apply CIH, rclo2_rclo, PR]. 
  apply compat2_compat with (gf:=gf). apply rclo2_compat. apply gf_mon. apply clo_compat.
  eapply rclo2_mon. apply IN.
  intros. pclearbot. _punfold PR; [..|apply cpaco2_def_mon].
  eapply cpaco2_def_mon. apply PR.
  intros. pclearbot. left. apply PR0.
Qed.

Lemma cpaco2_final r rg:
  (r \2/ paco2 gf rg) <2= cpaco2 r rg.
Proof.
  intros. destruct PR. apply cpaco2_base, H.
  econstructor. apply rclo2_base.
  left. eapply paco2_mon_gen. apply H.
  - intros. eapply gf_mon. apply PR.
    intros. apply rclo2_base. apply PR0.
  - intros. right. apply PR.
Qed.

Lemma cpaco2_unfold:
  cpaco2 bot2 bot2 <2= gf (cpaco2 bot2 bot2).
Proof.
  intros. apply cpaco2_init in PR. _punfold PR; [..|apply gf_mon].
  eapply gf_mon. apply PR.
  intros. pclearbot. apply cpaco2_final. right. apply PR0.
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
  eapply rclo2_mon_gen. apply IN. apply LEclo.
  intros. destruct PR; [| right; apply H].
  left. eapply paco2_mon_gen. apply H.
  - intros. eapply LEgf.
    eapply MON. apply PR.
    intros. eapply rclo2_mon_gen. apply PR0. apply LEclo. intros; apply PR1.
  - intros. apply PR.
Qed.

Lemma cpaco2_mon_bot (gf gf' clo clo': rel -> rel) x0 x1 r' rg'
      (IN: @cpaco2 gf clo bot2 bot2 x0 x1)
      (MON: monotone2 gf)
      (LEgf: gf <3= gf')
      (LEclo: clo <3= clo'):
  @cpaco2 gf' clo' r' rg' x0 x1.
Proof.
  eapply cpaco2_mon_gen. apply IN. apply MON. apply LEgf. apply LEclo. contradiction. contradiction.
Qed.

End CompatiblePaco2.

Hint Resolve cpaco2_base : paco.
Hint Resolve cpaco2_step : paco.
Hint Resolve cpaco2_final : paco.
Hint Resolve rclo2_base : paco.
