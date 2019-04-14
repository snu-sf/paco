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
| cpaco1_intro (IN: rclo1 clo (paco1 (compose gf (rclo1 clo)) (r \1/ rg) \1/ r) x0)
.

Definition cupaco1 r := cpaco1 r r.

Lemma cpaco1_def_mon : monotone1 (compose gf (rclo1 clo)).
Proof.
  eapply monotone1_compose. apply gf_mon. apply rclo1_mon.
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
  intros. destruct PR; [|right; apply LEr, H].
  left. eapply paco1_mon. apply H.
  intros. destruct PR.
  - left. apply LEr, H0.
  - right. apply LErg, H0.
Qed.

Lemma cpaco1_cofix r rg 
      l (OBG: forall rr (INC: rg <1= rr) (CIH: l <1= rr), l <1= cpaco1 r rr):
  l <1= cpaco1 r rg.
Proof.
  assert (IN: l <1= cpaco1 r (rg \1/ l)).
  { intros. apply OBG; [left; apply PR0 | right; apply PR0 | apply PR]. }
  clear OBG. intros. apply IN in PR.
  destruct PR. econstructor.
  eapply rclo1_mon. apply IN0.
  clear x0 IN0.
  intros. destruct PR; [|right; apply H].
  left. revert x0 H.
  pcofix CIH. intros.
  _punfold H0; [..|apply cpaco1_def_mon]. pstep.
  eapply gf_mon. apply H0. intros.
  apply rclo1_rclo. eapply rclo1_mon. apply PR.
  intros. destruct PR0.
  - apply rclo1_base. right. apply CIH. apply H.
  - destruct H; [|destruct H].
    + apply rclo1_base. right. apply CIH0. left. apply H.
    + apply rclo1_base. right. apply CIH0. right. apply H.
    + apply IN in H. destruct H.
      eapply rclo1_mon. apply IN0.
      intros. destruct PR0.
      * right. apply CIH. apply H.      
      * right. apply CIH0. left. apply H.
Qed.

Lemma cpaco1_cupaco r rg:
  cupaco1 (cpaco1 r rg) <1= cpaco1 r rg.
Proof.
  eapply cpaco1_cofix.
  intros. destruct PR. econstructor.
  apply rclo1_rclo. eapply rclo1_mon. apply IN.
  intros. destruct PR.
  - apply rclo1_base. left.
    eapply paco1_mon. apply H.
    intros. right; apply CIH.
    econstructor. apply rclo1_base. right.
    destruct PR as [PR|PR]; apply PR.
  - destruct H. eapply rclo1_mon. apply IN0.
    intros. destruct PR; [| right; apply H].
    left. eapply paco1_mon. apply H.
    intros. destruct PR. left; apply H0.
    right. apply INC, H0.
Qed.

Lemma cpaco1_uclo (uclo: rel -> rel) r rg 
      (LEclo: uclo <2= cupaco1) :
  uclo (cpaco1 r rg) <1= cpaco1 r rg.
Proof.
  intros. apply cpaco1_cupaco. apply LEclo, PR.
Qed.

Lemma cpaco1_base r rg: r <1= cpaco1 r rg.
Proof.
  econstructor. apply rclo1_base. right. apply PR.
Qed.

Lemma cpaco1_rclo r:
  rclo1 clo r <1= cupaco1 r.
Proof.
  intros. econstructor.
  eapply rclo1_mon. apply PR.
  intros. right. apply PR0.
Qed.

Lemma cpaco1_clo r:
  clo r <1= cupaco1 r.
Proof.
  intros. apply cpaco1_rclo. apply rclo1_clo.
  eapply clo_compat. apply PR.
  intros. apply rclo1_base. apply PR0.
Qed.

Lemma cpaco1_step r rg:
  gf (cpaco1 rg rg) <1= cpaco1 r rg.
Proof.
  intros. econstructor. apply rclo1_base. left.
  pstep. eapply gf_mon. apply PR.
  intros. destruct PR0. eapply rclo1_mon. apply IN.
  intros. destruct PR0.
  - left. eapply paco1_mon. apply H. right. destruct PR0; apply H0.
  - right. right. apply H.
Qed.

Lemma cpaco1_init:
  cpaco1 bot1 bot1 <1= paco1 gf bot1.
Proof.
  intros. destruct PR. revert x0 IN.
  pcofix CIH. intros.
  pstep. eapply gf_mon; [| right; apply CIH, rclo1_rclo, PR]. 
  apply compat1_compat with (gf:=gf). apply rclo1_compat. apply gf_mon. apply clo_compat.
  eapply rclo1_mon. apply IN.
  intros. pclearbot. _punfold PR; [..|apply cpaco1_def_mon].
  eapply cpaco1_def_mon. apply PR.
  intros. pclearbot. left. apply PR0.
Qed.

Lemma cpaco1_final r rg:
  (r \1/ paco1 gf rg) <1= cpaco1 r rg.
Proof.
  intros. destruct PR. apply cpaco1_base, H.
  econstructor. apply rclo1_base.
  left. eapply paco1_mon_gen. apply H.
  - intros. eapply gf_mon. apply PR.
    intros. apply rclo1_base. apply PR0.
  - intros. right. apply PR.
Qed.

Lemma cpaco1_unfold:
  cpaco1 bot1 bot1 <1= gf (cpaco1 bot1 bot1).
Proof.
  intros. apply cpaco1_init in PR. _punfold PR; [..|apply gf_mon].
  eapply gf_mon. apply PR.
  intros. pclearbot. apply cpaco1_final. right. apply PR0.
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
  eapply rclo1_mon_gen. apply IN. apply LEclo.
  intros. destruct PR; [| right; apply H].
  left. eapply paco1_mon_gen. apply H.
  - intros. eapply LEgf.
    eapply MON. apply PR.
    intros. eapply rclo1_mon_gen. apply PR0. apply LEclo. intros; apply PR1.
  - intros. apply PR.
Qed.

Lemma cpaco1_mon_bot (gf gf' clo clo': rel -> rel) x0 r' rg'
      (IN: @cpaco1 gf clo bot1 bot1 x0)
      (MON: monotone1 gf)
      (LEgf: gf <2= gf')
      (LEclo: clo <2= clo'):
  @cpaco1 gf' clo' r' rg' x0.
Proof.
  eapply cpaco1_mon_gen. apply IN. apply MON. apply LEgf. apply LEclo. contradiction. contradiction.
Qed.

End CompatiblePaco1.

Hint Resolve cpaco1_base : paco.
Hint Resolve cpaco1_step : paco.
Hint Resolve cpaco1_final : paco.
Hint Resolve rclo1_base : paco.
