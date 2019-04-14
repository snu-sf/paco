Require Export Program.Basics. Open Scope program_scope.
Require Import paco5 pacotac cpn5.
Set Implicit Arguments.

Section CompatiblePaco5.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.

Local Notation rel := (rel5 T0 T1 T2 T3 T4).

Section CompatiblePaco5_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone5 gf.

Variable clo : rel -> rel.
Hypothesis clo_compat: compatible5 gf clo.

Inductive cpaco5 r rg x0 x1 x2 x3 x4 : Prop :=
| cpaco5_intro (IN: rclo5 clo (paco5 (compose gf (rclo5 clo)) (r \5/ rg) \5/ r) x0 x1 x2 x3 x4)
.

Definition cupaco5 r := cpaco5 r r.

Lemma cpaco5_def_mon : monotone5 (compose gf (rclo5 clo)).
Proof.
  eapply monotone5_compose. apply gf_mon. apply rclo5_mon.
Qed.

Hint Resolve cpaco5_def_mon : paco.

Lemma cpaco5_mon r r' rg rg' x0 x1 x2 x3 x4
      (IN: @cpaco5 r rg x0 x1 x2 x3 x4)
      (LEr: r <5= r')
      (LErg: rg <5= rg'):
  @cpaco5 r' rg' x0 x1 x2 x3 x4.
Proof.
  destruct IN. econstructor.
  eapply rclo5_mon. apply IN.
  intros. destruct PR; [|right; apply LEr, H].
  left. eapply paco5_mon. apply H.
  intros. destruct PR.
  - left. apply LEr, H0.
  - right. apply LErg, H0.
Qed.

Lemma cpaco5_cofix r rg 
      l (OBG: forall rr (INC: rg <5= rr) (CIH: l <5= rr), l <5= cpaco5 r rr):
  l <5= cpaco5 r rg.
Proof.
  assert (IN: l <5= cpaco5 r (rg \5/ l)).
  { intros. apply OBG; [left; apply PR0 | right; apply PR0 | apply PR]. }
  clear OBG. intros. apply IN in PR.
  destruct PR. econstructor.
  eapply rclo5_mon. apply IN0.
  clear x0 x1 x2 x3 x4 IN0.
  intros. destruct PR; [|right; apply H].
  left. revert x0 x1 x2 x3 x4 H.
  pcofix CIH. intros.
  _punfold H0; [..|apply cpaco5_def_mon]. pstep.
  eapply gf_mon. apply H0. intros.
  apply rclo5_rclo. eapply rclo5_mon. apply PR.
  intros. destruct PR0.
  - apply rclo5_base. right. apply CIH. apply H.
  - destruct H; [|destruct H].
    + apply rclo5_base. right. apply CIH0. left. apply H.
    + apply rclo5_base. right. apply CIH0. right. apply H.
    + apply IN in H. destruct H.
      eapply rclo5_mon. apply IN0.
      intros. destruct PR0.
      * right. apply CIH. apply H.      
      * right. apply CIH0. left. apply H.
Qed.

Lemma cpaco5_cupaco r rg:
  cupaco5 (cpaco5 r rg) <5= cpaco5 r rg.
Proof.
  eapply cpaco5_cofix.
  intros. destruct PR. econstructor.
  apply rclo5_rclo. eapply rclo5_mon. apply IN.
  intros. destruct PR.
  - apply rclo5_base. left.
    eapply paco5_mon. apply H.
    intros. right; apply CIH.
    econstructor. apply rclo5_base. right.
    destruct PR as [PR|PR]; apply PR.
  - destruct H. eapply rclo5_mon. apply IN0.
    intros. destruct PR; [| right; apply H].
    left. eapply paco5_mon. apply H.
    intros. destruct PR. left; apply H0.
    right. apply INC, H0.
Qed.

Lemma cpaco5_uclo (uclo: rel -> rel) r rg 
      (LEclo: uclo <6= cupaco5) :
  uclo (cpaco5 r rg) <5= cpaco5 r rg.
Proof.
  intros. apply cpaco5_cupaco. apply LEclo, PR.
Qed.

Lemma cpaco5_base r rg: r <5= cpaco5 r rg.
Proof.
  econstructor. apply rclo5_base. right. apply PR.
Qed.

Lemma cpaco5_rclo r:
  rclo5 clo r <5= cupaco5 r.
Proof.
  intros. econstructor.
  eapply rclo5_mon. apply PR.
  intros. right. apply PR0.
Qed.

Lemma cpaco5_clo r:
  clo r <5= cupaco5 r.
Proof.
  intros. apply cpaco5_rclo. apply rclo5_clo.
  eapply clo_compat. apply PR.
  intros. apply rclo5_base. apply PR0.
Qed.

Lemma cpaco5_step r rg:
  gf (cpaco5 rg rg) <5= cpaco5 r rg.
Proof.
  intros. econstructor. apply rclo5_base. left.
  pstep. eapply gf_mon. apply PR.
  intros. destruct PR0. eapply rclo5_mon. apply IN.
  intros. destruct PR0.
  - left. eapply paco5_mon. apply H. right. destruct PR0; apply H0.
  - right. right. apply H.
Qed.

Lemma cpaco5_init:
  cpaco5 bot5 bot5 <5= paco5 gf bot5.
Proof.
  intros. destruct PR. revert x0 x1 x2 x3 x4 IN.
  pcofix CIH. intros.
  pstep. eapply gf_mon; [| right; apply CIH, rclo5_rclo, PR]. 
  apply compat5_compat with (gf:=gf). apply rclo5_compat. apply gf_mon. apply clo_compat.
  eapply rclo5_mon. apply IN.
  intros. pclearbot. _punfold PR; [..|apply cpaco5_def_mon].
  eapply cpaco5_def_mon. apply PR.
  intros. pclearbot. left. apply PR0.
Qed.

Lemma cpaco5_final r rg:
  (r \5/ paco5 gf rg) <5= cpaco5 r rg.
Proof.
  intros. destruct PR. apply cpaco5_base, H.
  econstructor. apply rclo5_base.
  left. eapply paco5_mon_gen. apply H.
  - intros. eapply gf_mon. apply PR.
    intros. apply rclo5_base. apply PR0.
  - intros. right. apply PR.
Qed.

Lemma cpaco5_unfold:
  cpaco5 bot5 bot5 <5= gf (cpaco5 bot5 bot5).
Proof.
  intros. apply cpaco5_init in PR. _punfold PR; [..|apply gf_mon].
  eapply gf_mon. apply PR.
  intros. pclearbot. apply cpaco5_final. right. apply PR0.
Qed.

End CompatiblePaco5_main.

Lemma cpaco5_mon_gen (gf gf' clo clo': rel -> rel) x0 x1 x2 x3 x4 r r' rg rg'
      (IN: @cpaco5 gf clo r rg x0 x1 x2 x3 x4)
      (MON: monotone5 gf)
      (LEgf: gf <6= gf')
      (LEclo: clo <6= clo')
      (LEr: r <5= r')
      (LErg: rg <5= rg') :
  @cpaco5 gf' clo' r' rg' x0 x1 x2 x3 x4.
Proof.
  eapply cpaco5_mon; [|apply LEr|apply LErg].
  destruct IN. econstructor.
  eapply rclo5_mon_gen. apply IN. apply LEclo.
  intros. destruct PR; [| right; apply H].
  left. eapply paco5_mon_gen. apply H.
  - intros. eapply LEgf.
    eapply MON. apply PR.
    intros. eapply rclo5_mon_gen. apply PR0. apply LEclo. intros; apply PR1.
  - intros. apply PR.
Qed.

Lemma cpaco5_mon_bot (gf gf' clo clo': rel -> rel) x0 x1 x2 x3 x4 r' rg'
      (IN: @cpaco5 gf clo bot5 bot5 x0 x1 x2 x3 x4)
      (MON: monotone5 gf)
      (LEgf: gf <6= gf')
      (LEclo: clo <6= clo'):
  @cpaco5 gf' clo' r' rg' x0 x1 x2 x3 x4.
Proof.
  eapply cpaco5_mon_gen. apply IN. apply MON. apply LEgf. apply LEclo. contradiction. contradiction.
Qed.

End CompatiblePaco5.

Hint Resolve cpaco5_base : paco.
Hint Resolve cpaco5_step : paco.
Hint Resolve cpaco5_final : paco.
Hint Resolve rclo5_base : paco.
