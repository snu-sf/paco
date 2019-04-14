Require Export Program.Basics. Open Scope program_scope.
Require Import paco4 pacotac cpn4.
Set Implicit Arguments.

Section CompatiblePaco4.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.

Local Notation rel := (rel4 T0 T1 T2 T3).

Section CompatiblePaco4_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone4 gf.

Variable clo : rel -> rel.
Hypothesis clo_compat: compatible4 gf clo.

Inductive cpaco4 r rg x0 x1 x2 x3 : Prop :=
| cpaco4_intro (IN: rclo4 clo (paco4 (compose gf (rclo4 clo)) (r \4/ rg) \4/ r) x0 x1 x2 x3)
.

Definition cupaco4 r := cpaco4 r r.

Lemma cpaco4_def_mon : monotone4 (compose gf (rclo4 clo)).
Proof.
  eapply monotone4_compose. apply gf_mon. apply rclo4_mon.
Qed.

Hint Resolve cpaco4_def_mon : paco.

Lemma cpaco4_mon r r' rg rg' x0 x1 x2 x3
      (IN: @cpaco4 r rg x0 x1 x2 x3)
      (LEr: r <4= r')
      (LErg: rg <4= rg'):
  @cpaco4 r' rg' x0 x1 x2 x3.
Proof.
  destruct IN. econstructor.
  eapply rclo4_mon. apply IN.
  intros. destruct PR; [|right; apply LEr, H].
  left. eapply paco4_mon. apply H.
  intros. destruct PR.
  - left. apply LEr, H0.
  - right. apply LErg, H0.
Qed.

Lemma cpaco4_cofix r rg 
      l (OBG: forall rr (INC: rg <4= rr) (CIH: l <4= rr), l <4= cpaco4 r rr):
  l <4= cpaco4 r rg.
Proof.
  assert (IN: l <4= cpaco4 r (rg \4/ l)).
  { intros. apply OBG; [left; apply PR0 | right; apply PR0 | apply PR]. }
  clear OBG. intros. apply IN in PR.
  destruct PR. econstructor.
  eapply rclo4_mon. apply IN0.
  clear x0 x1 x2 x3 IN0.
  intros. destruct PR; [|right; apply H].
  left. revert x0 x1 x2 x3 H.
  pcofix CIH. intros.
  _punfold H0; [..|apply cpaco4_def_mon]. pstep.
  eapply gf_mon. apply H0. intros.
  apply rclo4_rclo. eapply rclo4_mon. apply PR.
  intros. destruct PR0.
  - apply rclo4_base. right. apply CIH. apply H.
  - destruct H; [|destruct H].
    + apply rclo4_base. right. apply CIH0. left. apply H.
    + apply rclo4_base. right. apply CIH0. right. apply H.
    + apply IN in H. destruct H.
      eapply rclo4_mon. apply IN0.
      intros. destruct PR0.
      * right. apply CIH. apply H.      
      * right. apply CIH0. left. apply H.
Qed.

Lemma cpaco4_cupaco r rg:
  cupaco4 (cpaco4 r rg) <4= cpaco4 r rg.
Proof.
  eapply cpaco4_cofix.
  intros. destruct PR. econstructor.
  apply rclo4_rclo. eapply rclo4_mon. apply IN.
  intros. destruct PR.
  - apply rclo4_base. left.
    eapply paco4_mon. apply H.
    intros. right; apply CIH.
    econstructor. apply rclo4_base. right.
    destruct PR as [PR|PR]; apply PR.
  - destruct H. eapply rclo4_mon. apply IN0.
    intros. destruct PR; [| right; apply H].
    left. eapply paco4_mon. apply H.
    intros. destruct PR. left; apply H0.
    right. apply INC, H0.
Qed.

Lemma cpaco4_uclo (uclo: rel -> rel) r rg 
      (LEclo: uclo <5= cupaco4) :
  uclo (cpaco4 r rg) <4= cpaco4 r rg.
Proof.
  intros. apply cpaco4_cupaco. apply LEclo, PR.
Qed.

Lemma cpaco4_base r rg: r <4= cpaco4 r rg.
Proof.
  econstructor. apply rclo4_base. right. apply PR.
Qed.

Lemma cpaco4_rclo r:
  rclo4 clo r <4= cupaco4 r.
Proof.
  intros. econstructor.
  eapply rclo4_mon. apply PR.
  intros. right. apply PR0.
Qed.

Lemma cpaco4_clo r:
  clo r <4= cupaco4 r.
Proof.
  intros. apply cpaco4_rclo. apply rclo4_clo.
  eapply clo_compat. apply PR.
  intros. apply rclo4_base. apply PR0.
Qed.

Lemma cpaco4_step r rg:
  gf (cpaco4 rg rg) <4= cpaco4 r rg.
Proof.
  intros. econstructor. apply rclo4_base. left.
  pstep. eapply gf_mon. apply PR.
  intros. destruct PR0. eapply rclo4_mon. apply IN.
  intros. destruct PR0.
  - left. eapply paco4_mon. apply H. right. destruct PR0; apply H0.
  - right. right. apply H.
Qed.

Lemma cpaco4_init:
  cpaco4 bot4 bot4 <4= paco4 gf bot4.
Proof.
  intros. destruct PR. revert x0 x1 x2 x3 IN.
  pcofix CIH. intros.
  pstep. eapply gf_mon; [| right; apply CIH, rclo4_rclo, PR]. 
  apply compat4_compat with (gf:=gf). apply rclo4_compat. apply gf_mon. apply clo_compat.
  eapply rclo4_mon. apply IN.
  intros. pclearbot. _punfold PR; [..|apply cpaco4_def_mon].
  eapply cpaco4_def_mon. apply PR.
  intros. pclearbot. left. apply PR0.
Qed.

Lemma cpaco4_final r rg:
  (r \4/ paco4 gf rg) <4= cpaco4 r rg.
Proof.
  intros. destruct PR. apply cpaco4_base, H.
  econstructor. apply rclo4_base.
  left. eapply paco4_mon_gen. apply H.
  - intros. eapply gf_mon. apply PR.
    intros. apply rclo4_base. apply PR0.
  - intros. right. apply PR.
Qed.

Lemma cpaco4_unfold:
  cpaco4 bot4 bot4 <4= gf (cpaco4 bot4 bot4).
Proof.
  intros. apply cpaco4_init in PR. _punfold PR; [..|apply gf_mon].
  eapply gf_mon. apply PR.
  intros. pclearbot. apply cpaco4_final. right. apply PR0.
Qed.

End CompatiblePaco4_main.

Lemma cpaco4_mon_gen (gf gf' clo clo': rel -> rel) x0 x1 x2 x3 r r' rg rg'
      (IN: @cpaco4 gf clo r rg x0 x1 x2 x3)
      (MON: monotone4 gf)
      (LEgf: gf <5= gf')
      (LEclo: clo <5= clo')
      (LEr: r <4= r')
      (LErg: rg <4= rg') :
  @cpaco4 gf' clo' r' rg' x0 x1 x2 x3.
Proof.
  eapply cpaco4_mon; [|apply LEr|apply LErg].
  destruct IN. econstructor.
  eapply rclo4_mon_gen. apply IN. apply LEclo.
  intros. destruct PR; [| right; apply H].
  left. eapply paco4_mon_gen. apply H.
  - intros. eapply LEgf.
    eapply MON. apply PR.
    intros. eapply rclo4_mon_gen. apply PR0. apply LEclo. intros; apply PR1.
  - intros. apply PR.
Qed.

Lemma cpaco4_mon_bot (gf gf' clo clo': rel -> rel) x0 x1 x2 x3 r' rg'
      (IN: @cpaco4 gf clo bot4 bot4 x0 x1 x2 x3)
      (MON: monotone4 gf)
      (LEgf: gf <5= gf')
      (LEclo: clo <5= clo'):
  @cpaco4 gf' clo' r' rg' x0 x1 x2 x3.
Proof.
  eapply cpaco4_mon_gen. apply IN. apply MON. apply LEgf. apply LEclo. contradiction. contradiction.
Qed.

End CompatiblePaco4.

Hint Resolve cpaco4_base : paco.
Hint Resolve cpaco4_step : paco.
Hint Resolve cpaco4_final : paco.
Hint Resolve rclo4_base : paco.
