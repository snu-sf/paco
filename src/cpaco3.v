Require Export Program.Basics. Open Scope program_scope.
Require Import paco3 pacotac cpn3.
Set Implicit Arguments.

Section CompatiblePaco3.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.

Local Notation rel := (rel3 T0 T1 T2).

Section CompatiblePaco3_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone3 gf.

Variable clo : rel -> rel.
Hypothesis clo_compat: compatible3 gf clo.

Inductive cpaco3 r rg x0 x1 x2 : Prop :=
| cpaco3_intro (IN: rclo3 clo (paco3 (compose gf (rclo3 clo)) (r \3/ rg) \3/ r) x0 x1 x2)
.

Definition cupaco3 r := cpaco3 r r.

Lemma cpaco3_def_mon : monotone3 (compose gf (rclo3 clo)).
Proof.
  eapply monotone3_compose. apply gf_mon. apply rclo3_mon.
Qed.

Hint Resolve cpaco3_def_mon : paco.

Lemma cpaco3_mon r r' rg rg' x0 x1 x2
      (IN: @cpaco3 r rg x0 x1 x2)
      (LEr: r <3= r')
      (LErg: rg <3= rg'):
  @cpaco3 r' rg' x0 x1 x2.
Proof.
  destruct IN. econstructor.
  eapply rclo3_mon. apply IN.
  intros. destruct PR; [|right; apply LEr, H].
  left. eapply paco3_mon. apply H.
  intros. destruct PR.
  - left. apply LEr, H0.
  - right. apply LErg, H0.
Qed.

Lemma cpaco3_cofix r rg 
      l (OBG: forall rr (INC: rg <3= rr) (CIH: l <3= rr), l <3= cpaco3 r rr):
  l <3= cpaco3 r rg.
Proof.
  assert (IN: l <3= cpaco3 r (rg \3/ l)).
  { intros. apply OBG; [left; apply PR0 | right; apply PR0 | apply PR]. }
  clear OBG. intros. apply IN in PR.
  destruct PR. econstructor.
  eapply rclo3_mon. apply IN0.
  clear x0 x1 x2 IN0.
  intros. destruct PR; [|right; apply H].
  left. revert x0 x1 x2 H.
  pcofix CIH. intros.
  _punfold H0; [..|apply cpaco3_def_mon]. pstep.
  eapply gf_mon. apply H0. intros.
  apply rclo3_rclo. eapply rclo3_mon. apply PR.
  intros. destruct PR0.
  - apply rclo3_base. right. apply CIH. apply H.
  - destruct H; [|destruct H].
    + apply rclo3_base. right. apply CIH0. left. apply H.
    + apply rclo3_base. right. apply CIH0. right. apply H.
    + apply IN in H. destruct H.
      eapply rclo3_mon. apply IN0.
      intros. destruct PR0.
      * right. apply CIH. apply H.      
      * right. apply CIH0. left. apply H.
Qed.

Lemma cpaco3_cupaco r rg:
  cupaco3 (cpaco3 r rg) <3= cpaco3 r rg.
Proof.
  eapply cpaco3_cofix.
  intros. destruct PR. econstructor.
  apply rclo3_rclo. eapply rclo3_mon. apply IN.
  intros. destruct PR.
  - apply rclo3_base. left.
    eapply paco3_mon. apply H.
    intros. right; apply CIH.
    econstructor. apply rclo3_base. right.
    destruct PR as [PR|PR]; apply PR.
  - destruct H. eapply rclo3_mon. apply IN0.
    intros. destruct PR; [| right; apply H].
    left. eapply paco3_mon. apply H.
    intros. destruct PR. left; apply H0.
    right. apply INC, H0.
Qed.

Lemma cpaco3_uclo (uclo: rel -> rel) r rg 
      (LEclo: uclo <4= cupaco3) :
  uclo (cpaco3 r rg) <3= cpaco3 r rg.
Proof.
  intros. apply cpaco3_cupaco. apply LEclo, PR.
Qed.

Lemma cpaco3_base r rg: r <3= cpaco3 r rg.
Proof.
  econstructor. apply rclo3_base. right. apply PR.
Qed.

Lemma cpaco3_rclo r:
  rclo3 clo r <3= cupaco3 r.
Proof.
  intros. econstructor.
  eapply rclo3_mon. apply PR.
  intros. right. apply PR0.
Qed.

Lemma cpaco3_clo r:
  clo r <3= cupaco3 r.
Proof.
  intros. apply cpaco3_rclo. apply rclo3_clo.
  eapply clo_compat. apply PR.
  intros. apply rclo3_base. apply PR0.
Qed.

Lemma cpaco3_step r rg:
  gf (cpaco3 rg rg) <3= cpaco3 r rg.
Proof.
  intros. econstructor. apply rclo3_base. left.
  pstep. eapply gf_mon. apply PR.
  intros. destruct PR0. eapply rclo3_mon. apply IN.
  intros. destruct PR0.
  - left. eapply paco3_mon. apply H. right. destruct PR0; apply H0.
  - right. right. apply H.
Qed.

Lemma cpaco3_init:
  cpaco3 bot3 bot3 <3= paco3 gf bot3.
Proof.
  intros. destruct PR. revert x0 x1 x2 IN.
  pcofix CIH. intros.
  pstep. eapply gf_mon; [| right; apply CIH, rclo3_rclo, PR]. 
  apply compat3_compat with (gf:=gf). apply rclo3_compat. apply gf_mon. apply clo_compat.
  eapply rclo3_mon. apply IN.
  intros. pclearbot. _punfold PR; [..|apply cpaco3_def_mon].
  eapply cpaco3_def_mon. apply PR.
  intros. pclearbot. left. apply PR0.
Qed.

Lemma cpaco3_final r rg:
  (r \3/ paco3 gf rg) <3= cpaco3 r rg.
Proof.
  intros. destruct PR. apply cpaco3_base, H.
  econstructor. apply rclo3_base.
  left. eapply paco3_mon_gen. apply H.
  - intros. eapply gf_mon. apply PR.
    intros. apply rclo3_base. apply PR0.
  - intros. right. apply PR.
Qed.

Lemma cpaco3_unfold:
  cpaco3 bot3 bot3 <3= gf (cpaco3 bot3 bot3).
Proof.
  intros. apply cpaco3_init in PR. _punfold PR; [..|apply gf_mon].
  eapply gf_mon. apply PR.
  intros. pclearbot. apply cpaco3_final. right. apply PR0.
Qed.

End CompatiblePaco3_main.

Lemma cpaco3_mon_gen (gf gf' clo clo': rel -> rel) x0 x1 x2 r r' rg rg'
      (IN: @cpaco3 gf clo r rg x0 x1 x2)
      (MON: monotone3 gf)
      (LEgf: gf <4= gf')
      (LEclo: clo <4= clo')
      (LEr: r <3= r')
      (LErg: rg <3= rg') :
  @cpaco3 gf' clo' r' rg' x0 x1 x2.
Proof.
  eapply cpaco3_mon; [|apply LEr|apply LErg].
  destruct IN. econstructor.
  eapply rclo3_mon_gen. apply IN. apply LEclo.
  intros. destruct PR; [| right; apply H].
  left. eapply paco3_mon_gen. apply H.
  - intros. eapply LEgf.
    eapply MON. apply PR.
    intros. eapply rclo3_mon_gen. apply PR0. apply LEclo. intros; apply PR1.
  - intros. apply PR.
Qed.

Lemma cpaco3_mon_bot (gf gf' clo clo': rel -> rel) x0 x1 x2 r' rg'
      (IN: @cpaco3 gf clo bot3 bot3 x0 x1 x2)
      (MON: monotone3 gf)
      (LEgf: gf <4= gf')
      (LEclo: clo <4= clo'):
  @cpaco3 gf' clo' r' rg' x0 x1 x2.
Proof.
  eapply cpaco3_mon_gen. apply IN. apply MON. apply LEgf. apply LEclo. contradiction. contradiction.
Qed.

End CompatiblePaco3.

Hint Resolve cpaco3_base : paco.
Hint Resolve cpaco3_step : paco.
Hint Resolve cpaco3_final : paco.
Hint Resolve rclo3_base : paco.
