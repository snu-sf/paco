Require Export Program.Basics. Open Scope program_scope.
Require Import paco11 pacotac cpn11.
Set Implicit Arguments.

Section CompatiblePaco11.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
Variable T7 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5), Type.
Variable T8 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6), Type.
Variable T9 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7), Type.
Variable T10 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8), Type.

Local Notation rel := (rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10).

Section CompatiblePaco11_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone11 gf.

Variable clo : rel -> rel.
Hypothesis clo_compat: compatible11 gf clo.

Inductive cpaco11 r rg x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : Prop :=
| cpaco11_intro (IN: rclo11 clo (paco11 (compose gf (rclo11 clo)) (r \11/ rg) \11/ r) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
.

Definition cupaco11 r := cpaco11 r r.

Lemma cpaco11_def_mon : monotone11 (compose gf (rclo11 clo)).
Proof.
  eapply monotone11_compose. apply gf_mon. apply rclo11_mon.
Qed.

Hint Resolve cpaco11_def_mon : paco.

Lemma cpaco11_mon r r' rg rg' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
      (IN: @cpaco11 r rg x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
      (LEr: r <11= r')
      (LErg: rg <11= rg'):
  @cpaco11 r' rg' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10.
Proof.
  destruct IN. econstructor.
  eapply rclo11_mon. apply IN.
  intros. destruct PR; [|right; apply LEr, H].
  left. eapply paco11_mon. apply H.
  intros. destruct PR.
  - left. apply LEr, H0.
  - right. apply LErg, H0.
Qed.

Lemma cpaco11_cofix r rg 
      l (OBG: forall rr (INC: rg <11= rr) (CIH: l <11= rr), l <11= cpaco11 r rr):
  l <11= cpaco11 r rg.
Proof.
  assert (IN: l <11= cpaco11 r (rg \11/ l)).
  { intros. apply OBG; [left; apply PR0 | right; apply PR0 | apply PR]. }
  clear OBG. intros. apply IN in PR.
  destruct PR. econstructor.
  eapply rclo11_mon. apply IN0.
  clear x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 IN0.
  intros. destruct PR; [|right; apply H].
  left. revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 H.
  pcofix CIH. intros.
  _punfold H0; [..|apply cpaco11_def_mon]. pstep.
  eapply gf_mon. apply H0. intros.
  apply rclo11_rclo. eapply rclo11_mon. apply PR.
  intros. destruct PR0.
  - apply rclo11_base. right. apply CIH. apply H.
  - destruct H; [|destruct H].
    + apply rclo11_base. right. apply CIH0. left. apply H.
    + apply rclo11_base. right. apply CIH0. right. apply H.
    + apply IN in H. destruct H.
      eapply rclo11_mon. apply IN0.
      intros. destruct PR0.
      * right. apply CIH. apply H.      
      * right. apply CIH0. left. apply H.
Qed.

Lemma cpaco11_cupaco r rg:
  cupaco11 (cpaco11 r rg) <11= cpaco11 r rg.
Proof.
  eapply cpaco11_cofix.
  intros. destruct PR. econstructor.
  apply rclo11_rclo. eapply rclo11_mon. apply IN.
  intros. destruct PR.
  - apply rclo11_base. left.
    eapply paco11_mon. apply H.
    intros. right; apply CIH.
    econstructor. apply rclo11_base. right.
    destruct PR as [PR|PR]; apply PR.
  - destruct H. eapply rclo11_mon. apply IN0.
    intros. destruct PR; [| right; apply H].
    left. eapply paco11_mon. apply H.
    intros. destruct PR. left; apply H0.
    right. apply INC, H0.
Qed.

Lemma cpaco11_uclo (uclo: rel -> rel) r rg 
      (LEclo: uclo <12= cupaco11) :
  uclo (cpaco11 r rg) <11= cpaco11 r rg.
Proof.
  intros. apply cpaco11_cupaco. apply LEclo, PR.
Qed.

Lemma cpaco11_base r rg: r <11= cpaco11 r rg.
Proof.
  econstructor. apply rclo11_base. right. apply PR.
Qed.

Lemma cpaco11_rclo r:
  rclo11 clo r <11= cupaco11 r.
Proof.
  intros. econstructor.
  eapply rclo11_mon. apply PR.
  intros. right. apply PR0.
Qed.

Lemma cpaco11_clo r:
  clo r <11= cupaco11 r.
Proof.
  intros. apply cpaco11_rclo. apply rclo11_clo.
  eapply clo_compat. apply PR.
  intros. apply rclo11_base. apply PR0.
Qed.

Lemma cpaco11_step r rg:
  gf (cpaco11 rg rg) <11= cpaco11 r rg.
Proof.
  intros. econstructor. apply rclo11_base. left.
  pstep. eapply gf_mon. apply PR.
  intros. destruct PR0. eapply rclo11_mon. apply IN.
  intros. destruct PR0.
  - left. eapply paco11_mon. apply H. right. destruct PR0; apply H0.
  - right. right. apply H.
Qed.

Lemma cpaco11_init:
  cpaco11 bot11 bot11 <11= paco11 gf bot11.
Proof.
  intros. destruct PR. revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 IN.
  pcofix CIH. intros.
  pstep. eapply gf_mon; [| right; apply CIH, rclo11_rclo, PR]. 
  apply compat11_compat with (gf:=gf). apply rclo11_compat. apply gf_mon. apply clo_compat.
  eapply rclo11_mon. apply IN.
  intros. pclearbot. _punfold PR; [..|apply cpaco11_def_mon].
  eapply cpaco11_def_mon. apply PR.
  intros. pclearbot. left. apply PR0.
Qed.

Lemma cpaco11_final r rg:
  (r \11/ paco11 gf rg) <11= cpaco11 r rg.
Proof.
  intros. destruct PR. apply cpaco11_base, H.
  econstructor. apply rclo11_base.
  left. eapply paco11_mon_gen. apply H.
  - intros. eapply gf_mon. apply PR.
    intros. apply rclo11_base. apply PR0.
  - intros. right. apply PR.
Qed.

Lemma cpaco11_unfold:
  cpaco11 bot11 bot11 <11= gf (cpaco11 bot11 bot11).
Proof.
  intros. apply cpaco11_init in PR. _punfold PR; [..|apply gf_mon].
  eapply gf_mon. apply PR.
  intros. pclearbot. apply cpaco11_final. right. apply PR0.
Qed.

End CompatiblePaco11_main.

Lemma cpaco11_mon_gen (gf gf' clo clo': rel -> rel) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 r r' rg rg'
      (IN: @cpaco11 gf clo r rg x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
      (MON: monotone11 gf)
      (LEgf: gf <12= gf')
      (LEclo: clo <12= clo')
      (LEr: r <11= r')
      (LErg: rg <11= rg') :
  @cpaco11 gf' clo' r' rg' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10.
Proof.
  eapply cpaco11_mon; [|apply LEr|apply LErg].
  destruct IN. econstructor.
  eapply rclo11_mon_gen. apply IN. apply LEclo.
  intros. destruct PR; [| right; apply H].
  left. eapply paco11_mon_gen. apply H.
  - intros. eapply LEgf.
    eapply MON. apply PR.
    intros. eapply rclo11_mon_gen. apply PR0. apply LEclo. intros; apply PR1.
  - intros. apply PR.
Qed.

Lemma cpaco11_mon_bot (gf gf' clo clo': rel -> rel) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 r' rg'
      (IN: @cpaco11 gf clo bot11 bot11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
      (MON: monotone11 gf)
      (LEgf: gf <12= gf')
      (LEclo: clo <12= clo'):
  @cpaco11 gf' clo' r' rg' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10.
Proof.
  eapply cpaco11_mon_gen. apply IN. apply MON. apply LEgf. apply LEclo. contradiction. contradiction.
Qed.

End CompatiblePaco11.

Hint Resolve cpaco11_base : paco.
Hint Resolve cpaco11_step : paco.
Hint Resolve cpaco11_final : paco.
Hint Resolve rclo11_base : paco.
