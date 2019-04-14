Require Export Program.Basics. Open Scope program_scope.
Require Import paco8 pacotac cpn8.
Set Implicit Arguments.

Section CompatiblePaco8.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
Variable T7 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5), Type.

Local Notation rel := (rel8 T0 T1 T2 T3 T4 T5 T6 T7).

Section CompatiblePaco8_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone8 gf.

Variable clo : rel -> rel.
Hypothesis clo_compat: compatible8 gf clo.

Inductive cpaco8 r rg x0 x1 x2 x3 x4 x5 x6 x7 : Prop :=
| cpaco8_intro (IN: rclo8 clo (paco8 (compose gf (rclo8 clo)) (r \8/ rg) \8/ r) x0 x1 x2 x3 x4 x5 x6 x7)
.

Definition cupaco8 r := cpaco8 r r.

Lemma cpaco8_def_mon : monotone8 (compose gf (rclo8 clo)).
Proof.
  eapply monotone8_compose. apply gf_mon. apply rclo8_mon.
Qed.

Hint Resolve cpaco8_def_mon : paco.

Lemma cpaco8_mon r r' rg rg' x0 x1 x2 x3 x4 x5 x6 x7
      (IN: @cpaco8 r rg x0 x1 x2 x3 x4 x5 x6 x7)
      (LEr: r <8= r')
      (LErg: rg <8= rg'):
  @cpaco8 r' rg' x0 x1 x2 x3 x4 x5 x6 x7.
Proof.
  destruct IN. econstructor.
  eapply rclo8_mon. apply IN.
  intros. destruct PR; [|right; apply LEr, H].
  left. eapply paco8_mon. apply H.
  intros. destruct PR.
  - left. apply LEr, H0.
  - right. apply LErg, H0.
Qed.

Lemma cpaco8_cofix r rg 
      l (OBG: forall rr (INC: rg <8= rr) (CIH: l <8= rr), l <8= cpaco8 r rr):
  l <8= cpaco8 r rg.
Proof.
  assert (IN: l <8= cpaco8 r (rg \8/ l)).
  { intros. apply OBG; [left; apply PR0 | right; apply PR0 | apply PR]. }
  clear OBG. intros. apply IN in PR.
  destruct PR. econstructor.
  eapply rclo8_mon. apply IN0.
  clear x0 x1 x2 x3 x4 x5 x6 x7 IN0.
  intros. destruct PR; [|right; apply H].
  left. revert x0 x1 x2 x3 x4 x5 x6 x7 H.
  pcofix CIH. intros.
  _punfold H0; [..|apply cpaco8_def_mon]. pstep.
  eapply gf_mon. apply H0. intros.
  apply rclo8_rclo. eapply rclo8_mon. apply PR.
  intros. destruct PR0.
  - apply rclo8_base. right. apply CIH. apply H.
  - destruct H; [|destruct H].
    + apply rclo8_base. right. apply CIH0. left. apply H.
    + apply rclo8_base. right. apply CIH0. right. apply H.
    + apply IN in H. destruct H.
      eapply rclo8_mon. apply IN0.
      intros. destruct PR0.
      * right. apply CIH. apply H.      
      * right. apply CIH0. left. apply H.
Qed.

Lemma cpaco8_cupaco r rg:
  cupaco8 (cpaco8 r rg) <8= cpaco8 r rg.
Proof.
  eapply cpaco8_cofix.
  intros. destruct PR. econstructor.
  apply rclo8_rclo. eapply rclo8_mon. apply IN.
  intros. destruct PR.
  - apply rclo8_base. left.
    eapply paco8_mon. apply H.
    intros. right; apply CIH.
    econstructor. apply rclo8_base. right.
    destruct PR as [PR|PR]; apply PR.
  - destruct H. eapply rclo8_mon. apply IN0.
    intros. destruct PR; [| right; apply H].
    left. eapply paco8_mon. apply H.
    intros. destruct PR. left; apply H0.
    right. apply INC, H0.
Qed.

Lemma cpaco8_uclo (uclo: rel -> rel) r rg 
      (LEclo: uclo <9= cupaco8) :
  uclo (cpaco8 r rg) <8= cpaco8 r rg.
Proof.
  intros. apply cpaco8_cupaco. apply LEclo, PR.
Qed.

Lemma cpaco8_base r rg: r <8= cpaco8 r rg.
Proof.
  econstructor. apply rclo8_base. right. apply PR.
Qed.

Lemma cpaco8_rclo r:
  rclo8 clo r <8= cupaco8 r.
Proof.
  intros. econstructor.
  eapply rclo8_mon. apply PR.
  intros. right. apply PR0.
Qed.

Lemma cpaco8_clo r:
  clo r <8= cupaco8 r.
Proof.
  intros. apply cpaco8_rclo. apply rclo8_clo.
  eapply clo_compat. apply PR.
  intros. apply rclo8_base. apply PR0.
Qed.

Lemma cpaco8_step r rg:
  gf (cpaco8 rg rg) <8= cpaco8 r rg.
Proof.
  intros. econstructor. apply rclo8_base. left.
  pstep. eapply gf_mon. apply PR.
  intros. destruct PR0. eapply rclo8_mon. apply IN.
  intros. destruct PR0.
  - left. eapply paco8_mon. apply H. right. destruct PR0; apply H0.
  - right. right. apply H.
Qed.

Lemma cpaco8_init:
  cpaco8 bot8 bot8 <8= paco8 gf bot8.
Proof.
  intros. destruct PR. revert x0 x1 x2 x3 x4 x5 x6 x7 IN.
  pcofix CIH. intros.
  pstep. eapply gf_mon; [| right; apply CIH, rclo8_rclo, PR]. 
  apply compat8_compat with (gf:=gf). apply rclo8_compat. apply gf_mon. apply clo_compat.
  eapply rclo8_mon. apply IN.
  intros. pclearbot. _punfold PR; [..|apply cpaco8_def_mon].
  eapply cpaco8_def_mon. apply PR.
  intros. pclearbot. left. apply PR0.
Qed.

Lemma cpaco8_final r rg:
  (r \8/ paco8 gf rg) <8= cpaco8 r rg.
Proof.
  intros. destruct PR. apply cpaco8_base, H.
  econstructor. apply rclo8_base.
  left. eapply paco8_mon_gen. apply H.
  - intros. eapply gf_mon. apply PR.
    intros. apply rclo8_base. apply PR0.
  - intros. right. apply PR.
Qed.

Lemma cpaco8_unfold:
  cpaco8 bot8 bot8 <8= gf (cpaco8 bot8 bot8).
Proof.
  intros. apply cpaco8_init in PR. _punfold PR; [..|apply gf_mon].
  eapply gf_mon. apply PR.
  intros. pclearbot. apply cpaco8_final. right. apply PR0.
Qed.

End CompatiblePaco8_main.

Lemma cpaco8_mon_gen (gf gf' clo clo': rel -> rel) x0 x1 x2 x3 x4 x5 x6 x7 r r' rg rg'
      (IN: @cpaco8 gf clo r rg x0 x1 x2 x3 x4 x5 x6 x7)
      (MON: monotone8 gf)
      (LEgf: gf <9= gf')
      (LEclo: clo <9= clo')
      (LEr: r <8= r')
      (LErg: rg <8= rg') :
  @cpaco8 gf' clo' r' rg' x0 x1 x2 x3 x4 x5 x6 x7.
Proof.
  eapply cpaco8_mon; [|apply LEr|apply LErg].
  destruct IN. econstructor.
  eapply rclo8_mon_gen. apply IN. apply LEclo.
  intros. destruct PR; [| right; apply H].
  left. eapply paco8_mon_gen. apply H.
  - intros. eapply LEgf.
    eapply MON. apply PR.
    intros. eapply rclo8_mon_gen. apply PR0. apply LEclo. intros; apply PR1.
  - intros. apply PR.
Qed.

Lemma cpaco8_mon_bot (gf gf' clo clo': rel -> rel) x0 x1 x2 x3 x4 x5 x6 x7 r' rg'
      (IN: @cpaco8 gf clo bot8 bot8 x0 x1 x2 x3 x4 x5 x6 x7)
      (MON: monotone8 gf)
      (LEgf: gf <9= gf')
      (LEclo: clo <9= clo'):
  @cpaco8 gf' clo' r' rg' x0 x1 x2 x3 x4 x5 x6 x7.
Proof.
  eapply cpaco8_mon_gen. apply IN. apply MON. apply LEgf. apply LEclo. contradiction. contradiction.
Qed.

End CompatiblePaco8.

Hint Resolve cpaco8_base : paco.
Hint Resolve cpaco8_step : paco.
Hint Resolve cpaco8_final : paco.
Hint Resolve rclo8_base : paco.
