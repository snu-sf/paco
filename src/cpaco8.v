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
| cpaco8_intro (IN: rclo8 clo (r \8/ paco8 (compose gf (rclo8 clo)) rg) x0 x1 x2 x3 x4 x5 x6 x7)
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
  intros. destruct PR. left. apply LEr, H.
  right. eapply paco8_mon. apply H. apply LErg.
Qed.

Lemma cpaco8_base r rg: r <8= cpaco8 r rg.
Proof.
  econstructor. apply rclo8_base. left. apply PR.
Qed.

Lemma cpaco8_rclo r rg:
  rclo8 clo (cpaco8 r rg) <8= cpaco8 r rg.
Proof.
  intros. econstructor. apply rclo8_rclo.
  eapply rclo8_mon. apply PR.
  intros. apply PR0.
Qed.

Lemma cpaco8_clo r rg:
  clo (cpaco8 r rg) <8= cpaco8 r rg.
Proof.
  intros. apply cpaco8_rclo. apply rclo8_clo.
  eapply clo_compat. apply PR.
  intros. apply rclo8_base. apply PR0.
Qed.

Lemma cpaco8_step r rg:
  gf (cpaco8 rg rg) <8= cpaco8 r rg.
Proof.
  intros. econstructor. apply rclo8_base. right.
  pstep. eapply gf_mon. apply PR.
  intros. destruct PR0.
  eapply rclo8_mon. apply IN.
  intros. destruct PR0; [right|left]; apply H.
Qed.

Lemma cpaco8_init:
  cpaco8 bot8 bot8 <8= paco8 gf bot8.
Proof.
  intros. destruct PR. revert x0 x1 x2 x3 x4 x5 x6 x7 IN.
  pcofix CIH. intros.
  pstep. eapply gf_mon; [| right; apply CIH, rclo8_rclo, PR]. 
  apply compat8_compat with (gf:=gf). apply rclo8_compat. apply gf_mon. apply clo_compat.
  eapply rclo8_mon. apply IN.
  intros. destruct PR. contradiction.
  _punfold H; [..|apply cpaco8_def_mon]. eapply cpaco8_def_mon. apply H.
  intros. pclearbot. right. apply PR.
Qed.

Lemma cpaco8_final:
  paco8 gf bot8 <8= cpaco8 bot8 bot8.
Proof.
  intros. econstructor. apply rclo8_base.
  right. eapply paco8_mon_bot. apply PR.
  intros. eapply gf_mon. apply PR0.
  intros. apply rclo8_base. apply PR1.
Qed.

Lemma cpaco8_unfold:
  cpaco8 bot8 bot8 <8= gf (cpaco8 bot8 bot8).
Proof.
  intros. apply cpaco8_init in PR. _punfold PR; [..|apply gf_mon].
  eapply gf_mon. apply PR.
  intros. pclearbot. apply cpaco8_final, PR0.
Qed.

Lemma cpaco8_cofix
      r rg (LE: r <8= rg)
      l (OBG: forall rr (INC: rg <8= rr) (CIH: l <8= rr), l <8= cpaco8 r rr):
  l <8= cpaco8 r rg.
Proof.
  assert (IN: l <8= cpaco8 r (rg \8/ l)).
  { intros. apply OBG; [left; apply PR0 | right; apply PR0 | apply PR]. }
  clear OBG. intros. apply IN in PR.
  destruct PR. econstructor.
  eapply rclo8_mon. apply IN0.
  clear x0 x1 x2 x3 x4 x5 x6 x7 IN0.
  intros. destruct PR. left. apply H.
  right. revert x0 x1 x2 x3 x4 x5 x6 x7 H.
  pcofix CIH. intros.
  _punfold H0; [..|apply cpaco8_def_mon]. pstep.
  eapply gf_mon. apply H0. intros.
  apply rclo8_rclo. eapply rclo8_mon. apply PR.
  intros. destruct PR0.
  - apply rclo8_base. right. apply CIH. apply H.
  - destruct H.
    + apply rclo8_base. right. apply CIH0, H.
    + apply IN in H. destruct H.
      eapply rclo8_mon. apply IN0.
      intros. destruct PR0.
      * right. apply CIH0. apply LE, H.
      * right. apply CIH. apply H.
Qed.

Lemma cpaco8_cupaco
      r rg (LEr: r <8= rg):
  cupaco8 (cpaco8 r rg) <8= cpaco8 r rg.
Proof.
  eapply cpaco8_cofix. apply LEr.
  intros. destruct PR. econstructor.
  apply rclo8_rclo. eapply rclo8_mon. apply IN.
  intros. destruct PR.
  - destruct H.  eapply rclo8_mon. apply IN0.
    intros. destruct PR. left. apply H.
    right. eapply paco8_mon. apply H. apply INC.
  - apply rclo8_base. right.
    eapply paco8_mon. apply H.
    intros. apply CIH.
    econstructor. apply rclo8_base. left. apply PR.
Qed.

Lemma cpaco8_uclo (uclo: rel -> rel)
      r rg (LEr: r <8= rg)
      (LEclo: uclo <9= cupaco8) :
  uclo (cpaco8 r rg) <8= cpaco8 r rg.
Proof.
  intros. apply cpaco8_cupaco. apply LEr. apply LEclo, PR.
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
  intros. destruct PR. left; apply H.
  right. eapply paco8_mon_gen. apply H.
  - intros. eapply LEgf.
    eapply MON. apply PR.
    intros. eapply rclo8_mon_gen. apply PR0. apply LEclo. intros; apply PR1.
  - intros. apply PR.
Qed.

End CompatiblePaco8.

Hint Resolve cpaco8_base : paco.
Hint Resolve cpaco8_step : paco.
Hint Resolve rclo8_base : paco.
Hint Resolve rclo8_clo : paco.
