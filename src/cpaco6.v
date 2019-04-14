Require Export Program.Basics. Open Scope program_scope.
Require Import paco6 pacotac cpn6.
Set Implicit Arguments.

Section CompatiblePaco6.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.

Local Notation rel := (rel6 T0 T1 T2 T3 T4 T5).

Section CompatiblePaco6_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone6 gf.

Variable clo : rel -> rel.
Hypothesis clo_compat: compatible6 gf clo.

Inductive cpaco6 r rg x0 x1 x2 x3 x4 x5 : Prop :=
| cpaco6_intro (IN: rclo6 clo (r \6/ paco6 (compose gf (rclo6 clo)) rg) x0 x1 x2 x3 x4 x5)
.

Definition cupaco6 r := cpaco6 r r.

Lemma cpaco6_def_mon : monotone6 (compose gf (rclo6 clo)).
Proof.
  eapply monotone6_compose. apply gf_mon. apply rclo6_mon.
Qed.

Hint Resolve cpaco6_def_mon : paco.

Lemma cpaco6_mon r r' rg rg' x0 x1 x2 x3 x4 x5
      (IN: @cpaco6 r rg x0 x1 x2 x3 x4 x5)
      (LEr: r <6= r')
      (LErg: rg <6= rg'):
  @cpaco6 r' rg' x0 x1 x2 x3 x4 x5.
Proof.
  destruct IN. econstructor.
  eapply rclo6_mon. apply IN.
  intros. destruct PR. left. apply LEr, H.
  right. eapply paco6_mon. apply H. apply LErg.
Qed.

Lemma cpaco6_base r rg: r <6= cpaco6 r rg.
Proof.
  econstructor. apply rclo6_base. left. apply PR.
Qed.

Lemma cpaco6_rclo r rg:
  rclo6 clo (cpaco6 r rg) <6= cpaco6 r rg.
Proof.
  intros. econstructor. apply rclo6_rclo.
  eapply rclo6_mon. apply PR.
  intros. apply PR0.
Qed.

Lemma cpaco6_clo r rg:
  clo (cpaco6 r rg) <6= cpaco6 r rg.
Proof.
  intros. apply cpaco6_rclo. apply rclo6_clo.
  eapply clo_compat. apply PR.
  intros. apply rclo6_base. apply PR0.
Qed.

Lemma cpaco6_step r rg:
  gf (cpaco6 rg rg) <6= cpaco6 r rg.
Proof.
  intros. econstructor. apply rclo6_base. right.
  pstep. eapply gf_mon. apply PR.
  intros. destruct PR0.
  eapply rclo6_mon. apply IN.
  intros. destruct PR0; [right|left]; apply H.
Qed.

Lemma cpaco6_init:
  cpaco6 bot6 bot6 <6= paco6 gf bot6.
Proof.
  intros. destruct PR. revert x0 x1 x2 x3 x4 x5 IN.
  pcofix CIH. intros.
  pstep. eapply gf_mon; [| right; apply CIH, rclo6_rclo, PR]. 
  apply compat6_compat with (gf:=gf). apply rclo6_compat. apply gf_mon. apply clo_compat.
  eapply rclo6_mon. apply IN.
  intros. destruct PR. contradiction.
  _punfold H; [..|apply cpaco6_def_mon]. eapply cpaco6_def_mon. apply H.
  intros. pclearbot. right. apply PR.
Qed.

Lemma cpaco6_final:
  paco6 gf bot6 <6= cpaco6 bot6 bot6.
Proof.
  intros. econstructor. apply rclo6_base.
  right. eapply paco6_mon_bot. apply PR.
  intros. eapply gf_mon. apply PR0.
  intros. apply rclo6_base. apply PR1.
Qed.

Lemma cpaco6_unfold:
  cpaco6 bot6 bot6 <6= gf (cpaco6 bot6 bot6).
Proof.
  intros. apply cpaco6_init in PR. _punfold PR; [..|apply gf_mon].
  eapply gf_mon. apply PR.
  intros. pclearbot. apply cpaco6_final, PR0.
Qed.

Lemma cpaco6_cofix
      r rg (LE: r <6= rg)
      l (OBG: forall rr (INC: rg <6= rr) (CIH: l <6= rr), l <6= cpaco6 r rr):
  l <6= cpaco6 r rg.
Proof.
  assert (IN: l <6= cpaco6 r (rg \6/ l)).
  { intros. apply OBG; [left; apply PR0 | right; apply PR0 | apply PR]. }
  clear OBG. intros. apply IN in PR.
  destruct PR. econstructor.
  eapply rclo6_mon. apply IN0.
  clear x0 x1 x2 x3 x4 x5 IN0.
  intros. destruct PR. left. apply H.
  right. revert x0 x1 x2 x3 x4 x5 H.
  pcofix CIH. intros.
  _punfold H0; [..|apply cpaco6_def_mon]. pstep.
  eapply gf_mon. apply H0. intros.
  apply rclo6_rclo. eapply rclo6_mon. apply PR.
  intros. destruct PR0.
  - apply rclo6_base. right. apply CIH. apply H.
  - destruct H.
    + apply rclo6_base. right. apply CIH0, H.
    + apply IN in H. destruct H.
      eapply rclo6_mon. apply IN0.
      intros. destruct PR0.
      * right. apply CIH0. apply LE, H.
      * right. apply CIH. apply H.
Qed.

Lemma cpaco6_cupaco
      r rg (LEr: r <6= rg):
  cupaco6 (cpaco6 r rg) <6= cpaco6 r rg.
Proof.
  eapply cpaco6_cofix. apply LEr.
  intros. destruct PR. econstructor.
  apply rclo6_rclo. eapply rclo6_mon. apply IN.
  intros. destruct PR.
  - destruct H.  eapply rclo6_mon. apply IN0.
    intros. destruct PR. left. apply H.
    right. eapply paco6_mon. apply H. apply INC.
  - apply rclo6_base. right.
    eapply paco6_mon. apply H.
    intros. apply CIH.
    econstructor. apply rclo6_base. left. apply PR.
Qed.

Lemma cpaco6_uclo (uclo: rel -> rel)
      r rg (LEr: r <6= rg)
      (LEclo: uclo <7= cupaco6) :
  uclo (cpaco6 r rg) <6= cpaco6 r rg.
Proof.
  intros. apply cpaco6_cupaco. apply LEr. apply LEclo, PR.
Qed.

End CompatiblePaco6_main.

Lemma cpaco6_mon_gen (gf gf' clo clo': rel -> rel) x0 x1 x2 x3 x4 x5 r r' rg rg'
      (IN: @cpaco6 gf clo r rg x0 x1 x2 x3 x4 x5)
      (MON: monotone6 gf)
      (LEgf: gf <7= gf')
      (LEclo: clo <7= clo')
      (LEr: r <6= r')
      (LErg: rg <6= rg') :
  @cpaco6 gf' clo' r' rg' x0 x1 x2 x3 x4 x5.
Proof.
  eapply cpaco6_mon; [|apply LEr|apply LErg].
  destruct IN. econstructor.
  eapply rclo6_mon_gen. apply IN. apply LEclo.
  intros. destruct PR. left; apply H.
  right. eapply paco6_mon_gen. apply H.
  - intros. eapply LEgf.
    eapply MON. apply PR.
    intros. eapply rclo6_mon_gen. apply PR0. apply LEclo. intros; apply PR1.
  - intros. apply PR.
Qed.

End CompatiblePaco6.

Hint Resolve cpaco6_base : paco.
Hint Resolve cpaco6_step : paco.
Hint Resolve rclo6_base : paco.
Hint Resolve rclo6_clo : paco.
