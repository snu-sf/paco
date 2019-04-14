Require Export Program.Basics. Open Scope program_scope.
Require Import paco13 pacotac cpn13.
Set Implicit Arguments.

Section CompatiblePaco13.

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
Variable T11 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9), Type.
Variable T12 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10), Type.

Local Notation rel := (rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12).

Section CompatiblePaco13_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone13 gf.

Variable clo : rel -> rel.
Hypothesis clo_compat: compatible13 gf clo.

Inductive cpaco13 r rg x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : Prop :=
| cpaco13_intro (IN: rclo13 clo (r \13/ paco13 (compose gf (rclo13 clo)) rg) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)
.

Definition cupaco13 r := cpaco13 r r.

Lemma cpaco13_def_mon : monotone13 (compose gf (rclo13 clo)).
Proof.
  eapply compose_monotone13. apply gf_mon. apply rclo13_mon.
Qed.

Hint Resolve cpaco13_def_mon : paco.

Lemma cpaco13_mon r r' rg rg' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12
      (IN: @cpaco13 r rg x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)
      (LEr: r <13= r')
      (LErg: rg <13= rg'):
  @cpaco13 r' rg' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12.
Proof.
  destruct IN. econstructor.
  eapply rclo13_mon. apply IN.
  intros. destruct PR. left. apply LEr, H.
  right. eapply paco13_mon. apply H. apply LErg.
Qed.

Lemma cpaco13_base r rg: r <13= cpaco13 r rg.
Proof.
  econstructor. apply rclo13_base. left. apply PR.
Qed.

Lemma cpaco13_rclo r rg:
  rclo13 clo (cpaco13 r rg) <13= cpaco13 r rg.
Proof.
  intros. econstructor. apply rclo13_rclo.
  eapply rclo13_mon. apply PR.
  intros. apply PR0.
Qed.

Lemma cpaco13_clo r rg:
  clo (cpaco13 r rg) <13= cpaco13 r rg.
Proof.
  intros. apply cpaco13_rclo. apply rclo13_clo.
  eapply clo_compat. apply PR.
  intros. apply rclo13_base. apply PR0.
Qed.

Lemma cpaco13_step r rg:
  gf (cpaco13 rg rg) <13= cpaco13 r rg.
Proof.
  intros. econstructor. apply rclo13_base. right.
  pstep. eapply gf_mon. apply PR.
  intros. destruct PR0.
  eapply rclo13_mon. apply IN.
  intros. destruct PR0; [right|left]; apply H.
Qed.

Lemma cpaco13_init:
  cpaco13 bot13 bot13 <13= paco13 gf bot13.
Proof.
  intros. destruct PR. revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 IN.
  pcofix CIH. intros.
  pstep. eapply gf_mon; [| right; apply CIH, rclo13_rclo, PR]. 
  apply compat13_compat. apply rclo13_compat. apply gf_mon. apply clo_compat.
  eapply rclo13_mon. apply IN.
  intros. destruct PR. contradiction.
  punfold H. eapply cpaco13_def_mon. apply H.
  intros. pclearbot. right. apply PR.
Qed.

Lemma cpaco13_final:
  paco13 gf bot13 <13= cpaco13 bot13 bot13.
Proof.
  intros. econstructor. apply rclo13_base.
  right. eapply paco13_mon_bot. apply PR.
  intros. eapply gf_mon. apply PR0.
  intros. apply rclo13_base. apply PR1.
Qed.

Lemma cpaco13_unfold:
  cpaco13 bot13 bot13 <13= gf (cpaco13 bot13 bot13).
Proof.
  intros. apply cpaco13_init in PR. punfold PR.
  eapply gf_mon. apply PR.
  intros. pclearbot. apply cpaco13_final, PR0.
Qed.

Lemma cpaco13_cofix
      r rg (LE: r <13= rg)
      l (OBG: forall rr (INC: rg <13= rr) (CIH: l <13= rr), l <13= cpaco13 r rr):
  l <13= cpaco13 r rg.
Proof.
  assert (IN: l <13= cpaco13 r (rg \13/ l)).
  { intros. apply OBG; [left; apply PR0 | right; apply PR0 | apply PR]. }
  clear OBG. intros. apply IN in PR.
  destruct PR. econstructor.
  eapply rclo13_mon. apply IN0.
  clear x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 IN0.
  intros. destruct PR. left. apply H.
  right. revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 H.
  pcofix CIH. intros.
  punfold H0. pstep.
  eapply gf_mon. apply H0. intros.
  apply rclo13_rclo. eapply rclo13_mon. apply PR.
  intros. destruct PR0.
  - apply rclo13_base. right. apply CIH. apply H.
  - destruct H.
    + apply rclo13_base. right. apply CIH0, H.
    + apply IN in H. destruct H.
      eapply rclo13_mon. apply IN0.
      intros. destruct PR0.
      * right. apply CIH0. apply LE, H.
      * right. apply CIH. apply H.
Qed.

Lemma cpaco13_cupaco
      r rg (LE: r <13= rg):
  cupaco13 (cpaco13 r rg) <13= cpaco13 r rg.
Proof.
  eapply cpaco13_cofix. apply LE.
  intros. destruct PR. econstructor.
  apply rclo13_rclo. eapply rclo13_mon. apply IN.
  intros. destruct PR.
  - destruct H.  eapply rclo13_mon. apply IN0.
    intros. destruct PR. left. apply H.
    right. eapply paco13_mon. apply H. apply INC.
  - apply rclo13_base. right.
    eapply paco13_mon. apply H.
    intros. apply CIH.
    econstructor. apply rclo13_base. left. apply PR.
Qed.

End CompatiblePaco13_main.

Lemma cpaco13_mon_gen (gf gf' clo clo': rel -> rel) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 r r' rg rg'
      (IN: @cpaco13 gf clo r rg x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)
      (MON: monotone13 gf)
      (LEgf: gf <14= gf')
      (LEclo: clo <14= clo')
      (LEr: r <13= r')
      (LErg: rg <13= rg') :
  @cpaco13 gf' clo' r' rg' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12.
Proof.
  eapply cpaco13_mon; [|apply LEr|apply LErg].
  destruct IN. econstructor.
  eapply rclo13_mon_gen, IN. apply LEclo.
  intros. destruct PR. left; apply H.
  right. eapply paco13_mon_gen. apply H.
  - intros. eapply LEgf.
    eapply MON. apply PR.
    eapply rclo13_mon_gen. apply LEclo. intros; apply PR0.
  - intros. apply PR.
Qed.

End CompatiblePaco13.

Hint Resolve cpaco13_base : paco.
Hint Resolve cpaco13_step : paco.
Hint Resolve rclo13_base : paco.
Hint Resolve rclo13_clo : paco.
