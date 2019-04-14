Require Export Program.Basics. Open Scope program_scope.
Require Import paco14 pacotac cpn14.
Set Implicit Arguments.

Section CompatiblePaco14.

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
Variable T13 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) (x12: @T12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11), Type.

Local Notation rel := (rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13).

Section CompatiblePaco14_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone14 gf.

Variable clo : rel -> rel.
Hypothesis clo_compat: compatible14 gf clo.

Inductive cpaco14 r rg x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : Prop :=
| cpaco14_intro (IN: rclo14 clo (r \14/ paco14 (compose gf (rclo14 clo)) rg) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13)
.

Definition cupaco14 r := cpaco14 r r.

Lemma cpaco14_def_mon : monotone14 (compose gf (rclo14 clo)).
Proof.
  eapply compose_monotone14. apply gf_mon. apply rclo14_mon.
Qed.

Hint Resolve cpaco14_def_mon : paco.

Lemma cpaco14_mon r r' rg rg' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13
      (IN: @cpaco14 r rg x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13)
      (LEr: r <14= r')
      (LErg: rg <14= rg'):
  @cpaco14 r' rg' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13.
Proof.
  destruct IN. econstructor.
  eapply rclo14_mon. apply IN.
  intros. destruct PR. left. apply LEr, H.
  right. eapply paco14_mon. apply H. apply LErg.
Qed.

Lemma cpaco14_base r rg: r <14= cpaco14 r rg.
Proof.
  econstructor. apply rclo14_base. left. apply PR.
Qed.

Lemma cpaco14_rclo r rg:
  rclo14 clo (cpaco14 r rg) <14= cpaco14 r rg.
Proof.
  intros. econstructor. apply rclo14_rclo.
  eapply rclo14_mon. apply PR.
  intros. apply PR0.
Qed.

Lemma cpaco14_clo r rg:
  clo (cpaco14 r rg) <14= cpaco14 r rg.
Proof.
  intros. apply cpaco14_rclo. apply rclo14_clo.
  eapply clo_compat. apply PR.
  intros. apply rclo14_base. apply PR0.
Qed.

Lemma cpaco14_step r rg:
  gf (cpaco14 rg rg) <14= cpaco14 r rg.
Proof.
  intros. econstructor. apply rclo14_base. right.
  pstep. eapply gf_mon. apply PR.
  intros. destruct PR0.
  eapply rclo14_mon. apply IN.
  intros. destruct PR0; [right|left]; apply H.
Qed.

Lemma cpaco14_init:
  cpaco14 bot14 bot14 <14= paco14 gf bot14.
Proof.
  intros. destruct PR. revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 IN.
  pcofix CIH. intros.
  pstep. eapply gf_mon; [| right; apply CIH, rclo14_rclo, PR]. 
  apply compat14_compat. apply rclo14_compat. apply gf_mon. apply clo_compat.
  eapply rclo14_mon. apply IN.
  intros. destruct PR. contradiction.
  punfold H. eapply cpaco14_def_mon. apply H.
  intros. pclearbot. right. apply PR.
Qed.

Lemma cpaco14_final:
  paco14 gf bot14 <14= cpaco14 bot14 bot14.
Proof.
  intros. econstructor. apply rclo14_base.
  right. eapply paco14_mon_bot. apply PR.
  intros. eapply gf_mon. apply PR0.
  intros. apply rclo14_base. apply PR1.
Qed.

Lemma cpaco14_unfold:
  cpaco14 bot14 bot14 <14= gf (cpaco14 bot14 bot14).
Proof.
  intros. apply cpaco14_init in PR. punfold PR.
  eapply gf_mon. apply PR.
  intros. pclearbot. apply cpaco14_final, PR0.
Qed.

Lemma cpaco14_cofix
      r rg (LE: r <14= rg)
      l (OBG: forall rr (INC: rg <14= rr) (CIH: l <14= rr), l <14= cpaco14 r rr):
  l <14= cpaco14 r rg.
Proof.
  assert (IN: l <14= cpaco14 r (rg \14/ l)).
  { intros. apply OBG; [left; apply PR0 | right; apply PR0 | apply PR]. }
  clear OBG. intros. apply IN in PR.
  destruct PR. econstructor.
  eapply rclo14_mon. apply IN0.
  clear x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 IN0.
  intros. destruct PR. left. apply H.
  right. revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 H.
  pcofix CIH. intros.
  punfold H0. pstep.
  eapply gf_mon. apply H0. intros.
  apply rclo14_rclo. eapply rclo14_mon. apply PR.
  intros. destruct PR0.
  - apply rclo14_base. right. apply CIH. apply H.
  - destruct H.
    + apply rclo14_base. right. apply CIH0, H.
    + apply IN in H. destruct H.
      eapply rclo14_mon. apply IN0.
      intros. destruct PR0.
      * right. apply CIH0. apply LE, H.
      * right. apply CIH. apply H.
Qed.

Lemma cpaco14_cupaco
      r rg (LE: r <14= rg):
  cupaco14 (cpaco14 r rg) <14= cpaco14 r rg.
Proof.
  eapply cpaco14_cofix. apply LE.
  intros. destruct PR. econstructor.
  apply rclo14_rclo. eapply rclo14_mon. apply IN.
  intros. destruct PR.
  - destruct H.  eapply rclo14_mon. apply IN0.
    intros. destruct PR. left. apply H.
    right. eapply paco14_mon. apply H. apply INC.
  - apply rclo14_base. right.
    eapply paco14_mon. apply H.
    intros. apply CIH.
    econstructor. apply rclo14_base. left. apply PR.
Qed.

End CompatiblePaco14_main.

Lemma cpaco14_mon_gen (gf gf' clo clo': rel -> rel) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 r r' rg rg'
      (IN: @cpaco14 gf clo r rg x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13)
      (MON: monotone14 gf)
      (LEgf: gf <15= gf')
      (LEclo: clo <15= clo')
      (LEr: r <14= r')
      (LErg: rg <14= rg') :
  @cpaco14 gf' clo' r' rg' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13.
Proof.
  eapply cpaco14_mon; [|apply LEr|apply LErg].
  destruct IN. econstructor.
  eapply rclo14_mon_gen, IN. apply LEclo.
  intros. destruct PR. left; apply H.
  right. eapply paco14_mon_gen. apply H.
  - intros. eapply LEgf.
    eapply MON. apply PR.
    eapply rclo14_mon_gen. apply LEclo. intros; apply PR0.
  - intros. apply PR.
Qed.

End CompatiblePaco14.

Hint Resolve cpaco14_base : paco.
Hint Resolve cpaco14_step : paco.
Hint Resolve rclo14_base : paco.
Hint Resolve rclo14_clo : paco.
