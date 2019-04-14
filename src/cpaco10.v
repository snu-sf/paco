Require Export Program.Basics. Open Scope program_scope.
Require Import paco10 pacotac cpn10.
Set Implicit Arguments.

Section CompatiblePaco10.

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

Local Notation rel := (rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9).

Section CompatiblePaco10_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone10 gf.

Variable clo : rel -> rel.
Hypothesis clo_compat: compatible10 gf clo.

Inductive cpaco10 r rg x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Prop :=
| cpaco10_intro (IN: rclo10 clo (r \10/ paco10 (compose gf (rclo10 clo)) rg) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)
.

Definition cupaco10 r := cpaco10 r r.

Lemma cpaco10_def_mon : monotone10 (compose gf (rclo10 clo)).
Proof.
  eapply compose_monotone10. apply gf_mon. apply rclo10_mon.
Qed.

Hint Resolve cpaco10_def_mon : paco.

Lemma cpaco10_mon r r' rg rg' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9
      (IN: @cpaco10 r rg x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)
      (LEr: r <10= r')
      (LErg: rg <10= rg'):
  @cpaco10 r' rg' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9.
Proof.
  destruct IN. econstructor.
  eapply rclo10_mon. apply IN.
  intros. destruct PR. left. apply LEr, H.
  right. eapply paco10_mon. apply H. apply LErg.
Qed.

Lemma cpaco10_base r rg: r <10= cpaco10 r rg.
Proof.
  econstructor. apply rclo10_base. left. apply PR.
Qed.

Lemma cpaco10_rclo r rg:
  rclo10 clo (cpaco10 r rg) <10= cpaco10 r rg.
Proof.
  intros. econstructor. apply rclo10_rclo.
  eapply rclo10_mon. apply PR.
  intros. apply PR0.
Qed.

Lemma cpaco10_clo r rg:
  clo (cpaco10 r rg) <10= cpaco10 r rg.
Proof.
  intros. apply cpaco10_rclo. apply rclo10_clo.
  eapply clo_compat. apply PR.
  intros. apply rclo10_base. apply PR0.
Qed.

Lemma cpaco10_step r rg:
  gf (cpaco10 rg rg) <10= cpaco10 r rg.
Proof.
  intros. econstructor. apply rclo10_base. right.
  pstep. eapply gf_mon. apply PR.
  intros. destruct PR0.
  eapply rclo10_mon. apply IN.
  intros. destruct PR0; [right|left]; apply H.
Qed.

Lemma cpaco10_init:
  cpaco10 bot10 bot10 <10= paco10 gf bot10.
Proof.
  intros. destruct PR. revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 IN.
  pcofix CIH. intros.
  pstep. eapply gf_mon; [| right; apply CIH, rclo10_rclo, PR]. 
  apply compat10_compat. apply rclo10_compat. apply gf_mon. apply clo_compat.
  eapply rclo10_mon. apply IN.
  intros. destruct PR. contradiction.
  punfold H. eapply cpaco10_def_mon. apply H.
  intros. pclearbot. right. apply PR.
Qed.

Lemma cpaco10_final:
  paco10 gf bot10 <10= cpaco10 bot10 bot10.
Proof.
  intros. econstructor. apply rclo10_base.
  right. eapply paco10_mon_bot. apply PR.
  intros. eapply gf_mon. apply PR0.
  intros. apply rclo10_base. apply PR1.
Qed.

Lemma cpaco10_unfold:
  cpaco10 bot10 bot10 <10= gf (cpaco10 bot10 bot10).
Proof.
  intros. apply cpaco10_init in PR. punfold PR.
  eapply gf_mon. apply PR.
  intros. pclearbot. apply cpaco10_final, PR0.
Qed.

Lemma cpaco10_cofix
      r rg (LE: r <10= rg)
      l (OBG: forall rr (INC: rg <10= rr) (CIH: l <10= rr), l <10= cpaco10 r rr):
  l <10= cpaco10 r rg.
Proof.
  assert (IN: l <10= cpaco10 r (rg \10/ l)).
  { intros. apply OBG; [left; apply PR0 | right; apply PR0 | apply PR]. }
  clear OBG. intros. apply IN in PR.
  destruct PR. econstructor.
  eapply rclo10_mon. apply IN0.
  clear x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 IN0.
  intros. destruct PR. left. apply H.
  right. revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 H.
  pcofix CIH. intros.
  punfold H0. pstep.
  eapply gf_mon. apply H0. intros.
  apply rclo10_rclo. eapply rclo10_mon. apply PR.
  intros. destruct PR0.
  - apply rclo10_base. right. apply CIH. apply H.
  - destruct H.
    + apply rclo10_base. right. apply CIH0, H.
    + apply IN in H. destruct H.
      eapply rclo10_mon. apply IN0.
      intros. destruct PR0.
      * right. apply CIH0. apply LE, H.
      * right. apply CIH. apply H.
Qed.

Lemma cpaco10_cupaco
      r rg (LE: r <10= rg):
  cupaco10 (cpaco10 r rg) <10= cpaco10 r rg.
Proof.
  eapply cpaco10_cofix. apply LE.
  intros. destruct PR. econstructor.
  apply rclo10_rclo. eapply rclo10_mon. apply IN.
  intros. destruct PR.
  - destruct H.  eapply rclo10_mon. apply IN0.
    intros. destruct PR. left. apply H.
    right. eapply paco10_mon. apply H. apply INC.
  - apply rclo10_base. right.
    eapply paco10_mon. apply H.
    intros. apply CIH.
    econstructor. apply rclo10_base. left. apply PR.
Qed.

End CompatiblePaco10_main.

Lemma cpaco10_mon_gen (gf gf' clo clo': rel -> rel) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 r r' rg rg'
      (IN: @cpaco10 gf clo r rg x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)
      (MON: monotone10 gf)
      (LEgf: gf <11= gf')
      (LEclo: clo <11= clo')
      (LEr: r <10= r')
      (LErg: rg <10= rg') :
  @cpaco10 gf' clo' r' rg' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9.
Proof.
  eapply cpaco10_mon; [|apply LEr|apply LErg].
  destruct IN. econstructor.
  eapply rclo10_mon_gen, IN. apply LEclo.
  intros. destruct PR. left; apply H.
  right. eapply paco10_mon_gen. apply H.
  - intros. eapply LEgf.
    eapply MON. apply PR.
    eapply rclo10_mon_gen. apply LEclo. intros; apply PR0.
  - intros. apply PR.
Qed.

End CompatiblePaco10.

Hint Resolve cpaco10_base : paco.
Hint Resolve cpaco10_step : paco.
Hint Resolve rclo10_base : paco.
Hint Resolve rclo10_clo : paco.
