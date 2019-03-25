Require Import paco13 cpn13 cpntac.
Set Implicit Arguments.

Section WCompanion13.

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

Section WCompanion13_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone13 gf.

Inductive gcpn13 (r rg : rel) e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 : Prop :=
| gcpn13_intro (IN: cpn13 gf (r \13/ fcpn13 gf rg) e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12)
.              

Lemma gcpn13_mon r r' rg rg' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12
      (IN: @gcpn13 r rg e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12)
      (LEr: r <13= r')
      (LErg: rg <13= rg'):
  @gcpn13 r' rg' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12.
Proof.
  destruct IN. constructor.
  eapply cpn13_mon. apply IN. intros.
  destruct PR. left. apply LEr, H. right.
  eapply fcpn13_mon. apply gf_mon. apply H. apply LErg.
Qed.

Lemma gcpn13_inc_mon r rg:
  monotone13 (fun x : rel => gcpn13 r (rg \13/ x)).
Proof.
  red; intros.
  eapply gcpn13_mon. apply IN. intros. apply PR.
  intros. destruct PR. left. apply H. right. apply LE, H. 
Qed.

Lemma gcpn13_init r: gcpn13 r r <13= cpn13 gf r.
Proof.
  intros. destruct PR.
  ucpn.
  eapply cpn13_mon; [apply IN|].
  intros. destruct PR.
  - ubase. apply H.
  - ustep. apply H.
Qed.

Lemma gcpn13_final r rg: cpn13 gf r <13= gcpn13 r rg.
Proof.
  constructor. eapply cpn13_mon. apply PR.
  intros. left. apply PR0.
Qed.

Lemma gcpn13_unfold:
  gcpn13 bot13 bot13 <13= gf (gcpn13 bot13 bot13).
Proof.
  intros. apply gcpn13_init in PR. uunfold PR.
  eapply gf_mon; [apply PR|].
  intros. apply gcpn13_final. apply PR0.
Qed.

Lemma gcpn13_base r rg:
  r <13= gcpn13 r rg.
Proof.
  intros. constructor. ubase. left. apply PR.
Qed.

Lemma gcpn13_step r rg:
  gf (gcpn13 rg rg) <13= gcpn13 r rg.
Proof.
  intros. constructor. ubase. right.
  eapply gf_mon. apply PR.
  intros. apply gcpn13_init. apply PR0.
Qed.

Lemma gcpn13_cpn r rg:
  cpn13 gf (gcpn13 r rg) <13= gcpn13 r rg.
Proof.
  intros. constructor. ucpn.
  eapply cpn13_mon. apply PR.
  intros. destruct PR0. apply IN.
Qed.

Lemma gcpn13_clo r rg
      clo (LE: clo <14= cpn13 gf):
  clo (gcpn13 r rg) <13= gcpn13 r rg.
Proof.
  intros. apply gcpn13_cpn, LE, PR.
Qed.

Definition cut13 (x y z: rel) : rel := fun e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 => y <13= z /\ x e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12.

Lemma cut13_mon x y : monotone13 (cut13 x y).
Proof.
  repeat red. intros. destruct IN. split.
  - intros. apply LE, H, PR.
  - apply H0.
Qed.

Lemma cut13_wcomp r rg (LE: r <13= rg) :
  wcompatible13 gf (cut13 (cpn13 (fun x => gcpn13 r (rg \13/ x)) bot13) rg).
Proof.
  set (pfix := cpn13 (fun x => gcpn13 r (rg \13/ x)) bot13).
  
  econstructor; [apply cut13_mon|]. intros.
  destruct PR as [LEz FIX].
  uunfold FIX; [|apply gcpn13_inc_mon].
  eapply gf_mon, rclo13_cpn.
  apply cpn13_compat; [apply gf_mon|].
  eapply cpn13_mon; [apply FIX|]. clear x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 FIX; intros.

  destruct PR as [PR | PR].
  - apply LE in PR. apply LEz in PR.
    eapply gf_mon. apply PR.
    intros. apply rclo13_base. apply PR0.
  - eapply gf_mon; [apply PR|]. clear x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 PR; intros.
    eapply rclo13_cpn.
    eapply cpn13_mon. apply PR. clear x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 PR; intros.
    destruct PR as [PR | PR].
    + apply rclo13_step. eapply gf_mon. apply LEz, PR.
      intros. apply rclo13_base, PR0.
    + apply rclo13_clo. split.
      * intros. apply rclo13_step.
        eapply gf_mon. apply LEz. apply PR0.
        intros. apply rclo13_base. apply PR1.
      * apply PR.
Qed.

Lemma fix13_le_cpn r rg (LE: r <13= rg) :
  cpn13 (fun x => gcpn13 r (rg \13/ x)) bot13 <13= cpn13 gf rg.
Proof.
  intros. eexists.
  - apply wcompat13_compat, cut13_wcomp. apply gf_mon. apply LE.
  - apply rclo13_clo. split.
    + intros. apply rclo13_base. apply PR0.
    + apply PR.
Qed.

Lemma fix13_le_gcpn r rg (LE: r <13= rg):
  cpn13 (fun x => gcpn13 r (rg \13/ x)) bot13 <13= gcpn13 r rg.
Proof.
  (*
    fix
    =
    c(r + gc(rg + fix))
    <=
    c(r + gc(rg + c(rg)))  (by Lemma fix13_le_cpn)
    <=
    c(r + gc(rg))
   *)
  
  intros. uunfold PR; [| apply gcpn13_inc_mon].
  destruct PR. constructor.
  eapply cpn13_mon. apply IN. intros.
  destruct PR. left; apply H. right.
  eapply gf_mon.  apply H. intros.
  ucpn.
  eapply cpn13_mon. apply PR. intros.
  destruct PR0.
  - ubase. apply H0.
  - eapply fix13_le_cpn. apply LE. apply H0.
Qed.

Lemma gcpn13_cofix: forall
    r rg (LE: r <13= rg)
    l (OBG: forall rr (INC: rg <13= rr) (CIH: l <13= rr), l <13= gcpn13 r rr),
  l <13= gcpn13 r rg.
Proof.
  intros. apply fix13_le_gcpn. apply LE.
  eapply cpn13_algebra, PR. apply gcpn13_inc_mon.
  intros. eapply OBG; intros.
  - left. apply PR1.
  - right. apply PR1.
  - apply PR0.
Qed.

End WCompanion13_main.

Lemma gcpn13_mon_bot (gf gf': rel -> rel) e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 r rg
      (IN: @gcpn13 gf bot13 bot13 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12)
      (MONgf: monotone13 gf)
      (MONgf': monotone13 gf')
      (LE: gf <14= gf'):
  @gcpn13 gf' r rg e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12.
Proof.
  destruct IN. constructor.
  eapply cpn13_mon; [| intros; right; eapply PR].
  ubase.
  eapply fcpn13_mon_bot, LE; [|apply MONgf|apply MONgf'].
  eapply MONgf, cpn13_cpn; [| apply MONgf].
  eapply (compat13_compat (cpn13_compat MONgf)).
  eapply cpn13_mon. apply IN.
  intros. destruct PR. contradiction. apply H.
Qed.

End WCompanion13.

Hint Resolve gcpn13_base : paco.
Hint Resolve gcpn13_step : paco.

