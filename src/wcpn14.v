Require Import paco14 cpn14 cpntac.
Set Implicit Arguments.

Section WCompanion14.

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

Section WCompanion14_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone14 gf.

Inductive wcpn14 (r rg : rel) e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 : Prop :=
| wcpn14_intro (IN: cpn14 gf (r \14/ gcpn14 gf rg) e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13)
.              
Hint Constructors wcpn14.

Lemma wcpn14_mon r r' rg rg' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13
      (IN: @wcpn14 r rg e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13)
      (LEr: r <14= r')
      (LErg: rg <14= rg'):
  @wcpn14 r' rg' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13.
Proof.
  destruct IN. constructor.
  eapply cpn14_mon. apply IN. intros.
  destruct PR. left. apply LEr, H. right.
  eapply gcpn14_mon. apply gf_mon. apply H. apply LErg.
Qed.

Lemma wcpn14_inc_mon r rg:
  monotone14 (fun x : rel => wcpn14 r (rg \14/ x)).
Proof.
  red; intros.
  eapply wcpn14_mon. apply IN. intros. apply PR.
  intros. destruct PR. left. apply H. right. apply LE, H. 
Qed.

Lemma wcpn14_init r: wcpn14 r r <14= cpn14 gf r.
Proof.
  intros. destruct PR.
  ucpn.
  eapply cpn14_mon; [apply IN|].
  intros. destruct PR.
  - ubase. apply H.
  - ustep. apply H.
Qed.

Lemma wcpn14_final r rg: cpn14 gf r <14= wcpn14 r rg.
Proof.
  constructor. eapply cpn14_mon. apply PR.
  intros. left. apply PR0.
Qed.

Lemma wcpn14_base r rg:
  r <14= wcpn14 r rg.
Proof.
  intros. constructor. ubase. left. apply PR.
Qed.

Lemma wcpn14_step r rg:
  gf (wcpn14 rg rg) <14= wcpn14 r rg.
Proof.
  intros. constructor. ubase. right.
  eapply gf_mon. apply PR.
  intros. apply wcpn14_init. apply PR0.
Qed.

Lemma wcpn14_cpn r rg:
  cpn14 gf (wcpn14 r rg) <14= wcpn14 r rg.
Proof.
  intros. constructor. ucpn.
  eapply cpn14_mon. apply PR.
  intros. destruct PR0. apply IN.
Qed.

Lemma wcpn14_clo r rg
      clo (LE: clo <15= cpn14 gf):
  clo (wcpn14 r rg) <14= wcpn14 r rg.
Proof.
  intros. apply wcpn14_cpn, LE, PR.
Qed.

Definition cut14 (x y z: rel) : rel := fun e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 => y <14= z /\ x e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13.

Lemma cut14_mon x y : monotone14 (cut14 x y).
Proof.
  repeat red. intros. destruct IN. split.
  - intros. apply LE, H, PR.
  - apply H0.
Qed.

Lemma cut14_wcomp r rg (LE: r <14= rg) :
  wcompatible14 gf (cut14 (cpn14 (fun x => wcpn14 r (rg \14/ x)) bot14) rg).
Proof.
  set (pfix := cpn14 (fun x => wcpn14 r (rg \14/ x)) bot14).
  
  econstructor; [apply cut14_mon|]. intros.
  destruct PR as [LEz FIX].
  uunfold FIX; [|apply wcpn14_inc_mon].
  eapply gf_mon, rclo14_cpn.
  apply cpn14_compat; [apply gf_mon|].
  eapply cpn14_mon; [apply FIX|]. clear x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 FIX; intros.

  destruct PR as [PR | PR].
  - apply LE in PR. apply LEz in PR.
    eapply gf_mon. apply PR.
    intros. apply rclo14_base. apply PR0.
  - eapply gf_mon; [apply PR|]. clear x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 PR; intros.
    eapply rclo14_cpn.
    eapply cpn14_mon. apply PR. clear x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 PR; intros.
    destruct PR as [PR | PR].
    + apply rclo14_step. eapply gf_mon. apply LEz, PR.
      intros. apply rclo14_base, PR0.
    + apply rclo14_clo. split.
      * intros. apply rclo14_step.
        eapply gf_mon. apply LEz. apply PR0.
        intros. apply rclo14_base. apply PR1.
      * apply PR.
Qed.

Lemma fix14_le_cpn r rg (LE: r <14= rg) :
  cpn14 (fun x => wcpn14 r (rg \14/ x)) bot14 <14= cpn14 gf rg.
Proof.
  intros. eexists.
  - apply wcompat14_compat, cut14_wcomp. apply gf_mon. apply LE.
  - apply rclo14_clo. split.
    + intros. apply rclo14_base. apply PR0.
    + apply PR.
Qed.

Lemma fix14_le_wcpn r rg (LE: r <14= rg):
  cpn14 (fun x => wcpn14 r (rg \14/ x)) bot14 <14= wcpn14 r rg.
Proof.
  (*
    fix
    =
    c(r + gc(rg + fix))
    <=
    c(r + gc(rg + c(rg)))  (by Lemma fix14_le_cpn)
    <=
    c(r + gc(rg))
   *)
  
  intros. uunfold PR; [| apply wcpn14_inc_mon].
  destruct PR. constructor.
  eapply cpn14_mon. apply IN. intros.
  destruct PR. left; apply H. right.
  eapply gf_mon.  apply H. intros.
  ucpn.
  eapply cpn14_mon. apply PR. intros.
  destruct PR0.
  - ubase. apply H0.
  - eapply fix14_le_cpn. apply LE. apply H0.
Qed.

Lemma wcpn14_cofix: forall
    r rg (LE: r <14= rg)
    l (OBG: forall rr (INC: rg <14= rr) (CIH: l <14= rr), l <14= wcpn14 r rr),
  l <14= wcpn14 r rg.
Proof.
  intros. apply fix14_le_wcpn. apply LE.
  eapply cpn14_algebra, PR. apply wcpn14_inc_mon.
  intros. eapply OBG; intros.
  - left. apply PR1.
  - right. apply PR1.
  - apply PR0.
Qed.

End WCompanion14_main.

Lemma wcpn14_mon_bot (gf gf': rel -> rel) e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 r rg
      (IN: @wcpn14 gf bot14 bot14 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13)
      (MONgf: monotone14 gf)
      (MONgf': monotone14 gf')
      (LE: gf <15= gf'):
  @wcpn14 gf' r rg e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13.
Proof.
  destruct IN. constructor.
  eapply cpn14_mon; [| intros; right; eapply PR].
  ubase.
  eapply gcpn14_mon_bot, LE; [|apply MONgf|apply MONgf'].
  eapply MONgf, cpn14_cpn; [| apply MONgf].
  eapply (compat14_compat (cpn14_compat MONgf)).
  eapply cpn14_mon. apply IN.
  intros. destruct PR. contradiction. apply H.
Qed.

End WCompanion14.

Hint Constructors wcpn14 : paco.

Hint Resolve wcpn14_base : paco.
Hint Resolve wcpn14_step : paco.
Hint Resolve wcpn14_final : paco.

