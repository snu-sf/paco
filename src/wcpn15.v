Require Import paco15 cpn15 cpntac.
Set Implicit Arguments.

Section WCompanion15.

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
Variable T14 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) (x12: @T12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) (x13: @T13 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12), Type.

Local Notation rel := (rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14).

Section WCompanion15_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone15 gf.

Inductive wcpn15 (r rg : rel) e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 : Prop :=
| wcpn15_intro (IN: cpn15 gf (r \15/ gcpn15 gf rg) e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14)
.              
Hint Constructors wcpn15.

Lemma wcpn15_mon r r' rg rg' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14
      (IN: @wcpn15 r rg e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14)
      (LEr: r <15= r')
      (LErg: rg <15= rg'):
  @wcpn15 r' rg' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14.
Proof.
  destruct IN. constructor.
  eapply cpn15_mon. apply IN. intros.
  destruct PR. left. apply LEr, H. right.
  eapply gcpn15_mon. apply gf_mon. apply H. apply LErg.
Qed.

Lemma wcpn15_inc_mon r rg:
  monotone15 (fun x : rel => wcpn15 r (rg \15/ x)).
Proof.
  red; intros.
  eapply wcpn15_mon. apply IN. intros. apply PR.
  intros. destruct PR. left. apply H. right. apply LE, H. 
Qed.

Lemma wcpn15_init r: wcpn15 r r <15= cpn15 gf r.
Proof.
  intros. destruct PR.
  ucpn.
  eapply cpn15_mon; [apply IN|].
  intros. destruct PR.
  - ubase. apply H.
  - ustep. apply H.
Qed.

Lemma wcpn15_final r rg: cpn15 gf r <15= wcpn15 r rg.
Proof.
  constructor. eapply cpn15_mon. apply PR.
  intros. left. apply PR0.
Qed.

Lemma wcpn15_base r rg:
  r <15= wcpn15 r rg.
Proof.
  intros. constructor. ubase. left. apply PR.
Qed.

Lemma wcpn15_step r rg:
  gf (wcpn15 rg rg) <15= wcpn15 r rg.
Proof.
  intros. constructor. ubase. right.
  eapply gf_mon. apply PR.
  intros. apply wcpn15_init. apply PR0.
Qed.

Lemma wcpn15_cpn r rg:
  cpn15 gf (wcpn15 r rg) <15= wcpn15 r rg.
Proof.
  intros. constructor. ucpn.
  eapply cpn15_mon. apply PR.
  intros. destruct PR0. apply IN.
Qed.

Lemma wcpn15_clo r rg
      clo (LE: clo <16= cpn15 gf):
  clo (wcpn15 r rg) <15= wcpn15 r rg.
Proof.
  intros. apply wcpn15_cpn, LE, PR.
Qed.

Definition cut15 (x y z: rel) : rel := fun e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 => y <15= z /\ x e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14.

Lemma cut15_mon x y : monotone15 (cut15 x y).
Proof.
  repeat red. intros. destruct IN. split.
  - intros. apply LE, H, PR.
  - apply H0.
Qed.

Lemma cut15_wcomp r rg (LE: r <15= rg) :
  wcompatible15 gf (cut15 (cpn15 (fun x => wcpn15 r (rg \15/ x)) bot15) rg).
Proof.
  set (pfix := cpn15 (fun x => wcpn15 r (rg \15/ x)) bot15).
  
  econstructor; [apply cut15_mon|]. intros.
  destruct PR as [LEz FIX].
  uunfold FIX; [|apply wcpn15_inc_mon].
  eapply gf_mon, rclo15_cpn.
  apply cpn15_compat; [apply gf_mon|].
  eapply cpn15_mon; [apply FIX|]. clear x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 FIX; intros.

  destruct PR as [PR | PR].
  - apply LE in PR. apply LEz in PR.
    eapply gf_mon. apply PR.
    intros. apply rclo15_base. apply PR0.
  - eapply gf_mon; [apply PR|]. clear x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 PR; intros.
    eapply rclo15_cpn.
    eapply cpn15_mon. apply PR. clear x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 PR; intros.
    destruct PR as [PR | PR].
    + apply rclo15_step. eapply gf_mon. apply LEz, PR.
      intros. apply rclo15_base, PR0.
    + apply rclo15_clo. split.
      * intros. apply rclo15_step.
        eapply gf_mon. apply LEz. apply PR0.
        intros. apply rclo15_base. apply PR1.
      * apply PR.
Qed.

Lemma fix15_le_cpn r rg (LE: r <15= rg) :
  cpn15 (fun x => wcpn15 r (rg \15/ x)) bot15 <15= cpn15 gf rg.
Proof.
  intros. eexists.
  - apply wcompat15_compat, cut15_wcomp. apply gf_mon. apply LE.
  - apply rclo15_clo. split.
    + intros. apply rclo15_base. apply PR0.
    + apply PR.
Qed.

Lemma fix15_le_wcpn r rg (LE: r <15= rg):
  cpn15 (fun x => wcpn15 r (rg \15/ x)) bot15 <15= wcpn15 r rg.
Proof.
  (*
    fix
    =
    c(r + gc(rg + fix))
    <=
    c(r + gc(rg + c(rg)))  (by Lemma fix15_le_cpn)
    <=
    c(r + gc(rg))
   *)
  
  intros. uunfold PR; [| apply wcpn15_inc_mon].
  destruct PR. constructor.
  eapply cpn15_mon. apply IN. intros.
  destruct PR. left; apply H. right.
  eapply gf_mon.  apply H. intros.
  ucpn.
  eapply cpn15_mon. apply PR. intros.
  destruct PR0.
  - ubase. apply H0.
  - eapply fix15_le_cpn. apply LE. apply H0.
Qed.

Lemma wcpn15_cofix: forall
    r rg (LE: r <15= rg)
    l (OBG: forall rr (INC: rg <15= rr) (CIH: l <15= rr), l <15= wcpn15 r rr),
  l <15= wcpn15 r rg.
Proof.
  intros. apply fix15_le_wcpn. apply LE.
  eapply cpn15_algebra, PR. apply wcpn15_inc_mon.
  intros. eapply OBG; intros.
  - left. apply PR1.
  - right. apply PR1.
  - apply PR0.
Qed.

End WCompanion15_main.

Lemma wcpn15_mon_bot (gf gf': rel -> rel) e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 r rg
      (IN: @wcpn15 gf bot15 bot15 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14)
      (MONgf: monotone15 gf)
      (MONgf': monotone15 gf')
      (LE: gf <16= gf'):
  @wcpn15 gf' r rg e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14.
Proof.
  destruct IN. constructor.
  eapply cpn15_mon; [| intros; right; eapply PR].
  ubase.
  eapply gcpn15_mon_bot, LE; [|apply MONgf|apply MONgf'].
  eapply MONgf, cpn15_cpn; [| apply MONgf].
  eapply (compat15_compat (cpn15_compat MONgf)).
  eapply cpn15_mon. apply IN.
  intros. destruct PR. contradiction. apply H.
Qed.

End WCompanion15.

Hint Constructors wcpn15 : paco.

Hint Resolve wcpn15_base : paco.
Hint Resolve wcpn15_step : paco.
Hint Resolve wcpn15_final : paco.

