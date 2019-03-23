Require Import paco12 cpn12 cpntac.
Set Implicit Arguments.

Section WCompanion12.

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

Local Notation rel := (rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11).

Section WCompanion12_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone12 gf.

Inductive wcpn12 (r rg : rel) e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 : Prop :=
| wcpn12_intro (IN: cpn12 gf (r \12/ gcpn12 gf rg) e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11)
.              
Hint Constructors wcpn12.

Lemma wcpn12_mon r r' rg rg' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11
      (IN: @wcpn12 r rg e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11)
      (LEr: r <12= r')
      (LErg: rg <12= rg'):
  @wcpn12 r' rg' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.
Proof.
  destruct IN. constructor.
  eapply cpn12_mon. apply IN. intros.
  destruct PR. left. apply LEr, H. right.
  eapply gcpn12_mon. apply gf_mon. apply H. apply LErg.
Qed.

Lemma wcpn12_inc_mon r rg:
  monotone12 (fun x : rel => wcpn12 r (rg \12/ x)).
Proof.
  red; intros.
  eapply wcpn12_mon. apply IN. intros. apply PR.
  intros. destruct PR. left. apply H. right. apply LE, H. 
Qed.

Lemma wcpn12_init r: wcpn12 r r <12= cpn12 gf r.
Proof.
  intros. destruct PR.
  ucpn.
  eapply cpn12_mon; [apply IN|].
  intros. destruct PR.
  - ubase. apply H.
  - ustep. apply H.
Qed.

Lemma wcpn12_final r rg: cpn12 gf r <12= wcpn12 r rg.
Proof.
  constructor. eapply cpn12_mon. apply PR.
  intros. left. apply PR0.
Qed.

Lemma wcpn12_base r rg:
  r <12= wcpn12 r rg.
Proof.
  intros. constructor. ubase. left. apply PR.
Qed.

Lemma wcpn12_step r rg:
  gf (wcpn12 rg rg) <12= wcpn12 r rg.
Proof.
  intros. constructor. ubase. right.
  eapply gf_mon. apply PR.
  intros. apply wcpn12_init. apply PR0.
Qed.

Lemma wcpn12_cpn r rg:
  cpn12 gf (wcpn12 r rg) <12= wcpn12 r rg.
Proof.
  intros. constructor. ucpn.
  eapply cpn12_mon. apply PR.
  intros. destruct PR0. apply IN.
Qed.

Lemma wcpn12_clo r rg
      clo (LE: clo <13= cpn12 gf):
  clo (wcpn12 r rg) <12= wcpn12 r rg.
Proof.
  intros. apply wcpn12_cpn, LE, PR.
Qed.

Definition cut12 (x y z: rel) : rel := fun e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 => y <12= z /\ x e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.

Lemma cut12_mon x y : monotone12 (cut12 x y).
Proof.
  repeat red. intros. destruct IN. split.
  - intros. apply LE, H, PR.
  - apply H0.
Qed.

Lemma cut12_wcomp r rg (LE: r <12= rg) :
  wcompatible12 gf (cut12 (cpn12 (fun x => wcpn12 r (rg \12/ x)) bot12) rg).
Proof.
  set (pfix := cpn12 (fun x => wcpn12 r (rg \12/ x)) bot12).
  
  econstructor; [apply cut12_mon|]. intros.
  destruct PR as [LEz FIX].
  uunfold FIX; [|apply wcpn12_inc_mon].
  eapply gf_mon, rclo12_cpn.
  apply cpn12_compat; [apply gf_mon|].
  eapply cpn12_mon; [apply FIX|]. clear x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 FIX; intros.

  destruct PR as [PR | PR].
  - apply LE in PR. apply LEz in PR.
    eapply gf_mon. apply PR.
    intros. apply rclo12_base. apply PR0.
  - eapply gf_mon; [apply PR|]. clear x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 PR; intros.
    eapply rclo12_cpn.
    eapply cpn12_mon. apply PR. clear x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 PR; intros.
    destruct PR as [PR | PR].
    + apply rclo12_step. eapply gf_mon. apply LEz, PR.
      intros. apply rclo12_base, PR0.
    + apply rclo12_clo. split.
      * intros. apply rclo12_step.
        eapply gf_mon. apply LEz. apply PR0.
        intros. apply rclo12_base. apply PR1.
      * apply PR.
Qed.

Lemma fix12_le_cpn r rg (LE: r <12= rg) :
  cpn12 (fun x => wcpn12 r (rg \12/ x)) bot12 <12= cpn12 gf rg.
Proof.
  intros. eexists.
  - apply wcompat12_compat, cut12_wcomp. apply gf_mon. apply LE.
  - apply rclo12_clo. split.
    + intros. apply rclo12_base. apply PR0.
    + apply PR.
Qed.

Lemma fix12_le_wcpn r rg (LE: r <12= rg):
  cpn12 (fun x => wcpn12 r (rg \12/ x)) bot12 <12= wcpn12 r rg.
Proof.
  (*
    fix
    =
    c(r + gc(rg + fix))
    <=
    c(r + gc(rg + c(rg)))  (by Lemma fix12_le_cpn)
    <=
    c(r + gc(rg))
   *)
  
  intros. uunfold PR; [| apply wcpn12_inc_mon].
  destruct PR. constructor.
  eapply cpn12_mon. apply IN. intros.
  destruct PR. left; apply H. right.
  eapply gf_mon.  apply H. intros.
  ucpn.
  eapply cpn12_mon. apply PR. intros.
  destruct PR0.
  - ubase. apply H0.
  - eapply fix12_le_cpn. apply LE. apply H0.
Qed.

Lemma wcpn12_cofix: forall
    r rg (LE: r <12= rg)
    l (OBG: forall rr (INC: rg <12= rr) (CIH: l <12= rr), l <12= wcpn12 r rr),
  l <12= wcpn12 r rg.
Proof.
  intros. apply fix12_le_wcpn. apply LE.
  eapply cpn12_algebra, PR. apply wcpn12_inc_mon.
  intros. eapply OBG; intros.
  - left. apply PR1.
  - right. apply PR1.
  - apply PR0.
Qed.

End WCompanion12_main.

Lemma wcpn12_mon_bot (gf gf': rel -> rel) e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 r rg
      (IN: @wcpn12 gf bot12 bot12 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11)
      (MONgf: monotone12 gf)
      (MONgf': monotone12 gf')
      (LE: gf <13= gf'):
  @wcpn12 gf' r rg e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.
Proof.
  destruct IN. constructor.
  eapply cpn12_mon; [| intros; right; eapply PR].
  ubase.
  eapply gcpn12_mon_bot, LE; [|apply MONgf|apply MONgf'].
  eapply MONgf, cpn12_cpn; [| apply MONgf].
  eapply (compat12_compat (cpn12_compat MONgf)).
  eapply cpn12_mon. apply IN.
  intros. destruct PR. contradiction. apply H.
Qed.

End WCompanion12.

Hint Constructors wcpn12 : paco.

Hint Resolve wcpn12_base : paco.
Hint Resolve wcpn12_step : paco.
Hint Resolve wcpn12_final : paco.

