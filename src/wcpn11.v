Require Import paco11 cpn11 cpntac.
Set Implicit Arguments.

Section WCompanion11.

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

Local Notation rel := (rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10).

Section WCompanion11_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone11 gf.

Inductive wcpn11 (r rg : rel) e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 : Prop :=
| wcpn11_intro (IN: cpn11 gf (r \11/ gcpn11 gf rg) e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10)
.              

Lemma wcpn11_mon r r' rg rg' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10
      (IN: @wcpn11 r rg e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10)
      (LEr: r <11= r')
      (LErg: rg <11= rg'):
  @wcpn11 r' rg' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10.
Proof.
  destruct IN. constructor.
  eapply cpn11_mon. apply IN. intros.
  destruct PR. left. apply LEr, H. right.
  eapply gcpn11_mon. apply gf_mon. apply H. apply LErg.
Qed.

Lemma wcpn11_inc_mon r rg:
  monotone11 (fun x : rel => wcpn11 r (rg \11/ x)).
Proof.
  red; intros.
  eapply wcpn11_mon. apply IN. intros. apply PR.
  intros. destruct PR. left. apply H. right. apply LE, H. 
Qed.

Lemma wcpn11_init r: wcpn11 r r <11= cpn11 gf r.
Proof.
  intros. destruct PR.
  ucpn.
  eapply cpn11_mon; [apply IN|].
  intros. destruct PR.
  - ubase. apply H.
  - ustep. apply H.
Qed.

Lemma wcpn11_final r rg: cpn11 gf r <11= wcpn11 r rg.
Proof.
  constructor. eapply cpn11_mon. apply PR.
  intros. left. apply PR0.
Qed.

Lemma wcpn11_unfold:
  wcpn11 bot11 bot11 <11= gf (wcpn11 bot11 bot11).
Proof.
  intros. apply wcpn11_init in PR. uunfold PR.
  eapply gf_mon; [apply PR|].
  intros. apply wcpn11_final. apply PR0.
Qed.

Lemma wcpn11_base r rg:
  r <11= wcpn11 r rg.
Proof.
  intros. constructor. ubase. left. apply PR.
Qed.

Lemma wcpn11_step r rg:
  gf (wcpn11 rg rg) <11= wcpn11 r rg.
Proof.
  intros. constructor. ubase. right.
  eapply gf_mon. apply PR.
  intros. apply wcpn11_init. apply PR0.
Qed.

Lemma wcpn11_cpn r rg:
  cpn11 gf (wcpn11 r rg) <11= wcpn11 r rg.
Proof.
  intros. constructor. ucpn.
  eapply cpn11_mon. apply PR.
  intros. destruct PR0. apply IN.
Qed.

Lemma wcpn11_clo r rg
      clo (LE: clo <12= cpn11 gf):
  clo (wcpn11 r rg) <11= wcpn11 r rg.
Proof.
  intros. apply wcpn11_cpn, LE, PR.
Qed.

Definition cut11 (x y z: rel) : rel := fun e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 => y <11= z /\ x e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10.

Lemma cut11_mon x y : monotone11 (cut11 x y).
Proof.
  repeat red. intros. destruct IN. split.
  - intros. apply LE, H, PR.
  - apply H0.
Qed.

Lemma cut11_wcomp r rg (LE: r <11= rg) :
  wcompatible11 gf (cut11 (cpn11 (fun x => wcpn11 r (rg \11/ x)) bot11) rg).
Proof.
  set (pfix := cpn11 (fun x => wcpn11 r (rg \11/ x)) bot11).
  
  econstructor; [apply cut11_mon|]. intros.
  destruct PR as [LEz FIX].
  uunfold FIX; [|apply wcpn11_inc_mon].
  eapply gf_mon, rclo11_cpn.
  apply cpn11_compat; [apply gf_mon|].
  eapply cpn11_mon; [apply FIX|]. clear x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 FIX; intros.

  destruct PR as [PR | PR].
  - apply LE in PR. apply LEz in PR.
    eapply gf_mon. apply PR.
    intros. apply rclo11_base. apply PR0.
  - eapply gf_mon; [apply PR|]. clear x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 PR; intros.
    eapply rclo11_cpn.
    eapply cpn11_mon. apply PR. clear x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 PR; intros.
    destruct PR as [PR | PR].
    + apply rclo11_step. eapply gf_mon. apply LEz, PR.
      intros. apply rclo11_base, PR0.
    + apply rclo11_clo. split.
      * intros. apply rclo11_step.
        eapply gf_mon. apply LEz. apply PR0.
        intros. apply rclo11_base. apply PR1.
      * apply PR.
Qed.

Lemma fix11_le_cpn r rg (LE: r <11= rg) :
  cpn11 (fun x => wcpn11 r (rg \11/ x)) bot11 <11= cpn11 gf rg.
Proof.
  intros. eexists.
  - apply wcompat11_compat, cut11_wcomp. apply gf_mon. apply LE.
  - apply rclo11_clo. split.
    + intros. apply rclo11_base. apply PR0.
    + apply PR.
Qed.

Lemma fix11_le_wcpn r rg (LE: r <11= rg):
  cpn11 (fun x => wcpn11 r (rg \11/ x)) bot11 <11= wcpn11 r rg.
Proof.
  (*
    fix
    =
    c(r + gc(rg + fix))
    <=
    c(r + gc(rg + c(rg)))  (by Lemma fix11_le_cpn)
    <=
    c(r + gc(rg))
   *)
  
  intros. uunfold PR; [| apply wcpn11_inc_mon].
  destruct PR. constructor.
  eapply cpn11_mon. apply IN. intros.
  destruct PR. left; apply H. right.
  eapply gf_mon.  apply H. intros.
  ucpn.
  eapply cpn11_mon. apply PR. intros.
  destruct PR0.
  - ubase. apply H0.
  - eapply fix11_le_cpn. apply LE. apply H0.
Qed.

Lemma wcpn11_cofix: forall
    r rg (LE: r <11= rg)
    l (OBG: forall rr (INC: rg <11= rr) (CIH: l <11= rr), l <11= wcpn11 r rr),
  l <11= wcpn11 r rg.
Proof.
  intros. apply fix11_le_wcpn. apply LE.
  eapply cpn11_algebra, PR. apply wcpn11_inc_mon.
  intros. eapply OBG; intros.
  - left. apply PR1.
  - right. apply PR1.
  - apply PR0.
Qed.

End WCompanion11_main.

Lemma wcpn11_mon_bot (gf gf': rel -> rel) e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 r rg
      (IN: @wcpn11 gf bot11 bot11 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10)
      (MONgf: monotone11 gf)
      (MONgf': monotone11 gf')
      (LE: gf <12= gf'):
  @wcpn11 gf' r rg e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10.
Proof.
  destruct IN. constructor.
  eapply cpn11_mon; [| intros; right; eapply PR].
  ubase.
  eapply gcpn11_mon_bot, LE; [|apply MONgf|apply MONgf'].
  eapply MONgf, cpn11_cpn; [| apply MONgf].
  eapply (compat11_compat (cpn11_compat MONgf)).
  eapply cpn11_mon. apply IN.
  intros. destruct PR. contradiction. apply H.
Qed.

End WCompanion11.

Hint Resolve wcpn11_base : paco.
Hint Resolve wcpn11_step : paco.

