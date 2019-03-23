Require Import paco5 cpn5 cpntac.
Set Implicit Arguments.

Section WCompanion5.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.

Local Notation rel := (rel5 T0 T1 T2 T3 T4).

Section WCompanion5_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone5 gf.

Inductive wcpn5 (r rg : rel) e0 e1 e2 e3 e4 : Prop :=
| wcpn5_intro (IN: cpn5 gf (r \5/ gcpn5 gf rg) e0 e1 e2 e3 e4)
.              

Lemma wcpn5_mon r r' rg rg' e0 e1 e2 e3 e4
      (IN: @wcpn5 r rg e0 e1 e2 e3 e4)
      (LEr: r <5= r')
      (LErg: rg <5= rg'):
  @wcpn5 r' rg' e0 e1 e2 e3 e4.
Proof.
  destruct IN. constructor.
  eapply cpn5_mon. apply IN. intros.
  destruct PR. left. apply LEr, H. right.
  eapply gcpn5_mon. apply gf_mon. apply H. apply LErg.
Qed.

Lemma wcpn5_inc_mon r rg:
  monotone5 (fun x : rel => wcpn5 r (rg \5/ x)).
Proof.
  red; intros.
  eapply wcpn5_mon. apply IN. intros. apply PR.
  intros. destruct PR. left. apply H. right. apply LE, H. 
Qed.

Lemma wcpn5_init r: wcpn5 r r <5= cpn5 gf r.
Proof.
  intros. destruct PR.
  ucpn.
  eapply cpn5_mon; [apply IN|].
  intros. destruct PR.
  - ubase. apply H.
  - ustep. apply H.
Qed.

Lemma wcpn5_final r rg: cpn5 gf r <5= wcpn5 r rg.
Proof.
  constructor. eapply cpn5_mon. apply PR.
  intros. left. apply PR0.
Qed.

Lemma wcpn5_unfold:
  wcpn5 bot5 bot5 <5= gf (wcpn5 bot5 bot5).
Proof.
  intros. apply wcpn5_init in PR. uunfold PR.
  eapply gf_mon; [apply PR|].
  intros. apply wcpn5_final. apply PR0.
Qed.

Lemma wcpn5_base r rg:
  r <5= wcpn5 r rg.
Proof.
  intros. constructor. ubase. left. apply PR.
Qed.

Lemma wcpn5_step r rg:
  gf (wcpn5 rg rg) <5= wcpn5 r rg.
Proof.
  intros. constructor. ubase. right.
  eapply gf_mon. apply PR.
  intros. apply wcpn5_init. apply PR0.
Qed.

Lemma wcpn5_cpn r rg:
  cpn5 gf (wcpn5 r rg) <5= wcpn5 r rg.
Proof.
  intros. constructor. ucpn.
  eapply cpn5_mon. apply PR.
  intros. destruct PR0. apply IN.
Qed.

Lemma wcpn5_clo r rg
      clo (LE: clo <6= cpn5 gf):
  clo (wcpn5 r rg) <5= wcpn5 r rg.
Proof.
  intros. apply wcpn5_cpn, LE, PR.
Qed.

Definition cut5 (x y z: rel) : rel := fun e0 e1 e2 e3 e4 => y <5= z /\ x e0 e1 e2 e3 e4.

Lemma cut5_mon x y : monotone5 (cut5 x y).
Proof.
  repeat red. intros. destruct IN. split.
  - intros. apply LE, H, PR.
  - apply H0.
Qed.

Lemma cut5_wcomp r rg (LE: r <5= rg) :
  wcompatible5 gf (cut5 (cpn5 (fun x => wcpn5 r (rg \5/ x)) bot5) rg).
Proof.
  set (pfix := cpn5 (fun x => wcpn5 r (rg \5/ x)) bot5).
  
  econstructor; [apply cut5_mon|]. intros.
  destruct PR as [LEz FIX].
  uunfold FIX; [|apply wcpn5_inc_mon].
  eapply gf_mon, rclo5_cpn.
  apply cpn5_compat; [apply gf_mon|].
  eapply cpn5_mon; [apply FIX|]. clear x0 x1 x2 x3 x4 FIX; intros.

  destruct PR as [PR | PR].
  - apply LE in PR. apply LEz in PR.
    eapply gf_mon. apply PR.
    intros. apply rclo5_base. apply PR0.
  - eapply gf_mon; [apply PR|]. clear x0 x1 x2 x3 x4 PR; intros.
    eapply rclo5_cpn.
    eapply cpn5_mon. apply PR. clear x0 x1 x2 x3 x4 PR; intros.
    destruct PR as [PR | PR].
    + apply rclo5_step. eapply gf_mon. apply LEz, PR.
      intros. apply rclo5_base, PR0.
    + apply rclo5_clo. split.
      * intros. apply rclo5_step.
        eapply gf_mon. apply LEz. apply PR0.
        intros. apply rclo5_base. apply PR1.
      * apply PR.
Qed.

Lemma fix5_le_cpn r rg (LE: r <5= rg) :
  cpn5 (fun x => wcpn5 r (rg \5/ x)) bot5 <5= cpn5 gf rg.
Proof.
  intros. eexists.
  - apply wcompat5_compat, cut5_wcomp. apply gf_mon. apply LE.
  - apply rclo5_clo. split.
    + intros. apply rclo5_base. apply PR0.
    + apply PR.
Qed.

Lemma fix5_le_wcpn r rg (LE: r <5= rg):
  cpn5 (fun x => wcpn5 r (rg \5/ x)) bot5 <5= wcpn5 r rg.
Proof.
  (*
    fix
    =
    c(r + gc(rg + fix))
    <=
    c(r + gc(rg + c(rg)))  (by Lemma fix5_le_cpn)
    <=
    c(r + gc(rg))
   *)
  
  intros. uunfold PR; [| apply wcpn5_inc_mon].
  destruct PR. constructor.
  eapply cpn5_mon. apply IN. intros.
  destruct PR. left; apply H. right.
  eapply gf_mon.  apply H. intros.
  ucpn.
  eapply cpn5_mon. apply PR. intros.
  destruct PR0.
  - ubase. apply H0.
  - eapply fix5_le_cpn. apply LE. apply H0.
Qed.

Lemma wcpn5_cofix: forall
    r rg (LE: r <5= rg)
    l (OBG: forall rr (INC: rg <5= rr) (CIH: l <5= rr), l <5= wcpn5 r rr),
  l <5= wcpn5 r rg.
Proof.
  intros. apply fix5_le_wcpn. apply LE.
  eapply cpn5_algebra, PR. apply wcpn5_inc_mon.
  intros. eapply OBG; intros.
  - left. apply PR1.
  - right. apply PR1.
  - apply PR0.
Qed.

End WCompanion5_main.

Lemma wcpn5_mon_bot (gf gf': rel -> rel) e0 e1 e2 e3 e4 r rg
      (IN: @wcpn5 gf bot5 bot5 e0 e1 e2 e3 e4)
      (MONgf: monotone5 gf)
      (MONgf': monotone5 gf')
      (LE: gf <6= gf'):
  @wcpn5 gf' r rg e0 e1 e2 e3 e4.
Proof.
  destruct IN. constructor.
  eapply cpn5_mon; [| intros; right; eapply PR].
  ubase.
  eapply gcpn5_mon_bot, LE; [|apply MONgf|apply MONgf'].
  eapply MONgf, cpn5_cpn; [| apply MONgf].
  eapply (compat5_compat (cpn5_compat MONgf)).
  eapply cpn5_mon. apply IN.
  intros. destruct PR. contradiction. apply H.
Qed.

End WCompanion5.

Hint Resolve wcpn5_base : paco.
Hint Resolve wcpn5_step : paco.

