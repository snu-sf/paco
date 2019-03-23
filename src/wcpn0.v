Require Import paco0 cpn0 cpntac.
Set Implicit Arguments.

Section WCompanion0.


Local Notation rel := (rel0).

Section WCompanion0_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone0 gf.

Inductive wcpn0 (r rg : rel) : Prop :=
| wcpn0_intro (IN: cpn0 gf (r \0/ gcpn0 gf rg))
.              

Lemma wcpn0_mon r r' rg rg'
      (IN: @wcpn0 r rg)
      (LEr: r <0= r')
      (LErg: rg <0= rg'):
  @wcpn0 r' rg'.
Proof.
  destruct IN. constructor.
  eapply cpn0_mon. apply IN. intros.
  destruct PR. left. apply LEr, H. right.
  eapply gcpn0_mon. apply gf_mon. apply H. apply LErg.
Qed.

Lemma wcpn0_inc_mon r rg:
  monotone0 (fun x : rel => wcpn0 r (rg \0/ x)).
Proof.
  red; intros.
  eapply wcpn0_mon. apply IN. intros. apply PR.
  intros. destruct PR. left. apply H. right. apply LE, H. 
Qed.

Lemma wcpn0_init r: wcpn0 r r <0= cpn0 gf r.
Proof.
  intros. destruct PR.
  ucpn.
  eapply cpn0_mon; [apply IN|].
  intros. destruct PR.
  - ubase. apply H.
  - ustep. apply H.
Qed.

Lemma wcpn0_final r rg: cpn0 gf r <0= wcpn0 r rg.
Proof.
  constructor. eapply cpn0_mon. apply PR.
  intros. left. apply PR0.
Qed.

Lemma wcpn0_unfold:
  wcpn0 bot0 bot0 <0= gf (wcpn0 bot0 bot0).
Proof.
  intros. apply wcpn0_init in PR. uunfold PR.
  eapply gf_mon; [apply PR|].
  intros. apply wcpn0_final. apply PR0.
Qed.

Lemma wcpn0_base r rg:
  r <0= wcpn0 r rg.
Proof.
  intros. constructor. ubase. left. apply PR.
Qed.

Lemma wcpn0_step r rg:
  gf (wcpn0 rg rg) <0= wcpn0 r rg.
Proof.
  intros. constructor. ubase. right.
  eapply gf_mon. apply PR.
  intros. apply wcpn0_init. apply PR0.
Qed.

Lemma wcpn0_cpn r rg:
  cpn0 gf (wcpn0 r rg) <0= wcpn0 r rg.
Proof.
  intros. constructor. ucpn.
  eapply cpn0_mon. apply PR.
  intros. destruct PR0. apply IN.
Qed.

Lemma wcpn0_clo r rg
      clo (LE: clo <1= cpn0 gf):
  clo (wcpn0 r rg) <0= wcpn0 r rg.
Proof.
  intros. apply wcpn0_cpn, LE, PR.
Qed.

Definition cut0 (x y z: rel) : rel := y <0= z /\ x.

Lemma cut0_mon x y : monotone0 (cut0 x y).
Proof.
  repeat red. intros. destruct IN. split.
  - intros. apply LE, H, PR.
  - apply H0.
Qed.

Lemma cut0_wcomp r rg (LE: r <0= rg) :
  wcompatible0 gf (cut0 (cpn0 (fun x => wcpn0 r (rg \0/ x)) bot0) rg).
Proof.
  set (pfix := cpn0 (fun x => wcpn0 r (rg \0/ x)) bot0).
  
  econstructor; [apply cut0_mon|]. intros.
  destruct PR as [LEz FIX].
  uunfold FIX; [|apply wcpn0_inc_mon].
  eapply gf_mon, rclo0_cpn.
  apply cpn0_compat; [apply gf_mon|].
  eapply cpn0_mon; [apply FIX|]. clear FIX; intros.

  destruct PR as [PR | PR].
  - apply LE in PR. apply LEz in PR.
    eapply gf_mon. apply PR.
    intros. apply rclo0_base. apply PR0.
  - eapply gf_mon; [apply PR|]. clear PR; intros.
    eapply rclo0_cpn.
    eapply cpn0_mon. apply PR. clear PR; intros.
    destruct PR as [PR | PR].
    + apply rclo0_step. eapply gf_mon. apply LEz, PR.
      intros. apply rclo0_base, PR0.
    + apply rclo0_clo. split.
      * intros. apply rclo0_step.
        eapply gf_mon. apply LEz. apply PR0.
        intros. apply rclo0_base. apply PR1.
      * apply PR.
Qed.

Lemma fix0_le_cpn r rg (LE: r <0= rg) :
  cpn0 (fun x => wcpn0 r (rg \0/ x)) bot0 <0= cpn0 gf rg.
Proof.
  intros. eexists.
  - apply wcompat0_compat, cut0_wcomp. apply gf_mon. apply LE.
  - apply rclo0_clo. split.
    + intros. apply rclo0_base. apply PR0.
    + apply PR.
Qed.

Lemma fix0_le_wcpn r rg (LE: r <0= rg):
  cpn0 (fun x => wcpn0 r (rg \0/ x)) bot0 <0= wcpn0 r rg.
Proof.
  (*
    fix
    =
    c(r + gc(rg + fix))
    <=
    c(r + gc(rg + c(rg)))  (by Lemma fix0_le_cpn)
    <=
    c(r + gc(rg))
   *)
  
  intros. uunfold PR; [| apply wcpn0_inc_mon].
  destruct PR. constructor.
  eapply cpn0_mon. apply IN. intros.
  destruct PR. left; apply H. right.
  eapply gf_mon.  apply H. intros.
  ucpn.
  eapply cpn0_mon. apply PR. intros.
  destruct PR0.
  - ubase. apply H0.
  - eapply fix0_le_cpn. apply LE. apply H0.
Qed.

Lemma wcpn0_cofix: forall
    r rg (LE: r <0= rg)
    l (OBG: forall rr (INC: rg <0= rr) (CIH: l <0= rr), l <0= wcpn0 r rr),
  l <0= wcpn0 r rg.
Proof.
  intros. apply fix0_le_wcpn. apply LE.
  eapply cpn0_algebra, PR. apply wcpn0_inc_mon.
  intros. eapply OBG; intros.
  - left. apply PR1.
  - right. apply PR1.
  - apply PR0.
Qed.

End WCompanion0_main.

Lemma wcpn0_mon_bot (gf gf': rel -> rel) r rg
      (IN: @wcpn0 gf bot0 bot0)
      (MONgf: monotone0 gf)
      (MONgf': monotone0 gf')
      (LE: gf <1= gf'):
  @wcpn0 gf' r rg.
Proof.
  destruct IN. constructor.
  eapply cpn0_mon; [| intros; right; eapply PR].
  ubase.
  eapply gcpn0_mon_bot, LE; [|apply MONgf|apply MONgf'].
  eapply MONgf, cpn0_cpn; [| apply MONgf].
  eapply (compat0_compat (cpn0_compat MONgf)).
  eapply cpn0_mon. apply IN.
  intros. destruct PR. contradiction. apply H.
Qed.

End WCompanion0.

Hint Resolve wcpn0_base : paco.
Hint Resolve wcpn0_step : paco.

