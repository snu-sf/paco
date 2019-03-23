Require Import paco6 cpn6 cpntac.
Set Implicit Arguments.

Section WCompanion6.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.

Local Notation rel := (rel6 T0 T1 T2 T3 T4 T5).

Section WCompanion6_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone6 gf.

Inductive wcpn6 (r rg : rel) e0 e1 e2 e3 e4 e5 : Prop :=
| wcpn6_intro (IN: cpn6 gf (r \6/ gcpn6 gf rg) e0 e1 e2 e3 e4 e5)
.              

Lemma wcpn6_mon r r' rg rg' e0 e1 e2 e3 e4 e5
      (IN: @wcpn6 r rg e0 e1 e2 e3 e4 e5)
      (LEr: r <6= r')
      (LErg: rg <6= rg'):
  @wcpn6 r' rg' e0 e1 e2 e3 e4 e5.
Proof.
  destruct IN. constructor.
  eapply cpn6_mon. apply IN. intros.
  destruct PR. left. apply LEr, H. right.
  eapply gcpn6_mon. apply gf_mon. apply H. apply LErg.
Qed.

Lemma wcpn6_inc_mon r rg:
  monotone6 (fun x : rel => wcpn6 r (rg \6/ x)).
Proof.
  red; intros.
  eapply wcpn6_mon. apply IN. intros. apply PR.
  intros. destruct PR. left. apply H. right. apply LE, H. 
Qed.

Lemma wcpn6_init r: wcpn6 r r <6= cpn6 gf r.
Proof.
  intros. destruct PR.
  ucpn.
  eapply cpn6_mon; [apply IN|].
  intros. destruct PR.
  - ubase. apply H.
  - ustep. apply H.
Qed.

Lemma wcpn6_final r rg: cpn6 gf r <6= wcpn6 r rg.
Proof.
  constructor. eapply cpn6_mon. apply PR.
  intros. left. apply PR0.
Qed.

Lemma wcpn6_unfold:
  wcpn6 bot6 bot6 <6= gf (wcpn6 bot6 bot6).
Proof.
  intros. apply wcpn6_init in PR. uunfold PR.
  eapply gf_mon; [apply PR|].
  intros. apply wcpn6_final. apply PR0.
Qed.

Lemma wcpn6_base r rg:
  r <6= wcpn6 r rg.
Proof.
  intros. constructor. ubase. left. apply PR.
Qed.

Lemma wcpn6_step r rg:
  gf (wcpn6 rg rg) <6= wcpn6 r rg.
Proof.
  intros. constructor. ubase. right.
  eapply gf_mon. apply PR.
  intros. apply wcpn6_init. apply PR0.
Qed.

Lemma wcpn6_cpn r rg:
  cpn6 gf (wcpn6 r rg) <6= wcpn6 r rg.
Proof.
  intros. constructor. ucpn.
  eapply cpn6_mon. apply PR.
  intros. destruct PR0. apply IN.
Qed.

Lemma wcpn6_clo r rg
      clo (LE: clo <7= cpn6 gf):
  clo (wcpn6 r rg) <6= wcpn6 r rg.
Proof.
  intros. apply wcpn6_cpn, LE, PR.
Qed.

Definition cut6 (x y z: rel) : rel := fun e0 e1 e2 e3 e4 e5 => y <6= z /\ x e0 e1 e2 e3 e4 e5.

Lemma cut6_mon x y : monotone6 (cut6 x y).
Proof.
  repeat red. intros. destruct IN. split.
  - intros. apply LE, H, PR.
  - apply H0.
Qed.

Lemma cut6_wcomp r rg (LE: r <6= rg) :
  wcompatible6 gf (cut6 (cpn6 (fun x => wcpn6 r (rg \6/ x)) bot6) rg).
Proof.
  set (pfix := cpn6 (fun x => wcpn6 r (rg \6/ x)) bot6).
  
  econstructor; [apply cut6_mon|]. intros.
  destruct PR as [LEz FIX].
  uunfold FIX; [|apply wcpn6_inc_mon].
  eapply gf_mon, rclo6_cpn.
  apply cpn6_compat; [apply gf_mon|].
  eapply cpn6_mon; [apply FIX|]. clear x0 x1 x2 x3 x4 x5 FIX; intros.

  destruct PR as [PR | PR].
  - apply LE in PR. apply LEz in PR.
    eapply gf_mon. apply PR.
    intros. apply rclo6_base. apply PR0.
  - eapply gf_mon; [apply PR|]. clear x0 x1 x2 x3 x4 x5 PR; intros.
    eapply rclo6_cpn.
    eapply cpn6_mon. apply PR. clear x0 x1 x2 x3 x4 x5 PR; intros.
    destruct PR as [PR | PR].
    + apply rclo6_step. eapply gf_mon. apply LEz, PR.
      intros. apply rclo6_base, PR0.
    + apply rclo6_clo. split.
      * intros. apply rclo6_step.
        eapply gf_mon. apply LEz. apply PR0.
        intros. apply rclo6_base. apply PR1.
      * apply PR.
Qed.

Lemma fix6_le_cpn r rg (LE: r <6= rg) :
  cpn6 (fun x => wcpn6 r (rg \6/ x)) bot6 <6= cpn6 gf rg.
Proof.
  intros. eexists.
  - apply wcompat6_compat, cut6_wcomp. apply gf_mon. apply LE.
  - apply rclo6_clo. split.
    + intros. apply rclo6_base. apply PR0.
    + apply PR.
Qed.

Lemma fix6_le_wcpn r rg (LE: r <6= rg):
  cpn6 (fun x => wcpn6 r (rg \6/ x)) bot6 <6= wcpn6 r rg.
Proof.
  (*
    fix
    =
    c(r + gc(rg + fix))
    <=
    c(r + gc(rg + c(rg)))  (by Lemma fix6_le_cpn)
    <=
    c(r + gc(rg))
   *)
  
  intros. uunfold PR; [| apply wcpn6_inc_mon].
  destruct PR. constructor.
  eapply cpn6_mon. apply IN. intros.
  destruct PR. left; apply H. right.
  eapply gf_mon.  apply H. intros.
  ucpn.
  eapply cpn6_mon. apply PR. intros.
  destruct PR0.
  - ubase. apply H0.
  - eapply fix6_le_cpn. apply LE. apply H0.
Qed.

Lemma wcpn6_cofix: forall
    r rg (LE: r <6= rg)
    l (OBG: forall rr (INC: rg <6= rr) (CIH: l <6= rr), l <6= wcpn6 r rr),
  l <6= wcpn6 r rg.
Proof.
  intros. apply fix6_le_wcpn. apply LE.
  eapply cpn6_algebra, PR. apply wcpn6_inc_mon.
  intros. eapply OBG; intros.
  - left. apply PR1.
  - right. apply PR1.
  - apply PR0.
Qed.

End WCompanion6_main.

Lemma wcpn6_mon_bot (gf gf': rel -> rel) e0 e1 e2 e3 e4 e5 r rg
      (IN: @wcpn6 gf bot6 bot6 e0 e1 e2 e3 e4 e5)
      (MONgf: monotone6 gf)
      (MONgf': monotone6 gf')
      (LE: gf <7= gf'):
  @wcpn6 gf' r rg e0 e1 e2 e3 e4 e5.
Proof.
  destruct IN. constructor.
  eapply cpn6_mon; [| intros; right; eapply PR].
  ubase.
  eapply gcpn6_mon_bot, LE; [|apply MONgf|apply MONgf'].
  eapply MONgf, cpn6_cpn; [| apply MONgf].
  eapply (compat6_compat (cpn6_compat MONgf)).
  eapply cpn6_mon. apply IN.
  intros. destruct PR. contradiction. apply H.
Qed.

End WCompanion6.

Hint Resolve wcpn6_base : paco.
Hint Resolve wcpn6_step : paco.

