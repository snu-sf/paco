Require Import paco7 cpn7 cpntac.
Set Implicit Arguments.

Section WCompanion7.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.

Local Notation rel := (rel7 T0 T1 T2 T3 T4 T5 T6).

Section WCompanion7_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone7 gf.

Inductive wcpn7 (r rg : rel) e0 e1 e2 e3 e4 e5 e6 : Prop :=
| wcpn7_intro (IN: cpn7 gf (r \7/ gcpn7 gf rg) e0 e1 e2 e3 e4 e5 e6)
.              

Lemma wcpn7_mon r r' rg rg' e0 e1 e2 e3 e4 e5 e6
      (IN: @wcpn7 r rg e0 e1 e2 e3 e4 e5 e6)
      (LEr: r <7= r')
      (LErg: rg <7= rg'):
  @wcpn7 r' rg' e0 e1 e2 e3 e4 e5 e6.
Proof.
  destruct IN. constructor.
  eapply cpn7_mon. apply IN. intros.
  destruct PR. left. apply LEr, H. right.
  eapply gcpn7_mon. apply gf_mon. apply H. apply LErg.
Qed.

Lemma wcpn7_inc_mon r rg:
  monotone7 (fun x : rel => wcpn7 r (rg \7/ x)).
Proof.
  red; intros.
  eapply wcpn7_mon. apply IN. intros. apply PR.
  intros. destruct PR. left. apply H. right. apply LE, H. 
Qed.

Lemma wcpn7_init r: wcpn7 r r <7= cpn7 gf r.
Proof.
  intros. destruct PR.
  ucpn.
  eapply cpn7_mon; [apply IN|].
  intros. destruct PR.
  - ubase. apply H.
  - ustep. apply H.
Qed.

Lemma wcpn7_final r rg: cpn7 gf r <7= wcpn7 r rg.
Proof.
  constructor. eapply cpn7_mon. apply PR.
  intros. left. apply PR0.
Qed.

Lemma wcpn7_unfold:
  wcpn7 bot7 bot7 <7= gf (wcpn7 bot7 bot7).
Proof.
  intros. apply wcpn7_init in PR. uunfold PR.
  eapply gf_mon; [apply PR|].
  intros. apply wcpn7_final. apply PR0.
Qed.

Lemma wcpn7_base r rg:
  r <7= wcpn7 r rg.
Proof.
  intros. constructor. ubase. left. apply PR.
Qed.

Lemma wcpn7_step r rg:
  gf (wcpn7 rg rg) <7= wcpn7 r rg.
Proof.
  intros. constructor. ubase. right.
  eapply gf_mon. apply PR.
  intros. apply wcpn7_init. apply PR0.
Qed.

Lemma wcpn7_cpn r rg:
  cpn7 gf (wcpn7 r rg) <7= wcpn7 r rg.
Proof.
  intros. constructor. ucpn.
  eapply cpn7_mon. apply PR.
  intros. destruct PR0. apply IN.
Qed.

Lemma wcpn7_clo r rg
      clo (LE: clo <8= cpn7 gf):
  clo (wcpn7 r rg) <7= wcpn7 r rg.
Proof.
  intros. apply wcpn7_cpn, LE, PR.
Qed.

Definition cut7 (x y z: rel) : rel := fun e0 e1 e2 e3 e4 e5 e6 => y <7= z /\ x e0 e1 e2 e3 e4 e5 e6.

Lemma cut7_mon x y : monotone7 (cut7 x y).
Proof.
  repeat red. intros. destruct IN. split.
  - intros. apply LE, H, PR.
  - apply H0.
Qed.

Lemma cut7_wcomp r rg (LE: r <7= rg) :
  wcompatible7 gf (cut7 (cpn7 (fun x => wcpn7 r (rg \7/ x)) bot7) rg).
Proof.
  set (pfix := cpn7 (fun x => wcpn7 r (rg \7/ x)) bot7).
  
  econstructor; [apply cut7_mon|]. intros.
  destruct PR as [LEz FIX].
  uunfold FIX; [|apply wcpn7_inc_mon].
  eapply gf_mon, rclo7_cpn.
  apply cpn7_compat; [apply gf_mon|].
  eapply cpn7_mon; [apply FIX|]. clear x0 x1 x2 x3 x4 x5 x6 FIX; intros.

  destruct PR as [PR | PR].
  - apply LE in PR. apply LEz in PR.
    eapply gf_mon. apply PR.
    intros. apply rclo7_base. apply PR0.
  - eapply gf_mon; [apply PR|]. clear x0 x1 x2 x3 x4 x5 x6 PR; intros.
    eapply rclo7_cpn.
    eapply cpn7_mon. apply PR. clear x0 x1 x2 x3 x4 x5 x6 PR; intros.
    destruct PR as [PR | PR].
    + apply rclo7_step. eapply gf_mon. apply LEz, PR.
      intros. apply rclo7_base, PR0.
    + apply rclo7_clo. split.
      * intros. apply rclo7_step.
        eapply gf_mon. apply LEz. apply PR0.
        intros. apply rclo7_base. apply PR1.
      * apply PR.
Qed.

Lemma fix7_le_cpn r rg (LE: r <7= rg) :
  cpn7 (fun x => wcpn7 r (rg \7/ x)) bot7 <7= cpn7 gf rg.
Proof.
  intros. eexists.
  - apply wcompat7_compat, cut7_wcomp. apply gf_mon. apply LE.
  - apply rclo7_clo. split.
    + intros. apply rclo7_base. apply PR0.
    + apply PR.
Qed.

Lemma fix7_le_wcpn r rg (LE: r <7= rg):
  cpn7 (fun x => wcpn7 r (rg \7/ x)) bot7 <7= wcpn7 r rg.
Proof.
  (*
    fix
    =
    c(r + gc(rg + fix))
    <=
    c(r + gc(rg + c(rg)))  (by Lemma fix7_le_cpn)
    <=
    c(r + gc(rg))
   *)
  
  intros. uunfold PR; [| apply wcpn7_inc_mon].
  destruct PR. constructor.
  eapply cpn7_mon. apply IN. intros.
  destruct PR. left; apply H. right.
  eapply gf_mon.  apply H. intros.
  ucpn.
  eapply cpn7_mon. apply PR. intros.
  destruct PR0.
  - ubase. apply H0.
  - eapply fix7_le_cpn. apply LE. apply H0.
Qed.

Lemma wcpn7_cofix: forall
    r rg (LE: r <7= rg)
    l (OBG: forall rr (INC: rg <7= rr) (CIH: l <7= rr), l <7= wcpn7 r rr),
  l <7= wcpn7 r rg.
Proof.
  intros. apply fix7_le_wcpn. apply LE.
  eapply cpn7_algebra, PR. apply wcpn7_inc_mon.
  intros. eapply OBG; intros.
  - left. apply PR1.
  - right. apply PR1.
  - apply PR0.
Qed.

End WCompanion7_main.

Lemma wcpn7_mon_bot (gf gf': rel -> rel) e0 e1 e2 e3 e4 e5 e6 r rg
      (IN: @wcpn7 gf bot7 bot7 e0 e1 e2 e3 e4 e5 e6)
      (MONgf: monotone7 gf)
      (MONgf': monotone7 gf')
      (LE: gf <8= gf'):
  @wcpn7 gf' r rg e0 e1 e2 e3 e4 e5 e6.
Proof.
  destruct IN. constructor.
  eapply cpn7_mon; [| intros; right; eapply PR].
  ubase.
  eapply gcpn7_mon_bot, LE; [|apply MONgf|apply MONgf'].
  eapply MONgf, cpn7_cpn; [| apply MONgf].
  eapply (compat7_compat (cpn7_compat MONgf)).
  eapply cpn7_mon. apply IN.
  intros. destruct PR. contradiction. apply H.
Qed.

End WCompanion7.

Hint Resolve wcpn7_base : paco.
Hint Resolve wcpn7_step : paco.

