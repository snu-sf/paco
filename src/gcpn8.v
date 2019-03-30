Require Import paco8 cpn8 cpntac.
Set Implicit Arguments.

Section WCompanion8.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
Variable T7 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5), Type.

Local Notation rel := (rel8 T0 T1 T2 T3 T4 T5 T6 T7).

Section WCompanion8_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone8 gf.

Inductive gcpn8 (r rg : rel) e0 e1 e2 e3 e4 e5 e6 e7 : Prop :=
| gcpn8_intro (IN: cpn8 gf (r \8/ fcpn8 gf rg) e0 e1 e2 e3 e4 e5 e6 e7)
.              

Lemma gcpn8_mon r r' rg rg' e0 e1 e2 e3 e4 e5 e6 e7
      (IN: @gcpn8 r rg e0 e1 e2 e3 e4 e5 e6 e7)
      (LEr: r <8= r')
      (LErg: rg <8= rg'):
  @gcpn8 r' rg' e0 e1 e2 e3 e4 e5 e6 e7.
Proof.
  destruct IN. constructor.
  eapply cpn8_mon. apply IN. intros.
  destruct PR. left. apply LEr, H. right.
  eapply fcpn8_mon. apply gf_mon. apply H. apply LErg.
Qed.

Lemma gcpn8_inc_mon r rg:
  monotone8 (fun x : rel => gcpn8 r (rg \8/ x)).
Proof.
  red; intros.
  eapply gcpn8_mon. apply IN. intros. apply PR.
  intros. destruct PR. left. apply H. right. apply LE, H. 
Qed.

Lemma gcpn8_init r: gcpn8 r r <8= cpn8 gf r.
Proof.
  intros. destruct PR.
  ucpn.
  eapply cpn8_mon; [apply IN|].
  intros. destruct PR.
  - ubase. apply H.
  - ustep. apply H.
Qed.

Lemma gcpn8_final r rg: cpn8 gf r <8= gcpn8 r rg.
Proof.
  constructor. eapply cpn8_mon. apply PR.
  intros. left. apply PR0.
Qed.

Lemma gcpn8_unfold:
  gcpn8 bot8 bot8 <8= gf (gcpn8 bot8 bot8).
Proof.
  intros. apply gcpn8_init in PR. uunfold PR.
  eapply gf_mon; [apply PR|].
  intros. apply gcpn8_final. apply PR0.
Qed.

Lemma gcpn8_base r rg:
  r <8= gcpn8 r rg.
Proof.
  intros. constructor. ubase. left. apply PR.
Qed.

Lemma gcpn8_step r rg:
  gf (gcpn8 rg rg) <8= gcpn8 r rg.
Proof.
  intros. constructor. ubase. right.
  eapply gf_mon. apply PR.
  intros. apply gcpn8_init. apply PR0.
Qed.

Lemma gcpn8_cpn r rg:
  cpn8 gf (gcpn8 r rg) <8= gcpn8 r rg.
Proof.
  intros. constructor. ucpn.
  eapply cpn8_mon. apply PR.
  intros. destruct PR0. apply IN.
Qed.

Lemma gcpn8_clo r rg
      clo (LE: clo <9= cpn8 gf):
  clo (gcpn8 r rg) <8= gcpn8 r rg.
Proof.
  intros. apply gcpn8_cpn, LE, PR.
Qed.

Definition cut8 (x y z: rel) : rel := fun e0 e1 e2 e3 e4 e5 e6 e7 => y <8= z /\ x e0 e1 e2 e3 e4 e5 e6 e7.

Lemma cut8_mon x y : monotone8 (cut8 x y).
Proof.
  repeat red. intros. destruct IN. split.
  - intros. apply LE, H, PR.
  - apply H0.
Qed.

Lemma cut8_wcomp r rg (LE: r <8= rg) :
  wcompatible8 gf (cut8 (cpn8 (fun x => gcpn8 r (rg \8/ x)) bot8) rg).
Proof.
  set (pfix := cpn8 (fun x => gcpn8 r (rg \8/ x)) bot8).
  
  econstructor; [apply cut8_mon|]. intros.
  destruct PR as [LEz FIX].
  uunfold FIX; [|apply gcpn8_inc_mon].
  eapply gf_mon, rclo8_cpn.
  apply cpn8_compat; [apply gf_mon|].
  eapply cpn8_mon; [apply FIX|]. clear x0 x1 x2 x3 x4 x5 x6 x7 FIX; intros.

  destruct PR as [PR | PR].
  - apply LE in PR. apply LEz in PR.
    eapply gf_mon. apply PR.
    intros. apply rclo8_base. apply PR0.
  - eapply gf_mon; [apply PR|]. clear x0 x1 x2 x3 x4 x5 x6 x7 PR; intros.
    eapply rclo8_cpn.
    eapply cpn8_mon. apply PR. clear x0 x1 x2 x3 x4 x5 x6 x7 PR; intros.
    destruct PR as [PR | PR].
    + apply rclo8_step. eapply gf_mon. apply LEz, PR.
      intros. apply rclo8_base, PR0.
    + apply rclo8_clo. split.
      * intros. apply rclo8_step.
        eapply gf_mon. apply LEz. apply PR0.
        intros. apply rclo8_base. apply PR1.
      * apply PR.
Qed.

Lemma fix8_le_cpn r rg (LE: r <8= rg) :
  cpn8 (fun x => gcpn8 r (rg \8/ x)) bot8 <8= cpn8 gf rg.
Proof.
  intros. eexists.
  - apply wcompat8_compat, cut8_wcomp. apply gf_mon. apply LE.
  - apply rclo8_clo. split.
    + intros. apply rclo8_base. apply PR0.
    + apply PR.
Qed.

Lemma fix8_le_gcpn r rg (LE: r <8= rg):
  cpn8 (fun x => gcpn8 r (rg \8/ x)) bot8 <8= gcpn8 r rg.
Proof.
  (*
    fix
    =
    c(r + gc(rg + fix))
    <=
    c(r + gc(rg + c(rg)))  (by Lemma fix8_le_cpn)
    <=
    c(r + gc(rg))
   *)
  
  intros. uunfold PR; [| apply gcpn8_inc_mon].
  destruct PR. constructor.
  eapply cpn8_mon. apply IN. intros.
  destruct PR. left; apply H. right.
  eapply gf_mon.  apply H. intros.
  ucpn.
  eapply cpn8_mon. apply PR. intros.
  destruct PR0.
  - ubase. apply H0.
  - eapply fix8_le_cpn. apply LE. apply H0.
Qed.

Lemma gcpn8_cofix: forall
    r rg (LE: r <8= rg)
    l (OBG: forall rr (INC: rg <8= rr) (CIH: l <8= rr), l <8= gcpn8 r rr),
  l <8= gcpn8 r rg.
Proof.
  intros. apply fix8_le_gcpn. apply LE.
  eapply cpn8_algebra, PR. apply gcpn8_inc_mon.
  intros. eapply OBG; intros.
  - left. apply PR1.
  - right. apply PR1.
  - apply PR0.
Qed.

End WCompanion8_main.

Lemma gcpn8_mon_bot (gf gf': rel -> rel) e0 e1 e2 e3 e4 e5 e6 e7 r rg
      (IN: @gcpn8 gf bot8 bot8 e0 e1 e2 e3 e4 e5 e6 e7)
      (MONgf: monotone8 gf)
      (MONgf': monotone8 gf')
      (LE: gf <9= gf'):
  @gcpn8 gf' r rg e0 e1 e2 e3 e4 e5 e6 e7.
Proof.
  destruct IN. constructor.
  eapply cpn8_mon; [| intros; right; eapply PR].
  ubase.
  eapply fcpn8_mon_bot, LE; [|apply MONgf|apply MONgf'].
  eapply MONgf, cpn8_cpn; [| apply MONgf].
  eapply (compat8_compat (cpn8_compat MONgf)).
  eapply cpn8_mon. apply IN.
  intros. destruct PR. contradiction. apply H.
Qed.

End WCompanion8.

Hint Resolve gcpn8_base : paco.
Hint Resolve gcpn8_step : paco.

