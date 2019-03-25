Require Import paco9 cpn9 cpntac.
Set Implicit Arguments.

Section WCompanion9.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
Variable T7 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5), Type.
Variable T8 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6), Type.

Local Notation rel := (rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8).

Section WCompanion9_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone9 gf.

Inductive gcpn9 (r rg : rel) e0 e1 e2 e3 e4 e5 e6 e7 e8 : Prop :=
| gcpn9_intro (IN: cpn9 gf (r \9/ fcpn9 gf rg) e0 e1 e2 e3 e4 e5 e6 e7 e8)
.              

Lemma gcpn9_mon r r' rg rg' e0 e1 e2 e3 e4 e5 e6 e7 e8
      (IN: @gcpn9 r rg e0 e1 e2 e3 e4 e5 e6 e7 e8)
      (LEr: r <9= r')
      (LErg: rg <9= rg'):
  @gcpn9 r' rg' e0 e1 e2 e3 e4 e5 e6 e7 e8.
Proof.
  destruct IN. constructor.
  eapply cpn9_mon. apply IN. intros.
  destruct PR. left. apply LEr, H. right.
  eapply fcpn9_mon. apply gf_mon. apply H. apply LErg.
Qed.

Lemma gcpn9_inc_mon r rg:
  monotone9 (fun x : rel => gcpn9 r (rg \9/ x)).
Proof.
  red; intros.
  eapply gcpn9_mon. apply IN. intros. apply PR.
  intros. destruct PR. left. apply H. right. apply LE, H. 
Qed.

Lemma gcpn9_init r: gcpn9 r r <9= cpn9 gf r.
Proof.
  intros. destruct PR.
  ucpn.
  eapply cpn9_mon; [apply IN|].
  intros. destruct PR.
  - ubase. apply H.
  - ustep. apply H.
Qed.

Lemma gcpn9_final r rg: cpn9 gf r <9= gcpn9 r rg.
Proof.
  constructor. eapply cpn9_mon. apply PR.
  intros. left. apply PR0.
Qed.

Lemma gcpn9_unfold:
  gcpn9 bot9 bot9 <9= gf (gcpn9 bot9 bot9).
Proof.
  intros. apply gcpn9_init in PR. uunfold PR.
  eapply gf_mon; [apply PR|].
  intros. apply gcpn9_final. apply PR0.
Qed.

Lemma gcpn9_base r rg:
  r <9= gcpn9 r rg.
Proof.
  intros. constructor. ubase. left. apply PR.
Qed.

Lemma gcpn9_step r rg:
  gf (gcpn9 rg rg) <9= gcpn9 r rg.
Proof.
  intros. constructor. ubase. right.
  eapply gf_mon. apply PR.
  intros. apply gcpn9_init. apply PR0.
Qed.

Lemma gcpn9_cpn r rg:
  cpn9 gf (gcpn9 r rg) <9= gcpn9 r rg.
Proof.
  intros. constructor. ucpn.
  eapply cpn9_mon. apply PR.
  intros. destruct PR0. apply IN.
Qed.

Lemma gcpn9_clo r rg
      clo (LE: clo <10= cpn9 gf):
  clo (gcpn9 r rg) <9= gcpn9 r rg.
Proof.
  intros. apply gcpn9_cpn, LE, PR.
Qed.

Definition cut9 (x y z: rel) : rel := fun e0 e1 e2 e3 e4 e5 e6 e7 e8 => y <9= z /\ x e0 e1 e2 e3 e4 e5 e6 e7 e8.

Lemma cut9_mon x y : monotone9 (cut9 x y).
Proof.
  repeat red. intros. destruct IN. split.
  - intros. apply LE, H, PR.
  - apply H0.
Qed.

Lemma cut9_wcomp r rg (LE: r <9= rg) :
  wcompatible9 gf (cut9 (cpn9 (fun x => gcpn9 r (rg \9/ x)) bot9) rg).
Proof.
  set (pfix := cpn9 (fun x => gcpn9 r (rg \9/ x)) bot9).
  
  econstructor; [apply cut9_mon|]. intros.
  destruct PR as [LEz FIX].
  uunfold FIX; [|apply gcpn9_inc_mon].
  eapply gf_mon, rclo9_cpn.
  apply cpn9_compat; [apply gf_mon|].
  eapply cpn9_mon; [apply FIX|]. clear x0 x1 x2 x3 x4 x5 x6 x7 x8 FIX; intros.

  destruct PR as [PR | PR].
  - apply LE in PR. apply LEz in PR.
    eapply gf_mon. apply PR.
    intros. apply rclo9_base. apply PR0.
  - eapply gf_mon; [apply PR|]. clear x0 x1 x2 x3 x4 x5 x6 x7 x8 PR; intros.
    eapply rclo9_cpn.
    eapply cpn9_mon. apply PR. clear x0 x1 x2 x3 x4 x5 x6 x7 x8 PR; intros.
    destruct PR as [PR | PR].
    + apply rclo9_step. eapply gf_mon. apply LEz, PR.
      intros. apply rclo9_base, PR0.
    + apply rclo9_clo. split.
      * intros. apply rclo9_step.
        eapply gf_mon. apply LEz. apply PR0.
        intros. apply rclo9_base. apply PR1.
      * apply PR.
Qed.

Lemma fix9_le_cpn r rg (LE: r <9= rg) :
  cpn9 (fun x => gcpn9 r (rg \9/ x)) bot9 <9= cpn9 gf rg.
Proof.
  intros. eexists.
  - apply wcompat9_compat, cut9_wcomp. apply gf_mon. apply LE.
  - apply rclo9_clo. split.
    + intros. apply rclo9_base. apply PR0.
    + apply PR.
Qed.

Lemma fix9_le_gcpn r rg (LE: r <9= rg):
  cpn9 (fun x => gcpn9 r (rg \9/ x)) bot9 <9= gcpn9 r rg.
Proof.
  (*
    fix
    =
    c(r + gc(rg + fix))
    <=
    c(r + gc(rg + c(rg)))  (by Lemma fix9_le_cpn)
    <=
    c(r + gc(rg))
   *)
  
  intros. uunfold PR; [| apply gcpn9_inc_mon].
  destruct PR. constructor.
  eapply cpn9_mon. apply IN. intros.
  destruct PR. left; apply H. right.
  eapply gf_mon.  apply H. intros.
  ucpn.
  eapply cpn9_mon. apply PR. intros.
  destruct PR0.
  - ubase. apply H0.
  - eapply fix9_le_cpn. apply LE. apply H0.
Qed.

Lemma gcpn9_cofix: forall
    r rg (LE: r <9= rg)
    l (OBG: forall rr (INC: rg <9= rr) (CIH: l <9= rr), l <9= gcpn9 r rr),
  l <9= gcpn9 r rg.
Proof.
  intros. apply fix9_le_gcpn. apply LE.
  eapply cpn9_algebra, PR. apply gcpn9_inc_mon.
  intros. eapply OBG; intros.
  - left. apply PR1.
  - right. apply PR1.
  - apply PR0.
Qed.

End WCompanion9_main.

Lemma gcpn9_mon_bot (gf gf': rel -> rel) e0 e1 e2 e3 e4 e5 e6 e7 e8 r rg
      (IN: @gcpn9 gf bot9 bot9 e0 e1 e2 e3 e4 e5 e6 e7 e8)
      (MONgf: monotone9 gf)
      (MONgf': monotone9 gf')
      (LE: gf <10= gf'):
  @gcpn9 gf' r rg e0 e1 e2 e3 e4 e5 e6 e7 e8.
Proof.
  destruct IN. constructor.
  eapply cpn9_mon; [| intros; right; eapply PR].
  ubase.
  eapply fcpn9_mon_bot, LE; [|apply MONgf|apply MONgf'].
  eapply MONgf, cpn9_cpn; [| apply MONgf].
  eapply (compat9_compat (cpn9_compat MONgf)).
  eapply cpn9_mon. apply IN.
  intros. destruct PR. contradiction. apply H.
Qed.

End WCompanion9.

Hint Resolve gcpn9_base : paco.
Hint Resolve gcpn9_step : paco.

