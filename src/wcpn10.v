Require Import paco10 cpn10 cpntac.
Set Implicit Arguments.

Section WCompanion10.

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

Local Notation rel := (rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9).

Section WCompanion10_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone10 gf.

Inductive wcpn10 (r rg : rel) e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 : Prop :=
| wcpn10_intro (IN: cpn10 gf (r \10/ gcpn10 gf rg) e0 e1 e2 e3 e4 e5 e6 e7 e8 e9)
.              
Hint Constructors wcpn10.

Lemma wcpn10_mon r r' rg rg' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9
      (IN: @wcpn10 r rg e0 e1 e2 e3 e4 e5 e6 e7 e8 e9)
      (LEr: r <10= r')
      (LErg: rg <10= rg'):
  @wcpn10 r' rg' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9.
Proof.
  destruct IN. constructor.
  eapply cpn10_mon. apply IN. intros.
  destruct PR. left. apply LEr, H. right.
  eapply gcpn10_mon. apply gf_mon. apply H. apply LErg.
Qed.

Lemma wcpn10_inc_mon r rg:
  monotone10 (fun x : rel => wcpn10 r (rg \10/ x)).
Proof.
  red; intros.
  eapply wcpn10_mon. apply IN. intros. apply PR.
  intros. destruct PR. left. apply H. right. apply LE, H. 
Qed.

Lemma wcpn10_init r: wcpn10 r r <10= cpn10 gf r.
Proof.
  intros. destruct PR.
  ucpn.
  eapply cpn10_mon; [apply IN|].
  intros. destruct PR.
  - ubase. apply H.
  - ustep. apply H.
Qed.

Lemma wcpn10_final r rg: cpn10 gf r <10= wcpn10 r rg.
Proof.
  constructor. eapply cpn10_mon. apply PR.
  intros. left. apply PR0.
Qed.

Lemma wcpn10_base r rg:
  r <10= wcpn10 r rg.
Proof.
  intros. constructor. ubase. left. apply PR.
Qed.

Lemma wcpn10_step r rg:
  gf (wcpn10 rg rg) <10= wcpn10 r rg.
Proof.
  intros. constructor. ubase. right.
  eapply gf_mon. apply PR.
  intros. apply wcpn10_init. apply PR0.
Qed.

Lemma wcpn10_cpn r rg:
  cpn10 gf (wcpn10 r rg) <10= wcpn10 r rg.
Proof.
  intros. constructor. ucpn.
  eapply cpn10_mon. apply PR.
  intros. destruct PR0. apply IN.
Qed.

Lemma wcpn10_clo r rg
      clo (LE: clo <11= cpn10 gf):
  clo (wcpn10 r rg) <10= wcpn10 r rg.
Proof.
  intros. apply wcpn10_cpn, LE, PR.
Qed.

Definition cut10 (x y z: rel) : rel := fun e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 => y <10= z /\ x e0 e1 e2 e3 e4 e5 e6 e7 e8 e9.

Lemma cut10_mon x y : monotone10 (cut10 x y).
Proof.
  repeat red. intros. destruct IN. split.
  - intros. apply LE, H, PR.
  - apply H0.
Qed.

Lemma cut10_wcomp r rg (LE: r <10= rg) :
  wcompatible10 gf (cut10 (cpn10 (fun x => wcpn10 r (rg \10/ x)) bot10) rg).
Proof.
  set (pfix := cpn10 (fun x => wcpn10 r (rg \10/ x)) bot10).
  
  econstructor; [apply cut10_mon|]. intros.
  destruct PR as [LEz FIX].
  uunfold FIX; [|apply wcpn10_inc_mon].
  eapply gf_mon, rclo10_cpn.
  apply cpn10_compat; [apply gf_mon|].
  eapply cpn10_mon; [apply FIX|]. clear x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 FIX; intros.

  destruct PR as [PR | PR].
  - apply LE in PR. apply LEz in PR.
    eapply gf_mon. apply PR.
    intros. apply rclo10_base. apply PR0.
  - eapply gf_mon; [apply PR|]. clear x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 PR; intros.
    eapply rclo10_cpn.
    eapply cpn10_mon. apply PR. clear x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 PR; intros.
    destruct PR as [PR | PR].
    + apply rclo10_step. eapply gf_mon. apply LEz, PR.
      intros. apply rclo10_base, PR0.
    + apply rclo10_clo. split.
      * intros. apply rclo10_step.
        eapply gf_mon. apply LEz. apply PR0.
        intros. apply rclo10_base. apply PR1.
      * apply PR.
Qed.

Lemma fix10_le_cpn r rg (LE: r <10= rg) :
  cpn10 (fun x => wcpn10 r (rg \10/ x)) bot10 <10= cpn10 gf rg.
Proof.
  intros. eexists.
  - apply wcompat10_compat, cut10_wcomp. apply gf_mon. apply LE.
  - apply rclo10_clo. split.
    + intros. apply rclo10_base. apply PR0.
    + apply PR.
Qed.

Lemma fix10_le_wcpn r rg (LE: r <10= rg):
  cpn10 (fun x => wcpn10 r (rg \10/ x)) bot10 <10= wcpn10 r rg.
Proof.
  (*
    fix
    =
    c(r + gc(rg + fix))
    <=
    c(r + gc(rg + c(rg)))  (by Lemma fix10_le_cpn)
    <=
    c(r + gc(rg))
   *)
  
  intros. uunfold PR; [| apply wcpn10_inc_mon].
  destruct PR. constructor.
  eapply cpn10_mon. apply IN. intros.
  destruct PR. left; apply H. right.
  eapply gf_mon.  apply H. intros.
  ucpn.
  eapply cpn10_mon. apply PR. intros.
  destruct PR0.
  - ubase. apply H0.
  - eapply fix10_le_cpn. apply LE. apply H0.
Qed.

Lemma wcpn10_cofix: forall
    r rg (LE: r <10= rg)
    l (OBG: forall rr (INC: rg <10= rr) (CIH: l <10= rr), l <10= wcpn10 r rr),
  l <10= wcpn10 r rg.
Proof.
  intros. apply fix10_le_wcpn. apply LE.
  eapply cpn10_algebra, PR. apply wcpn10_inc_mon.
  intros. eapply OBG; intros.
  - left. apply PR1.
  - right. apply PR1.
  - apply PR0.
Qed.

End WCompanion10_main.

Lemma wcpn10_mon_bot (gf gf': rel -> rel) e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 r rg
      (IN: @wcpn10 gf bot10 bot10 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9)
      (MONgf: monotone10 gf)
      (MONgf': monotone10 gf')
      (LE: gf <11= gf'):
  @wcpn10 gf' r rg e0 e1 e2 e3 e4 e5 e6 e7 e8 e9.
Proof.
  destruct IN. constructor.
  eapply cpn10_mon; [| intros; right; eapply PR].
  ubase.
  eapply gcpn10_mon_bot, LE; [|apply MONgf|apply MONgf'].
  eapply MONgf, cpn10_cpn; [| apply MONgf].
  eapply (compat10_compat (cpn10_compat MONgf)).
  eapply cpn10_mon. apply IN.
  intros. destruct PR. contradiction. apply H.
Qed.

End WCompanion10.

Hint Constructors wcpn10 : paco.

Hint Resolve wcpn10_base : paco.
Hint Resolve wcpn10_step : paco.
Hint Resolve wcpn10_final : paco.

