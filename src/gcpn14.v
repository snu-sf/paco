Require Import paco14 cpn14 cpntac.
Set Implicit Arguments.

Section WCompanion14.

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

Local Notation rel := (rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13).

Section WCompanion14_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone14 gf.

Variable bnd: rel -> rel.
Hypothesis bnd_compat : compatible_bound14 gf bnd.

Inductive gcpn14 (r rg : rel) e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 : Prop :=
| gcpn14_intro (IN: cpn14 gf bnd (r \14/ fcpn14 gf bnd rg) e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13)
.              

Lemma gcpn14_mon r r' rg rg' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13
      (IN: @gcpn14 r rg e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13)
      (LEr: r <14= r')
      (LErg: rg <14= rg'):
  @gcpn14 r' rg' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13.
Proof.
  destruct IN. constructor.
  eapply cpn14_mon. apply IN. intros.
  destruct PR. left. apply LEr, H. right.
  eapply fcpn14_mon. apply gf_mon. apply H. apply LErg.
Qed.

Lemma gcpn14_init r: gcpn14 r r <14= cpn14 gf bnd r.
Proof.
  intros. destruct PR.
  ucpn.
  eapply cpn14_mon; [apply IN|].
  intros. destruct PR.
  - ubase. apply H.
  - ustep. apply H.
Qed.

Lemma gcpn14_final r rg: cpn14 gf bnd r <14= gcpn14 r rg.
Proof.
  constructor. eapply cpn14_mon. apply PR.
  intros. left. apply PR0.
Qed.

Lemma gcpn14_unfold:
  gcpn14 bot14 bot14 <14= gf (gcpn14 bot14 bot14).
Proof.
  intros. apply gcpn14_init in PR. uunfold PR.
  eapply gf_mon; [apply PR|].
  intros. apply gcpn14_final. apply PR0.
Qed.

Lemma gcpn14_base r rg:
  r <14= gcpn14 r rg.
Proof.
  intros. constructor. ubase. left. apply PR.
Qed.

Lemma gcpn14_bound r rg:
  bnd r <14= gcpn14 r rg.
Proof.
  intros. econstructor. apply cpn14_bound. apply bnd_compat.
  eapply cbound14_mon.
  - apply bnd_compat.
  - apply PR.
  - intros. left. apply PR0.
Qed.

Lemma gcpn14_step r rg:
  gf (gcpn14 rg rg) <14= gcpn14 r rg.
Proof.
  intros. constructor. ubase. right.
  eapply gf_mon. apply PR.
  intros. apply gcpn14_init. apply PR0.
Qed.

Lemma gcpn14_cpn r rg:
  cpn14 gf bnd (gcpn14 r rg) <14= gcpn14 r rg.
Proof.
  intros. constructor. ucpn.
  eapply cpn14_mon. apply PR.
  intros. destruct PR0. apply IN.
Qed.

Lemma gcpn14_clo r rg
      clo (LE: clo <15= cpn14 gf bnd):
  clo (gcpn14 r rg) <14= gcpn14 r rg.
Proof.
  intros. apply gcpn14_cpn, LE, PR.
Qed.

(*
  Fixpoint theorem of gcpn14
 *)

Definition gcut14 (x y z: rel) : rel := fun e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 => y <14= z /\ x e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13.

Definition gfixF14 (r rg z: rel) : rel := gcpn14 r (rg \14/ z).

Definition gfix14 (r rg: rel) : rel := cpn14 (gfixF14 r rg) bot15 bot14.

Lemma gfixF14_mon r rg:
  monotone14 (gfixF14 r rg).
Proof.
  red; intros.
  eapply gcpn14_mon. apply IN. intros. apply PR.
  intros. destruct PR. left. apply H. right. apply LE, H.
Qed.

Local Hint Resolve gfixF14_mon.

Lemma gcut14_mon x y : monotone14 (gcut14 x y).
Proof.
  repeat red. intros. destruct IN. split.
  - intros. apply LE, H, PR.
  - apply H0.
Qed.

Lemma gcut14_wcomp r rg (LE: r <14= rg) :
  wcompatible14 gf bnd (gcut14 (gfix14 r rg) rg).
Proof.
  econstructor; [apply gcut14_mon| |].
  { intros.
    destruct PR as [LEz FIX].
    uunfold FIX.
    eapply gf_mon, rclo14_cpn.
    apply cpn14_compat; [apply gf_mon|apply bnd_compat|].
    eapply cpn14_mon; [apply FIX|]. clear x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 FIX; intros.

    destruct PR as [PR | PR].
    - apply LE in PR. apply LEz in PR.
      eapply gf_mon. apply PR.
      intros. apply rclo14_base. apply PR0.
    - eapply gf_mon; [apply PR|]. clear x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 PR; intros.
      eapply rclo14_cpn.
      eapply cpn14_mon. apply PR. clear x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 PR; intros.
      destruct PR as [PR | PR].
      + apply rclo14_step. eapply gf_mon. apply LEz, PR.
        intros. apply rclo14_base, PR0.
      + apply rclo14_clo. split.
        * intros. apply rclo14_step.
          eapply gf_mon. apply LEz. apply PR0.
          intros. apply rclo14_base. apply PR1.
        * apply PR.
  }
  { intros. apply (cbound14_distr bnd_compat) in PR.
    destruct PR, IN.
    uunfold H0. destruct H0. specialize (PTW _ IN).
    eapply (compat14_bound (cpn14_compat gf_mon bnd_compat)) in PTW.
    destruct PTW as [BND|BND].
    - apply (cbound14_distr bnd_compat) in BND. destruct BND.
      destruct IN0.
      + left. apply PTW, H, LE, H0.
      + specialize (PTW _ H0).
        apply (cbound14_compat bnd_compat) in PTW.
        right. eapply gf_mon. apply PTW.
        intros. apply rclo14_cpn, cpn14_bound; [apply bnd_compat|].
        eapply cbound14_mon. apply bnd_compat. apply PR.
        intros. apply rclo14_cpn.
        eapply cpn14_mon. apply PR0.
        intros. destruct PR1.
        * apply rclo14_base. apply H, H1.
        * apply rclo14_clo. econstructor; [|apply H1].
          intros. apply rclo14_base. apply H, PR1.
    - right. eapply gf_mon. apply BND.
      intros. apply rclo14_cpn.
      eapply cpn14_mon. apply PR.
      intros. destruct PR0.
      + apply rclo14_base. apply H, LE, H0.
      + apply rclo14_step.
        eapply gf_mon. apply H0.
        intros. apply rclo14_cpn.
        eapply cpn14_mon. apply PR0.
        intros. destruct PR1.
        * apply rclo14_base. apply H, H1.
        * apply rclo14_clo. econstructor; [|apply H1].
          intros. apply rclo14_base. apply H, PR1.
  }
Qed.

Lemma gfix14_le_cpn r rg (LE: r <14= rg) :
  gfix14 r rg <14= cpn14 gf bnd rg.
Proof.
  intros. eexists.
  - apply wcompat14_compat, gcut14_wcomp. apply gf_mon. apply bnd_compat. apply LE.
  - apply rclo14_clo. split.
    + intros. apply rclo14_base. apply PR0.
    + apply PR.
Qed.

Lemma gfix14_le_gcpn r rg (LE: r <14= rg):
  gfix14 r rg <14= gcpn14 r rg.
Proof.
  (*
    fix
    =
    c(r + gc(rg + fix))
    <=
    c(r + gc(rg + c(rg)))  (by Lemma fix14_le_cpn)
    <=
    c(r + gc(rg))
   *)
  
  intros. uunfold PR.
  destruct PR. constructor.
  eapply cpn14_mon. apply IN. intros.
  destruct PR. left; apply H. right.
  eapply gf_mon.  apply H. intros.
  ucpn.
  eapply cpn14_mon. apply PR. intros.
  destruct PR0.
  - ubase. apply H0.
  - eapply gfix14_le_cpn. apply LE. apply H0.
Qed.

Lemma gcpn14_cofix: forall
    r rg (LE: r <14= rg)
    l (OBG: forall rr (INC: rg <14= rr) (CIH: l <14= rr), l <14= gcpn14 r rr),
  l <14= gcpn14 r rg.
Proof.
  intros. apply gfix14_le_gcpn. apply LE.
  eapply cpn14_algebra, PR. apply gfixF14_mon. apply cbound14_bot.
  intros. eapply OBG; intros.
  - left. apply PR1.
  - right. apply PR1.
  - apply PR0.
Qed.

End WCompanion14_main.

Lemma gcpn14_mon_bot bnd bnd' (gf gf': rel -> rel) e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 r rg
      (IN: @gcpn14 gf bnd bot14 bot14 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13)
      (MON: monotone14 gf)
      (MON': monotone14 gf')
      (BASE: compatible_bound14 gf bnd)
      (BASE': compatible_bound14 gf' bnd')
      (LE: gf <15= gf'):
  @gcpn14 gf' bnd' r rg e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13.
Proof.
  destruct IN. constructor.
  eapply cpn14_mon; [| intros; right; eapply PR].
  ubase.
  eapply fcpn14_mon_bot, LE; [|apply MON|apply MON'|apply BASE|apply BASE'].
  eapply MON, cpn14_cpn; [|apply MON|apply BASE].
  eapply (compat14_compat (cpn14_compat MON BASE)).
  eapply cpn14_mon. apply IN.
  intros. destruct PR. contradiction. apply H.
Qed.

End WCompanion14.

Hint Resolve gcpn14_base : paco.
Hint Resolve gcpn14_step : paco.

