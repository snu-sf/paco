Require Import paco12 pcpn12 pcpntac.
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

Variable bnd: rel -> rel.
Hypothesis bnd_compat : compatible_bound12 gf bnd.

Inductive gcpn12 (r rg : rel) e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 : Prop :=
| gcpn12_intro (IN: cpn12 gf bnd (r \12/ fcpn12 gf bnd rg) e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11)
.              

Lemma gcpn12_mon r r' rg rg' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11
      (IN: @gcpn12 r rg e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11)
      (LEr: r <12= r')
      (LErg: rg <12= rg'):
  @gcpn12 r' rg' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.
Proof.
  destruct IN. constructor.
  eapply cpn12_mon. apply IN. intros.
  destruct PR. left. apply LEr, H. right.
  eapply fcpn12_mon. apply gf_mon. apply H. apply LErg.
Qed.

Lemma gcpn12_init r: gcpn12 r r <12= cpn12 gf bnd r.
Proof.
  intros. destruct PR.
  ucpn.
  eapply cpn12_mon; [apply IN|].
  intros. destruct PR.
  - ubase. apply H.
  - ustep. apply H.
Qed.

Lemma gcpn12_final r rg: cpn12 gf bnd r <12= gcpn12 r rg.
Proof.
  constructor. eapply cpn12_mon. apply PR.
  intros. left. apply PR0.
Qed.

Lemma gcpn12_unfold:
  gcpn12 bot12 bot12 <12= gf (gcpn12 bot12 bot12).
Proof.
  intros. apply gcpn12_init in PR. uunfold PR.
  eapply gf_mon; [apply PR|].
  intros. apply gcpn12_final. apply PR0.
Qed.

Lemma gcpn12_base r rg:
  r <12= gcpn12 r rg.
Proof.
  intros. constructor. ubase. left. apply PR.
Qed.

Lemma gcpn12_bound r rg:
  bnd r <12= gcpn12 r rg.
Proof.
  intros. econstructor. apply cpn12_bound. apply bnd_compat.
  eapply cbound12_mon.
  - apply bnd_compat.
  - apply PR.
  - intros. left. apply PR0.
Qed.

Lemma gcpn12_step r rg:
  gf (gcpn12 rg rg) <12= gcpn12 r rg.
Proof.
  intros. constructor. ubase. right.
  eapply gf_mon. apply PR.
  intros. apply gcpn12_init. apply PR0.
Qed.

Lemma gcpn12_cpn r rg:
  cpn12 gf bnd (gcpn12 r rg) <12= gcpn12 r rg.
Proof.
  intros. constructor. ucpn.
  eapply cpn12_mon. apply PR.
  intros. destruct PR0. apply IN.
Qed.

Lemma gcpn12_clo r rg
      clo (LE: clo <13= cpn12 gf bnd):
  clo (gcpn12 r rg) <12= gcpn12 r rg.
Proof.
  intros. apply gcpn12_cpn, LE, PR.
Qed.

(*
  Fixpoint theorem of gcpn12
 *)

Definition gcut12 (x y z: rel) : rel := fun e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 => y <12= z /\ x e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.

Definition gfixF12 (r rg z: rel) : rel := gcpn12 r (rg \12/ z).

Definition gfix12 (r rg: rel) : rel := cpn12 (gfixF12 r rg) bot13 bot12.

Lemma gfixF12_mon r rg:
  monotone12 (gfixF12 r rg).
Proof.
  red; intros.
  eapply gcpn12_mon. apply IN. intros. apply PR.
  intros. destruct PR. left. apply H. right. apply LE, H.
Qed.

Local Hint Resolve gfixF12_mon.

Lemma gcut12_mon x y : monotone12 (gcut12 x y).
Proof.
  repeat red. intros. destruct IN. split.
  - intros. apply LE, H, PR.
  - apply H0.
Qed.

Lemma gcut12_wcomp r rg (LE: r <12= rg) :
  wcompatible12 gf bnd (gcut12 (gfix12 r rg) rg).
Proof.
  econstructor; [apply gcut12_mon| |].
  { intros.
    destruct PR as [LEz FIX].
    uunfold FIX.
    eapply gf_mon, rclo12_cpn.
    apply cpn12_compat; [apply gf_mon|apply bnd_compat|].
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
  }
  { intros. apply (cbound12_distr bnd_compat) in PR.
    destruct PR, IN.
    uunfold H0. destruct H0. specialize (PTW _ IN).
    eapply (compat12_bound (cpn12_compat gf_mon bnd_compat)) in PTW.
    destruct PTW as [BND|BND].
    - apply (cbound12_distr bnd_compat) in BND. destruct BND.
      destruct IN0.
      + left. apply PTW, H, LE, H0.
      + specialize (PTW _ H0).
        apply (cbound12_compat bnd_compat) in PTW.
        right. eapply gf_mon. apply PTW.
        intros. apply rclo12_cpn, cpn12_bound; [apply bnd_compat|].
        eapply cbound12_mon. apply bnd_compat. apply PR.
        intros. apply rclo12_cpn.
        eapply cpn12_mon. apply PR0.
        intros. destruct PR1.
        * apply rclo12_base. apply H, H1.
        * apply rclo12_clo. econstructor; [|apply H1].
          intros. apply rclo12_base. apply H, PR1.
    - right. eapply gf_mon. apply BND.
      intros. apply rclo12_cpn.
      eapply cpn12_mon. apply PR.
      intros. destruct PR0.
      + apply rclo12_base. apply H, LE, H0.
      + apply rclo12_step.
        eapply gf_mon. apply H0.
        intros. apply rclo12_cpn.
        eapply cpn12_mon. apply PR0.
        intros. destruct PR1.
        * apply rclo12_base. apply H, H1.
        * apply rclo12_clo. econstructor; [|apply H1].
          intros. apply rclo12_base. apply H, PR1.
  }
Qed.

Lemma gfix12_le_cpn r rg (LE: r <12= rg) :
  gfix12 r rg <12= cpn12 gf bnd rg.
Proof.
  intros. eexists.
  - apply wcompat12_compat, gcut12_wcomp. apply gf_mon. apply bnd_compat. apply LE.
  - apply rclo12_clo. split.
    + intros. apply rclo12_base. apply PR0.
    + apply PR.
Qed.

Lemma gfix12_le_gcpn r rg (LE: r <12= rg):
  gfix12 r rg <12= gcpn12 r rg.
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
  
  intros. uunfold PR.
  destruct PR. constructor.
  eapply cpn12_mon. apply IN. intros.
  destruct PR. left; apply H. right.
  eapply gf_mon.  apply H. intros.
  ucpn.
  eapply cpn12_mon. apply PR. intros.
  destruct PR0.
  - ubase. apply H0.
  - eapply gfix12_le_cpn. apply LE. apply H0.
Qed.

Lemma gcpn12_cofix: forall
    r rg (LE: r <12= rg)
    l (OBG: forall rr (INC: rg <12= rr) (CIH: l <12= rr), l <12= gcpn12 r rr),
  l <12= gcpn12 r rg.
Proof.
  intros. apply gfix12_le_gcpn. apply LE.
  eapply cpn12_algebra, PR. apply gfixF12_mon. apply cbound12_bot.
  intros. eapply OBG; intros.
  - left. apply PR1.
  - right. apply PR1.
  - apply PR0.
Qed.

End WCompanion12_main.

Lemma gcpn12_mon_bot bnd bnd' (gf gf': rel -> rel) e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 r rg
      (IN: @gcpn12 gf bnd bot12 bot12 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11)
      (MON: monotone12 gf)
      (MON': monotone12 gf')
      (BASE: compatible_bound12 gf bnd)
      (BASE': compatible_bound12 gf' bnd')
      (LE: gf <13= gf'):
  @gcpn12 gf' bnd' r rg e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.
Proof.
  destruct IN. constructor.
  eapply cpn12_mon; [| intros; right; eapply PR].
  ubase.
  eapply fcpn12_mon_bot, LE; [|apply MON|apply MON'|apply BASE|apply BASE'].
  eapply MON, cpn12_cpn; [|apply MON|apply BASE].
  eapply (compat12_compat (cpn12_compat MON BASE)).
  eapply cpn12_mon. apply IN.
  intros. destruct PR. contradiction. apply H.
Qed.

End WCompanion12.

Hint Resolve gcpn12_base : paco.
Hint Resolve gcpn12_step : paco.

