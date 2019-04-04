Require Import paco10 pcpn10 pcpntac.
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

Variable bnd: rel -> rel.
Hypothesis bnd_compat : compatible_bound10 gf bnd.

Inductive gcpn10 (r rg : rel) e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 : Prop :=
| gcpn10_intro (IN: cpn10 gf bnd (r \10/ fcpn10 gf bnd rg) e0 e1 e2 e3 e4 e5 e6 e7 e8 e9)
.              

Lemma gcpn10_mon r r' rg rg' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9
      (IN: @gcpn10 r rg e0 e1 e2 e3 e4 e5 e6 e7 e8 e9)
      (LEr: r <10= r')
      (LErg: rg <10= rg'):
  @gcpn10 r' rg' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9.
Proof.
  destruct IN. constructor.
  eapply cpn10_mon. apply IN. intros.
  destruct PR. left. apply LEr, H. right.
  eapply fcpn10_mon. apply gf_mon. apply H. apply LErg.
Qed.

Lemma gcpn10_init r: gcpn10 r r <10= cpn10 gf bnd r.
Proof.
  intros. destruct PR.
  ucpn.
  eapply cpn10_mon; [apply IN|].
  intros. destruct PR.
  - ubase. apply H.
  - ustep. apply H.
Qed.

Lemma gcpn10_final r rg: cpn10 gf bnd r <10= gcpn10 r rg.
Proof.
  constructor. eapply cpn10_mon. apply PR.
  intros. left. apply PR0.
Qed.

Lemma gcpn10_unfold:
  gcpn10 bot10 bot10 <10= gf (gcpn10 bot10 bot10).
Proof.
  intros. apply gcpn10_init in PR. uunfold PR.
  eapply gf_mon; [apply PR|].
  intros. apply gcpn10_final. apply PR0.
Qed.

Lemma gcpn10_base r rg:
  r <10= gcpn10 r rg.
Proof.
  intros. constructor. ubase. left. apply PR.
Qed.

Lemma gcpn10_bound r rg:
  bnd r <10= gcpn10 r rg.
Proof.
  intros. econstructor. apply cpn10_bound. apply bnd_compat.
  eapply cbound10_mon.
  - apply bnd_compat.
  - apply PR.
  - intros. left. apply PR0.
Qed.

Lemma gcpn10_step r rg:
  gf (gcpn10 rg rg) <10= gcpn10 r rg.
Proof.
  intros. constructor. ubase. right.
  eapply gf_mon. apply PR.
  intros. apply gcpn10_init. apply PR0.
Qed.

Lemma gcpn10_cpn r rg:
  cpn10 gf bnd (gcpn10 r rg) <10= gcpn10 r rg.
Proof.
  intros. constructor. ucpn.
  eapply cpn10_mon. apply PR.
  intros. destruct PR0. apply IN.
Qed.

Lemma gcpn10_clo r rg
      clo (LE: clo <11= cpn10 gf bnd):
  clo (gcpn10 r rg) <10= gcpn10 r rg.
Proof.
  intros. apply gcpn10_cpn, LE, PR.
Qed.

(*
  Fixpoint theorem of gcpn10
 *)

Definition gcut10 (x y z: rel) : rel := fun e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 => y <10= z /\ x e0 e1 e2 e3 e4 e5 e6 e7 e8 e9.

Definition gfixF10 (r rg z: rel) : rel := gcpn10 r (rg \10/ z).

Definition gfix10 (r rg: rel) : rel := cpn10 (gfixF10 r rg) bot11 bot10.

Lemma gfixF10_mon r rg:
  monotone10 (gfixF10 r rg).
Proof.
  red; intros.
  eapply gcpn10_mon. apply IN. intros. apply PR.
  intros. destruct PR. left. apply H. right. apply LE, H.
Qed.

Local Hint Resolve gfixF10_mon.

Lemma gcut10_mon x y : monotone10 (gcut10 x y).
Proof.
  repeat red. intros. destruct IN. split.
  - intros. apply LE, H, PR.
  - apply H0.
Qed.

Lemma gcut10_wcomp r rg (LE: r <10= rg) :
  wcompatible10 gf bnd (gcut10 (gfix10 r rg) rg).
Proof.
  econstructor; [apply gcut10_mon| |].
  { intros.
    destruct PR as [LEz FIX].
    uunfold FIX.
    eapply gf_mon, rclo10_cpn.
    apply cpn10_compat; [apply gf_mon|apply bnd_compat|].
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
  }
  { intros. apply (cbound10_distr bnd_compat) in PR.
    destruct PR, IN.
    uunfold H0. destruct H0. specialize (PTW _ IN).
    eapply (compat10_bound (cpn10_compat gf_mon bnd_compat)) in PTW.
    destruct PTW as [BND|BND].
    - apply (cbound10_distr bnd_compat) in BND. destruct BND.
      destruct IN0.
      + left. apply PTW, H, LE, H0.
      + specialize (PTW _ H0).
        apply (cbound10_compat bnd_compat) in PTW.
        right. eapply gf_mon. apply PTW.
        intros. apply rclo10_cpn, cpn10_bound; [apply bnd_compat|].
        eapply cbound10_mon. apply bnd_compat. apply PR.
        intros. apply rclo10_cpn.
        eapply cpn10_mon. apply PR0.
        intros. destruct PR1.
        * apply rclo10_base. apply H, H1.
        * apply rclo10_clo. econstructor; [|apply H1].
          intros. apply rclo10_base. apply H, PR1.
    - right. eapply gf_mon. apply BND.
      intros. apply rclo10_cpn.
      eapply cpn10_mon. apply PR.
      intros. destruct PR0.
      + apply rclo10_base. apply H, LE, H0.
      + apply rclo10_step.
        eapply gf_mon. apply H0.
        intros. apply rclo10_cpn.
        eapply cpn10_mon. apply PR0.
        intros. destruct PR1.
        * apply rclo10_base. apply H, H1.
        * apply rclo10_clo. econstructor; [|apply H1].
          intros. apply rclo10_base. apply H, PR1.
  }
Qed.

Lemma gfix10_le_cpn r rg (LE: r <10= rg) :
  gfix10 r rg <10= cpn10 gf bnd rg.
Proof.
  intros. eexists.
  - apply wcompat10_compat, gcut10_wcomp. apply gf_mon. apply bnd_compat. apply LE.
  - apply rclo10_clo. split.
    + intros. apply rclo10_base. apply PR0.
    + apply PR.
Qed.

Lemma gfix10_le_gcpn r rg (LE: r <10= rg):
  gfix10 r rg <10= gcpn10 r rg.
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
  
  intros. uunfold PR.
  destruct PR. constructor.
  eapply cpn10_mon. apply IN. intros.
  destruct PR. left; apply H. right.
  eapply gf_mon.  apply H. intros.
  ucpn.
  eapply cpn10_mon. apply PR. intros.
  destruct PR0.
  - ubase. apply H0.
  - eapply gfix10_le_cpn. apply LE. apply H0.
Qed.

Lemma gcpn10_cofix: forall
    r rg (LE: r <10= rg)
    l (OBG: forall rr (INC: rg <10= rr) (CIH: l <10= rr), l <10= gcpn10 r rr),
  l <10= gcpn10 r rg.
Proof.
  intros. apply gfix10_le_gcpn. apply LE.
  eapply cpn10_algebra, PR. apply gfixF10_mon. apply cbound10_bot.
  intros. eapply OBG; intros.
  - left. apply PR1.
  - right. apply PR1.
  - apply PR0.
Qed.

End WCompanion10_main.

Lemma gcpn10_mon_bot bnd bnd' (gf gf': rel -> rel) e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 r rg
      (IN: @gcpn10 gf bnd bot10 bot10 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9)
      (MON: monotone10 gf)
      (MON': monotone10 gf')
      (BASE: compatible_bound10 gf bnd)
      (BASE': compatible_bound10 gf' bnd')
      (LE: gf <11= gf'):
  @gcpn10 gf' bnd' r rg e0 e1 e2 e3 e4 e5 e6 e7 e8 e9.
Proof.
  destruct IN. constructor.
  eapply cpn10_mon; [| intros; right; eapply PR].
  ubase.
  eapply fcpn10_mon_bot, LE; [|apply MON|apply MON'|apply BASE|apply BASE'].
  eapply MON, cpn10_cpn; [|apply MON|apply BASE].
  eapply (compat10_compat (cpn10_compat MON BASE)).
  eapply cpn10_mon. apply IN.
  intros. destruct PR. contradiction. apply H.
Qed.

End WCompanion10.

Hint Resolve gcpn10_base : paco.
Hint Resolve gcpn10_step : paco.

