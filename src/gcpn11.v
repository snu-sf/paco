Require Import paco11 cpn11 cpntac.
Set Implicit Arguments.

Section WCompanion11.

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

Local Notation rel := (rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10).

Section WCompanion11_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone11 gf.

Variable bnd: rel -> rel.
Hypothesis bnd_compat : compatible_bound11 gf bnd.

Inductive gcpn11 (r rg : rel) e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 : Prop :=
| gcpn11_intro (IN: cpn11 gf bnd (r \11/ fcpn11 gf bnd rg) e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10)
.              

Lemma gcpn11_mon r r' rg rg' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10
      (IN: @gcpn11 r rg e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10)
      (LEr: r <11= r')
      (LErg: rg <11= rg'):
  @gcpn11 r' rg' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10.
Proof.
  destruct IN. constructor.
  eapply cpn11_mon. apply IN. intros.
  destruct PR. left. apply LEr, H. right.
  eapply fcpn11_mon. apply gf_mon. apply H. apply LErg.
Qed.

Lemma gcpn11_init r: gcpn11 r r <11= cpn11 gf bnd r.
Proof.
  intros. destruct PR.
  ucpn.
  eapply cpn11_mon; [apply IN|].
  intros. destruct PR.
  - ubase. apply H.
  - ustep. apply H.
Qed.

Lemma gcpn11_final r rg: cpn11 gf bnd r <11= gcpn11 r rg.
Proof.
  constructor. eapply cpn11_mon. apply PR.
  intros. left. apply PR0.
Qed.

Lemma gcpn11_unfold:
  gcpn11 bot11 bot11 <11= gf (gcpn11 bot11 bot11).
Proof.
  intros. apply gcpn11_init in PR. uunfold PR.
  eapply gf_mon; [apply PR|].
  intros. apply gcpn11_final. apply PR0.
Qed.

Lemma gcpn11_base r rg:
  r <11= gcpn11 r rg.
Proof.
  intros. constructor. ubase. left. apply PR.
Qed.

Lemma gcpn11_bound r rg:
  bnd r <11= gcpn11 r rg.
Proof.
  intros. econstructor. apply cpn11_bound. apply bnd_compat.
  eapply cbound11_mon.
  - apply bnd_compat.
  - apply PR.
  - intros. left. apply PR0.
Qed.

Lemma gcpn11_step r rg:
  gf (gcpn11 rg rg) <11= gcpn11 r rg.
Proof.
  intros. constructor. ubase. right.
  eapply gf_mon. apply PR.
  intros. apply gcpn11_init. apply PR0.
Qed.

Lemma gcpn11_cpn r rg:
  cpn11 gf bnd (gcpn11 r rg) <11= gcpn11 r rg.
Proof.
  intros. constructor. ucpn.
  eapply cpn11_mon. apply PR.
  intros. destruct PR0. apply IN.
Qed.

Lemma gcpn11_clo r rg
      clo (LE: clo <12= cpn11 gf bnd):
  clo (gcpn11 r rg) <11= gcpn11 r rg.
Proof.
  intros. apply gcpn11_cpn, LE, PR.
Qed.

(*
  Fixpoint theorem of gcpn11
 *)

Definition gcut11 (x y z: rel) : rel := fun e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 => y <11= z /\ x e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10.

Definition gfixF11 (r rg z: rel) : rel := gcpn11 r (rg \11/ z).

Definition gfix11 (r rg: rel) : rel := cpn11 (gfixF11 r rg) bot12 bot11.

Lemma gfixF11_mon r rg:
  monotone11 (gfixF11 r rg).
Proof.
  red; intros.
  eapply gcpn11_mon. apply IN. intros. apply PR.
  intros. destruct PR. left. apply H. right. apply LE, H.
Qed.

Local Hint Resolve gfixF11_mon.

Lemma gcut11_mon x y : monotone11 (gcut11 x y).
Proof.
  repeat red. intros. destruct IN. split.
  - intros. apply LE, H, PR.
  - apply H0.
Qed.

Lemma gcut11_wcomp r rg (LE: r <11= rg) :
  wcompatible11 gf bnd (gcut11 (gfix11 r rg) rg).
Proof.
  econstructor; [apply gcut11_mon| |].
  { intros.
    destruct PR as [LEz FIX].
    uunfold FIX.
    eapply gf_mon, rclo11_cpn.
    apply cpn11_compat; [apply gf_mon|apply bnd_compat|].
    eapply cpn11_mon; [apply FIX|]. clear x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 FIX; intros.

    destruct PR as [PR | PR].
    - apply LE in PR. apply LEz in PR.
      eapply gf_mon. apply PR.
      intros. apply rclo11_base. apply PR0.
    - eapply gf_mon; [apply PR|]. clear x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 PR; intros.
      eapply rclo11_cpn.
      eapply cpn11_mon. apply PR. clear x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 PR; intros.
      destruct PR as [PR | PR].
      + apply rclo11_step. eapply gf_mon. apply LEz, PR.
        intros. apply rclo11_base, PR0.
      + apply rclo11_clo. split.
        * intros. apply rclo11_step.
          eapply gf_mon. apply LEz. apply PR0.
          intros. apply rclo11_base. apply PR1.
        * apply PR.
  }
  { intros. apply (cbound11_distr bnd_compat) in PR.
    destruct PR, IN.
    uunfold H0. destruct H0. specialize (PTW _ IN).
    eapply (compat11_bound (cpn11_compat gf_mon bnd_compat)) in PTW.
    destruct PTW as [BND|BND].
    - apply (cbound11_distr bnd_compat) in BND. destruct BND.
      destruct IN0.
      + left. apply PTW, H, LE, H0.
      + specialize (PTW _ H0).
        apply (cbound11_compat bnd_compat) in PTW.
        right. eapply gf_mon. apply PTW.
        intros. apply rclo11_cpn, cpn11_bound; [apply bnd_compat|].
        eapply cbound11_mon. apply bnd_compat. apply PR.
        intros. apply rclo11_cpn.
        eapply cpn11_mon. apply PR0.
        intros. destruct PR1.
        * apply rclo11_base. apply H, H1.
        * apply rclo11_clo. econstructor; [|apply H1].
          intros. apply rclo11_base. apply H, PR1.
    - right. eapply gf_mon. apply BND.
      intros. apply rclo11_cpn.
      eapply cpn11_mon. apply PR.
      intros. destruct PR0.
      + apply rclo11_base. apply H, LE, H0.
      + apply rclo11_step.
        eapply gf_mon. apply H0.
        intros. apply rclo11_cpn.
        eapply cpn11_mon. apply PR0.
        intros. destruct PR1.
        * apply rclo11_base. apply H, H1.
        * apply rclo11_clo. econstructor; [|apply H1].
          intros. apply rclo11_base. apply H, PR1.
  }
Qed.

Lemma gfix11_le_cpn r rg (LE: r <11= rg) :
  gfix11 r rg <11= cpn11 gf bnd rg.
Proof.
  intros. eexists.
  - apply wcompat11_compat, gcut11_wcomp. apply gf_mon. apply bnd_compat. apply LE.
  - apply rclo11_clo. split.
    + intros. apply rclo11_base. apply PR0.
    + apply PR.
Qed.

Lemma gfix11_le_gcpn r rg (LE: r <11= rg):
  gfix11 r rg <11= gcpn11 r rg.
Proof.
  (*
    fix
    =
    c(r + gc(rg + fix))
    <=
    c(r + gc(rg + c(rg)))  (by Lemma fix11_le_cpn)
    <=
    c(r + gc(rg))
   *)
  
  intros. uunfold PR.
  destruct PR. constructor.
  eapply cpn11_mon. apply IN. intros.
  destruct PR. left; apply H. right.
  eapply gf_mon.  apply H. intros.
  ucpn.
  eapply cpn11_mon. apply PR. intros.
  destruct PR0.
  - ubase. apply H0.
  - eapply gfix11_le_cpn. apply LE. apply H0.
Qed.

Lemma gcpn11_cofix: forall
    r rg (LE: r <11= rg)
    l (OBG: forall rr (INC: rg <11= rr) (CIH: l <11= rr), l <11= gcpn11 r rr),
  l <11= gcpn11 r rg.
Proof.
  intros. apply gfix11_le_gcpn. apply LE.
  eapply cpn11_algebra, PR. apply gfixF11_mon. apply cbound11_bot.
  intros. eapply OBG; intros.
  - left. apply PR1.
  - right. apply PR1.
  - apply PR0.
Qed.

End WCompanion11_main.

Lemma gcpn11_mon_bot bnd bnd' (gf gf': rel -> rel) e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 r rg
      (IN: @gcpn11 gf bnd bot11 bot11 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10)
      (MON: monotone11 gf)
      (MON': monotone11 gf')
      (BASE: compatible_bound11 gf bnd)
      (BASE': compatible_bound11 gf' bnd')
      (LE: gf <12= gf'):
  @gcpn11 gf' bnd' r rg e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10.
Proof.
  destruct IN. constructor.
  eapply cpn11_mon; [| intros; right; eapply PR].
  ubase.
  eapply fcpn11_mon_bot, LE; [|apply MON|apply MON'|apply BASE|apply BASE'].
  eapply MON, cpn11_cpn; [|apply MON|apply BASE].
  eapply (compat11_compat (cpn11_compat MON BASE)).
  eapply cpn11_mon. apply IN.
  intros. destruct PR. contradiction. apply H.
Qed.

End WCompanion11.

Hint Resolve gcpn11_base : paco.
Hint Resolve gcpn11_step : paco.

