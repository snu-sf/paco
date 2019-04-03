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

Variable bnd: rel -> rel.
Hypothesis bnd_compat : compatible_bound9 gf bnd.

Inductive gcpn9 (r rg : rel) e0 e1 e2 e3 e4 e5 e6 e7 e8 : Prop :=
| gcpn9_intro (IN: cpn9 gf bnd (r \9/ fcpn9 gf bnd rg) e0 e1 e2 e3 e4 e5 e6 e7 e8)
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

Lemma gcpn9_init r: gcpn9 r r <9= cpn9 gf bnd r.
Proof.
  intros. destruct PR.
  ucpn.
  eapply cpn9_mon; [apply IN|].
  intros. destruct PR.
  - ubase. apply H.
  - ustep. apply H.
Qed.

Lemma gcpn9_final r rg: cpn9 gf bnd r <9= gcpn9 r rg.
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

Lemma gcpn9_bound r rg:
  bnd r <9= gcpn9 r rg.
Proof.
  intros. econstructor. apply cpn9_bound. apply bnd_compat.
  eapply cbound9_mon.
  - apply bnd_compat.
  - apply PR.
  - intros. left. apply PR0.
Qed.

Lemma gcpn9_step r rg:
  gf (gcpn9 rg rg) <9= gcpn9 r rg.
Proof.
  intros. constructor. ubase. right.
  eapply gf_mon. apply PR.
  intros. apply gcpn9_init. apply PR0.
Qed.

Lemma gcpn9_cpn r rg:
  cpn9 gf bnd (gcpn9 r rg) <9= gcpn9 r rg.
Proof.
  intros. constructor. ucpn.
  eapply cpn9_mon. apply PR.
  intros. destruct PR0. apply IN.
Qed.

Lemma gcpn9_clo r rg
      clo (LE: clo <10= cpn9 gf bnd):
  clo (gcpn9 r rg) <9= gcpn9 r rg.
Proof.
  intros. apply gcpn9_cpn, LE, PR.
Qed.

(*
  Fixpoint theorem of gcpn9
 *)

Definition gcut9 (x y z: rel) : rel := fun e0 e1 e2 e3 e4 e5 e6 e7 e8 => y <9= z /\ x e0 e1 e2 e3 e4 e5 e6 e7 e8.

Definition gfixF9 (r rg z: rel) : rel := gcpn9 r (rg \9/ z).

Definition gfix9 (r rg: rel) : rel := cpn9 (gfixF9 r rg) bot10 bot9.

Lemma gfixF9_mon r rg:
  monotone9 (gfixF9 r rg).
Proof.
  red; intros.
  eapply gcpn9_mon. apply IN. intros. apply PR.
  intros. destruct PR. left. apply H. right. apply LE, H.
Qed.

Local Hint Resolve gfixF9_mon.

Lemma gcut9_mon x y : monotone9 (gcut9 x y).
Proof.
  repeat red. intros. destruct IN. split.
  - intros. apply LE, H, PR.
  - apply H0.
Qed.

Lemma gcut9_wcomp r rg (LE: r <9= rg) :
  wcompatible9 gf bnd (gcut9 (gfix9 r rg) rg).
Proof.
  econstructor; [apply gcut9_mon| |].
  { intros.
    destruct PR as [LEz FIX].
    uunfold FIX.
    eapply gf_mon, rclo9_cpn.
    apply cpn9_compat; [apply gf_mon|apply bnd_compat|].
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
  }
  { intros. apply (cbound9_distr bnd_compat) in PR.
    destruct PR, IN.
    uunfold H0. destruct H0. specialize (PTW _ IN).
    eapply (compat9_bound (cpn9_compat gf_mon bnd_compat)) in PTW.
    destruct PTW as [BND|BND].
    - apply (cbound9_distr bnd_compat) in BND. destruct BND.
      destruct IN0.
      + left. apply PTW, H, LE, H0.
      + specialize (PTW _ H0).
        apply (cbound9_compat bnd_compat) in PTW.
        right. eapply gf_mon. apply PTW.
        intros. apply rclo9_cpn, cpn9_bound; [apply bnd_compat|].
        eapply cbound9_mon. apply bnd_compat. apply PR.
        intros. apply rclo9_cpn.
        eapply cpn9_mon. apply PR0.
        intros. destruct PR1.
        * apply rclo9_base. apply H, H1.
        * apply rclo9_clo. econstructor; [|apply H1].
          intros. apply rclo9_base. apply H, PR1.
    - right. eapply gf_mon. apply BND.
      intros. apply rclo9_cpn.
      eapply cpn9_mon. apply PR.
      intros. destruct PR0.
      + apply rclo9_base. apply H, LE, H0.
      + apply rclo9_step.
        eapply gf_mon. apply H0.
        intros. apply rclo9_cpn.
        eapply cpn9_mon. apply PR0.
        intros. destruct PR1.
        * apply rclo9_base. apply H, H1.
        * apply rclo9_clo. econstructor; [|apply H1].
          intros. apply rclo9_base. apply H, PR1.
  }
Qed.

Lemma gfix9_le_cpn r rg (LE: r <9= rg) :
  gfix9 r rg <9= cpn9 gf bnd rg.
Proof.
  intros. eexists.
  - apply wcompat9_compat, gcut9_wcomp. apply gf_mon. apply bnd_compat. apply LE.
  - apply rclo9_clo. split.
    + intros. apply rclo9_base. apply PR0.
    + apply PR.
Qed.

Lemma gfix9_le_gcpn r rg (LE: r <9= rg):
  gfix9 r rg <9= gcpn9 r rg.
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
  
  intros. uunfold PR.
  destruct PR. constructor.
  eapply cpn9_mon. apply IN. intros.
  destruct PR. left; apply H. right.
  eapply gf_mon.  apply H. intros.
  ucpn.
  eapply cpn9_mon. apply PR. intros.
  destruct PR0.
  - ubase. apply H0.
  - eapply gfix9_le_cpn. apply LE. apply H0.
Qed.

Lemma gcpn9_cofix: forall
    r rg (LE: r <9= rg)
    l (OBG: forall rr (INC: rg <9= rr) (CIH: l <9= rr), l <9= gcpn9 r rr),
  l <9= gcpn9 r rg.
Proof.
  intros. apply gfix9_le_gcpn. apply LE.
  eapply cpn9_algebra, PR. apply gfixF9_mon. apply cbound9_bot.
  intros. eapply OBG; intros.
  - left. apply PR1.
  - right. apply PR1.
  - apply PR0.
Qed.

End WCompanion9_main.

Lemma gcpn9_mon_bot bnd bnd' (gf gf': rel -> rel) e0 e1 e2 e3 e4 e5 e6 e7 e8 r rg
      (IN: @gcpn9 gf bnd bot9 bot9 e0 e1 e2 e3 e4 e5 e6 e7 e8)
      (MON: monotone9 gf)
      (MON': monotone9 gf')
      (BASE: compatible_bound9 gf bnd)
      (BASE': compatible_bound9 gf' bnd')
      (LE: gf <10= gf'):
  @gcpn9 gf' bnd' r rg e0 e1 e2 e3 e4 e5 e6 e7 e8.
Proof.
  destruct IN. constructor.
  eapply cpn9_mon; [| intros; right; eapply PR].
  ubase.
  eapply fcpn9_mon_bot, LE; [|apply MON|apply MON'|apply BASE|apply BASE'].
  eapply MON, cpn9_cpn; [|apply MON|apply BASE].
  eapply (compat9_compat (cpn9_compat MON BASE)).
  eapply cpn9_mon. apply IN.
  intros. destruct PR. contradiction. apply H.
Qed.

End WCompanion9.

Hint Resolve gcpn9_base : paco.
Hint Resolve gcpn9_step : paco.

