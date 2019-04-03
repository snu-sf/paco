Require Import paco4 cpn4 cpntac.
Set Implicit Arguments.

Section WCompanion4.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.

Local Notation rel := (rel4 T0 T1 T2 T3).

Section WCompanion4_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone4 gf.

Variable bnd: rel -> rel.
Hypothesis bnd_compat : compatible_bound4 gf bnd.

Inductive gcpn4 (r rg : rel) e0 e1 e2 e3 : Prop :=
| gcpn4_intro (IN: cpn4 gf bnd (r \4/ fcpn4 gf bnd rg) e0 e1 e2 e3)
.              

Lemma gcpn4_mon r r' rg rg' e0 e1 e2 e3
      (IN: @gcpn4 r rg e0 e1 e2 e3)
      (LEr: r <4= r')
      (LErg: rg <4= rg'):
  @gcpn4 r' rg' e0 e1 e2 e3.
Proof.
  destruct IN. constructor.
  eapply cpn4_mon. apply IN. intros.
  destruct PR. left. apply LEr, H. right.
  eapply fcpn4_mon. apply gf_mon. apply H. apply LErg.
Qed.

Lemma gcpn4_init r: gcpn4 r r <4= cpn4 gf bnd r.
Proof.
  intros. destruct PR.
  ucpn.
  eapply cpn4_mon; [apply IN|].
  intros. destruct PR.
  - ubase. apply H.
  - ustep. apply H.
Qed.

Lemma gcpn4_final r rg: cpn4 gf bnd r <4= gcpn4 r rg.
Proof.
  constructor. eapply cpn4_mon. apply PR.
  intros. left. apply PR0.
Qed.

Lemma gcpn4_unfold:
  gcpn4 bot4 bot4 <4= gf (gcpn4 bot4 bot4).
Proof.
  intros. apply gcpn4_init in PR. uunfold PR.
  eapply gf_mon; [apply PR|].
  intros. apply gcpn4_final. apply PR0.
Qed.

Lemma gcpn4_base r rg:
  r <4= gcpn4 r rg.
Proof.
  intros. constructor. ubase. left. apply PR.
Qed.

Lemma gcpn4_bound r rg:
  bnd r <4= gcpn4 r rg.
Proof.
  intros. econstructor. apply cpn4_bound. apply bnd_compat.
  eapply cbound4_mon.
  - apply bnd_compat.
  - apply PR.
  - intros. left. apply PR0.
Qed.

Lemma gcpn4_step r rg:
  gf (gcpn4 rg rg) <4= gcpn4 r rg.
Proof.
  intros. constructor. ubase. right.
  eapply gf_mon. apply PR.
  intros. apply gcpn4_init. apply PR0.
Qed.

Lemma gcpn4_cpn r rg:
  cpn4 gf bnd (gcpn4 r rg) <4= gcpn4 r rg.
Proof.
  intros. constructor. ucpn.
  eapply cpn4_mon. apply PR.
  intros. destruct PR0. apply IN.
Qed.

Lemma gcpn4_clo r rg
      clo (LE: clo <5= cpn4 gf bnd):
  clo (gcpn4 r rg) <4= gcpn4 r rg.
Proof.
  intros. apply gcpn4_cpn, LE, PR.
Qed.

(*
  Fixpoint theorem of gcpn4
 *)

Definition gcut4 (x y z: rel) : rel := fun e0 e1 e2 e3 => y <4= z /\ x e0 e1 e2 e3.

Definition gfixF4 (r rg z: rel) : rel := gcpn4 r (rg \4/ z).

Definition gfix4 (r rg: rel) : rel := cpn4 (gfixF4 r rg) bot5 bot4.

Lemma gfixF4_mon r rg:
  monotone4 (gfixF4 r rg).
Proof.
  red; intros.
  eapply gcpn4_mon. apply IN. intros. apply PR.
  intros. destruct PR. left. apply H. right. apply LE, H.
Qed.

Local Hint Resolve gfixF4_mon.

Lemma gcut4_mon x y : monotone4 (gcut4 x y).
Proof.
  repeat red. intros. destruct IN. split.
  - intros. apply LE, H, PR.
  - apply H0.
Qed.

Lemma gcut4_wcomp r rg (LE: r <4= rg) :
  wcompatible4 gf bnd (gcut4 (gfix4 r rg) rg).
Proof.
  econstructor; [apply gcut4_mon| |].
  { intros.
    destruct PR as [LEz FIX].
    uunfold FIX.
    eapply gf_mon, rclo4_cpn.
    apply cpn4_compat; [apply gf_mon|apply bnd_compat|].
    eapply cpn4_mon; [apply FIX|]. clear x0 x1 x2 x3 FIX; intros.

    destruct PR as [PR | PR].
    - apply LE in PR. apply LEz in PR.
      eapply gf_mon. apply PR.
      intros. apply rclo4_base. apply PR0.
    - eapply gf_mon; [apply PR|]. clear x0 x1 x2 x3 PR; intros.
      eapply rclo4_cpn.
      eapply cpn4_mon. apply PR. clear x0 x1 x2 x3 PR; intros.
      destruct PR as [PR | PR].
      + apply rclo4_step. eapply gf_mon. apply LEz, PR.
        intros. apply rclo4_base, PR0.
      + apply rclo4_clo. split.
        * intros. apply rclo4_step.
          eapply gf_mon. apply LEz. apply PR0.
          intros. apply rclo4_base. apply PR1.
        * apply PR.
  }
  { intros. apply (cbound4_distr bnd_compat) in PR.
    destruct PR, IN.
    uunfold H0. destruct H0. specialize (PTW _ IN).
    eapply (compat4_bound (cpn4_compat gf_mon bnd_compat)) in PTW.
    destruct PTW as [BND|BND].
    - apply (cbound4_distr bnd_compat) in BND. destruct BND.
      destruct IN0.
      + left. apply PTW, H, LE, H0.
      + specialize (PTW _ H0).
        apply (cbound4_compat bnd_compat) in PTW.
        right. eapply gf_mon. apply PTW.
        intros. apply rclo4_cpn, cpn4_bound; [apply bnd_compat|].
        eapply cbound4_mon. apply bnd_compat. apply PR.
        intros. apply rclo4_cpn.
        eapply cpn4_mon. apply PR0.
        intros. destruct PR1.
        * apply rclo4_base. apply H, H1.
        * apply rclo4_clo. econstructor; [|apply H1].
          intros. apply rclo4_base. apply H, PR1.
    - right. eapply gf_mon. apply BND.
      intros. apply rclo4_cpn.
      eapply cpn4_mon. apply PR.
      intros. destruct PR0.
      + apply rclo4_base. apply H, LE, H0.
      + apply rclo4_step.
        eapply gf_mon. apply H0.
        intros. apply rclo4_cpn.
        eapply cpn4_mon. apply PR0.
        intros. destruct PR1.
        * apply rclo4_base. apply H, H1.
        * apply rclo4_clo. econstructor; [|apply H1].
          intros. apply rclo4_base. apply H, PR1.
  }
Qed.

Lemma gfix4_le_cpn r rg (LE: r <4= rg) :
  gfix4 r rg <4= cpn4 gf bnd rg.
Proof.
  intros. eexists.
  - apply wcompat4_compat, gcut4_wcomp. apply gf_mon. apply bnd_compat. apply LE.
  - apply rclo4_clo. split.
    + intros. apply rclo4_base. apply PR0.
    + apply PR.
Qed.

Lemma gfix4_le_gcpn r rg (LE: r <4= rg):
  gfix4 r rg <4= gcpn4 r rg.
Proof.
  (*
    fix
    =
    c(r + gc(rg + fix))
    <=
    c(r + gc(rg + c(rg)))  (by Lemma fix4_le_cpn)
    <=
    c(r + gc(rg))
   *)
  
  intros. uunfold PR.
  destruct PR. constructor.
  eapply cpn4_mon. apply IN. intros.
  destruct PR. left; apply H. right.
  eapply gf_mon.  apply H. intros.
  ucpn.
  eapply cpn4_mon. apply PR. intros.
  destruct PR0.
  - ubase. apply H0.
  - eapply gfix4_le_cpn. apply LE. apply H0.
Qed.

Lemma gcpn4_cofix: forall
    r rg (LE: r <4= rg)
    l (OBG: forall rr (INC: rg <4= rr) (CIH: l <4= rr), l <4= gcpn4 r rr),
  l <4= gcpn4 r rg.
Proof.
  intros. apply gfix4_le_gcpn. apply LE.
  eapply cpn4_algebra, PR. apply gfixF4_mon. apply cbound4_bot.
  intros. eapply OBG; intros.
  - left. apply PR1.
  - right. apply PR1.
  - apply PR0.
Qed.

End WCompanion4_main.

Lemma gcpn4_mon_bot bnd bnd' (gf gf': rel -> rel) e0 e1 e2 e3 r rg
      (IN: @gcpn4 gf bnd bot4 bot4 e0 e1 e2 e3)
      (MON: monotone4 gf)
      (MON': monotone4 gf')
      (BASE: compatible_bound4 gf bnd)
      (BASE': compatible_bound4 gf' bnd')
      (LE: gf <5= gf'):
  @gcpn4 gf' bnd' r rg e0 e1 e2 e3.
Proof.
  destruct IN. constructor.
  eapply cpn4_mon; [| intros; right; eapply PR].
  ubase.
  eapply fcpn4_mon_bot, LE; [|apply MON|apply MON'|apply BASE|apply BASE'].
  eapply MON, cpn4_cpn; [|apply MON|apply BASE].
  eapply (compat4_compat (cpn4_compat MON BASE)).
  eapply cpn4_mon. apply IN.
  intros. destruct PR. contradiction. apply H.
Qed.

End WCompanion4.

Hint Resolve gcpn4_base : paco.
Hint Resolve gcpn4_step : paco.

