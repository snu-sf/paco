Require Import paco0 pcpn0 pcpntac.
Set Implicit Arguments.

Section WCompanion0.


Local Notation rel := (rel0).

Section WCompanion0_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone0 gf.

Variable bnd: rel -> rel.
Hypothesis bnd_compat : compatible_bound0 gf bnd.

Inductive gcpn0 (r rg : rel) : Prop :=
| gcpn0_intro (IN: cpn0 gf bnd (r \0/ fcpn0 gf bnd rg))
.              

Lemma gcpn0_mon r r' rg rg'
      (IN: @gcpn0 r rg)
      (LEr: r <0= r')
      (LErg: rg <0= rg'):
  @gcpn0 r' rg'.
Proof.
  destruct IN. constructor.
  eapply cpn0_mon. apply IN. intros.
  destruct PR. left. apply LEr, H. right.
  eapply fcpn0_mon. apply gf_mon. apply H. apply LErg.
Qed.

Lemma gcpn0_init r: gcpn0 r r <0= cpn0 gf bnd r.
Proof.
  intros. destruct PR.
  ucpn.
  eapply cpn0_mon; [apply IN|].
  intros. destruct PR.
  - ubase. apply H.
  - ustep. apply H.
Qed.

Lemma gcpn0_final r rg: cpn0 gf bnd r <0= gcpn0 r rg.
Proof.
  constructor. eapply cpn0_mon. apply PR.
  intros. left. apply PR0.
Qed.

Lemma gcpn0_unfold:
  gcpn0 bot0 bot0 <0= gf (gcpn0 bot0 bot0).
Proof.
  intros. apply gcpn0_init in PR. uunfold PR.
  eapply gf_mon; [apply PR|].
  intros. apply gcpn0_final. apply PR0.
Qed.

Lemma gcpn0_base r rg:
  r <0= gcpn0 r rg.
Proof.
  intros. constructor. ubase. left. apply PR.
Qed.

Lemma gcpn0_bound r rg:
  bnd r <0= gcpn0 r rg.
Proof.
  intros. econstructor. apply cpn0_bound. apply bnd_compat.
  eapply cbound0_mon.
  - apply bnd_compat.
  - apply PR.
  - intros. left. apply PR0.
Qed.

Lemma gcpn0_step r rg:
  gf (gcpn0 rg rg) <0= gcpn0 r rg.
Proof.
  intros. constructor. ubase. right.
  eapply gf_mon. apply PR.
  intros. apply gcpn0_init. apply PR0.
Qed.

Lemma gcpn0_cpn r rg:
  cpn0 gf bnd (gcpn0 r rg) <0= gcpn0 r rg.
Proof.
  intros. constructor. ucpn.
  eapply cpn0_mon. apply PR.
  intros. destruct PR0. apply IN.
Qed.

Lemma gcpn0_clo r rg
      clo (LE: clo <1= cpn0 gf bnd):
  clo (gcpn0 r rg) <0= gcpn0 r rg.
Proof.
  intros. apply gcpn0_cpn, LE, PR.
Qed.

(*
  Fixpoint theorem of gcpn0
 *)

Definition gcut0 (x y z: rel) : rel := y <0= z /\ x.

Definition gfixF0 (r rg z: rel) : rel := gcpn0 r (rg \0/ z).

Definition gfix0 (r rg: rel) : rel := cpn0 (gfixF0 r rg) bot1 bot0.

Lemma gfixF0_mon r rg:
  monotone0 (gfixF0 r rg).
Proof.
  red; intros.
  eapply gcpn0_mon. apply IN. intros. apply PR.
  intros. destruct PR. left. apply H. right. apply LE, H.
Qed.

Local Hint Resolve gfixF0_mon.

Lemma gcut0_mon x y : monotone0 (gcut0 x y).
Proof.
  repeat red. intros. destruct IN. split.
  - intros. apply LE, H, PR.
  - apply H0.
Qed.

Lemma gcut0_wcomp r rg (LE: r <0= rg) :
  wcompatible0 gf bnd (gcut0 (gfix0 r rg) rg).
Proof.
  econstructor; [apply gcut0_mon| |].
  { intros.
    destruct PR as [LEz FIX].
    uunfold FIX.
    eapply gf_mon, rclo0_cpn.
    apply cpn0_compat; [apply gf_mon|apply bnd_compat|].
    eapply cpn0_mon; [apply FIX|]. clear FIX; intros.

    destruct PR as [PR | PR].
    - apply LE in PR. apply LEz in PR.
      eapply gf_mon. apply PR.
      intros. apply rclo0_base. apply PR0.
    - eapply gf_mon; [apply PR|]. clear PR; intros.
      eapply rclo0_cpn.
      eapply cpn0_mon. apply PR. clear PR; intros.
      destruct PR as [PR | PR].
      + apply rclo0_step. eapply gf_mon. apply LEz, PR.
        intros. apply rclo0_base, PR0.
      + apply rclo0_clo. split.
        * intros. apply rclo0_step.
          eapply gf_mon. apply LEz. apply PR0.
          intros. apply rclo0_base. apply PR1.
        * apply PR.
  }
  { intros. apply (cbound0_distr bnd_compat) in PR.
    destruct PR, IN.
    uunfold H0. destruct H0. specialize (PTW _ IN).
    eapply (compat0_bound (cpn0_compat gf_mon bnd_compat)) in PTW.
    destruct PTW as [BND|BND].
    - apply (cbound0_distr bnd_compat) in BND. destruct BND.
      destruct IN0.
      + left. apply PTW, H, LE, H0.
      + specialize (PTW _ H0).
        apply (cbound0_compat bnd_compat) in PTW.
        right. eapply gf_mon. apply PTW.
        intros. apply rclo0_cpn, cpn0_bound; [apply bnd_compat|].
        eapply cbound0_mon. apply bnd_compat. apply PR.
        intros. apply rclo0_cpn.
        eapply cpn0_mon. apply PR0.
        intros. destruct PR1.
        * apply rclo0_base. apply H, H1.
        * apply rclo0_clo. econstructor; [|apply H1].
          intros. apply rclo0_base. apply H, PR1.
    - right. eapply gf_mon. apply BND.
      intros. apply rclo0_cpn.
      eapply cpn0_mon. apply PR.
      intros. destruct PR0.
      + apply rclo0_base. apply H, LE, H0.
      + apply rclo0_step.
        eapply gf_mon. apply H0.
        intros. apply rclo0_cpn.
        eapply cpn0_mon. apply PR0.
        intros. destruct PR1.
        * apply rclo0_base. apply H, H1.
        * apply rclo0_clo. econstructor; [|apply H1].
          intros. apply rclo0_base. apply H, PR1.
  }
Qed.

Lemma gfix0_le_cpn r rg (LE: r <0= rg) :
  gfix0 r rg <0= cpn0 gf bnd rg.
Proof.
  intros. eexists.
  - apply wcompat0_compat, gcut0_wcomp. apply gf_mon. apply bnd_compat. apply LE.
  - apply rclo0_clo. split.
    + intros. apply rclo0_base. apply PR0.
    + apply PR.
Qed.

Lemma gfix0_le_gcpn r rg (LE: r <0= rg):
  gfix0 r rg <0= gcpn0 r rg.
Proof.
  (*
    fix
    =
    c(r + gc(rg + fix))
    <=
    c(r + gc(rg + c(rg)))  (by Lemma fix0_le_cpn)
    <=
    c(r + gc(rg))
   *)
  
  intros. uunfold PR.
  destruct PR. constructor.
  eapply cpn0_mon. apply IN. intros.
  destruct PR. left; apply H. right.
  eapply gf_mon.  apply H. intros.
  ucpn.
  eapply cpn0_mon. apply PR. intros.
  destruct PR0.
  - ubase. apply H0.
  - eapply gfix0_le_cpn. apply LE. apply H0.
Qed.

Lemma gcpn0_cofix: forall
    r rg (LE: r <0= rg)
    l (OBG: forall rr (INC: rg <0= rr) (CIH: l <0= rr), l <0= gcpn0 r rr),
  l <0= gcpn0 r rg.
Proof.
  intros. apply gfix0_le_gcpn. apply LE.
  eapply cpn0_algebra, PR. apply gfixF0_mon. apply cbound0_bot.
  intros. eapply OBG; intros.
  - left. apply PR1.
  - right. apply PR1.
  - apply PR0.
Qed.

End WCompanion0_main.

Lemma gcpn0_mon_bot bnd bnd' (gf gf': rel -> rel) r rg
      (IN: @gcpn0 gf bnd bot0 bot0)
      (MON: monotone0 gf)
      (MON': monotone0 gf')
      (BASE: compatible_bound0 gf bnd)
      (BASE': compatible_bound0 gf' bnd')
      (LE: gf <1= gf'):
  @gcpn0 gf' bnd' r rg.
Proof.
  destruct IN. constructor.
  eapply cpn0_mon; [| intros; right; eapply PR].
  ubase.
  eapply fcpn0_mon_bot, LE; [|apply MON|apply MON'|apply BASE|apply BASE'].
  eapply MON, cpn0_cpn; [|apply MON|apply BASE].
  eapply (compat0_compat (cpn0_compat MON BASE)).
  eapply cpn0_mon. apply IN.
  intros. destruct PR. contradiction. apply H.
Qed.

End WCompanion0.

Hint Resolve gcpn0_base : paco.
Hint Resolve gcpn0_step : paco.

