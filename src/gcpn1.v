Require Import paco1 pcpn1 pcpntac.
Set Implicit Arguments.

Section WCompanion1.

Variable T0 : Type.

Local Notation rel := (rel1 T0).

Section WCompanion1_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone1 gf.

Variable bnd: rel -> rel.
Hypothesis bnd_compat : compatible_bound1 gf bnd.

Inductive gcpn1 (r rg : rel) e0 : Prop :=
| gcpn1_intro (IN: cpn1 gf bnd (r \1/ fcpn1 gf bnd rg) e0)
.              

Lemma gcpn1_mon r r' rg rg' e0
      (IN: @gcpn1 r rg e0)
      (LEr: r <1= r')
      (LErg: rg <1= rg'):
  @gcpn1 r' rg' e0.
Proof.
  destruct IN. constructor.
  eapply cpn1_mon. apply IN. intros.
  destruct PR. left. apply LEr, H. right.
  eapply fcpn1_mon. apply gf_mon. apply H. apply LErg.
Qed.

Lemma gcpn1_init r: gcpn1 r r <1= cpn1 gf bnd r.
Proof.
  intros. destruct PR.
  ucpn.
  eapply cpn1_mon; [apply IN|].
  intros. destruct PR.
  - ubase. apply H.
  - ustep. apply H.
Qed.

Lemma gcpn1_final r rg: cpn1 gf bnd r <1= gcpn1 r rg.
Proof.
  constructor. eapply cpn1_mon. apply PR.
  intros. left. apply PR0.
Qed.

Lemma gcpn1_unfold:
  gcpn1 bot1 bot1 <1= gf (gcpn1 bot1 bot1).
Proof.
  intros. apply gcpn1_init in PR. uunfold PR.
  eapply gf_mon; [apply PR|].
  intros. apply gcpn1_final. apply PR0.
Qed.

Lemma gcpn1_base r rg:
  r <1= gcpn1 r rg.
Proof.
  intros. constructor. ubase. left. apply PR.
Qed.

Lemma gcpn1_bound r rg:
  bnd r <1= gcpn1 r rg.
Proof.
  intros. econstructor. apply cpn1_bound. apply bnd_compat.
  eapply cbound1_mon.
  - apply bnd_compat.
  - apply PR.
  - intros. left. apply PR0.
Qed.

Lemma gcpn1_step r rg:
  gf (gcpn1 rg rg) <1= gcpn1 r rg.
Proof.
  intros. constructor. ubase. right.
  eapply gf_mon. apply PR.
  intros. apply gcpn1_init. apply PR0.
Qed.

Lemma gcpn1_cpn r rg:
  cpn1 gf bnd (gcpn1 r rg) <1= gcpn1 r rg.
Proof.
  intros. constructor. ucpn.
  eapply cpn1_mon. apply PR.
  intros. destruct PR0. apply IN.
Qed.

Lemma gcpn1_clo r rg
      clo (LE: clo <2= cpn1 gf bnd):
  clo (gcpn1 r rg) <1= gcpn1 r rg.
Proof.
  intros. apply gcpn1_cpn, LE, PR.
Qed.

(*
  Fixpoint theorem of gcpn1
 *)

Definition gcut1 (x y z: rel) : rel := fun e0 => y <1= z /\ x e0.

Definition gfixF1 (r rg z: rel) : rel := gcpn1 r (rg \1/ z).

Definition gfix1 (r rg: rel) : rel := cpn1 (gfixF1 r rg) bot2 bot1.

Lemma gfixF1_mon r rg:
  monotone1 (gfixF1 r rg).
Proof.
  red; intros.
  eapply gcpn1_mon. apply IN. intros. apply PR.
  intros. destruct PR. left. apply H. right. apply LE, H.
Qed.

Local Hint Resolve gfixF1_mon.

Lemma gcut1_mon x y : monotone1 (gcut1 x y).
Proof.
  repeat red. intros. destruct IN. split.
  - intros. apply LE, H, PR.
  - apply H0.
Qed.

Lemma gcut1_wcomp r rg (LE: r <1= rg) :
  wcompatible1 gf bnd (gcut1 (gfix1 r rg) rg).
Proof.
  econstructor; [apply gcut1_mon| |].
  { intros.
    destruct PR as [LEz FIX].
    uunfold FIX.
    eapply gf_mon, rclo1_cpn.
    apply cpn1_compat; [apply gf_mon|apply bnd_compat|].
    eapply cpn1_mon; [apply FIX|]. clear x0 FIX; intros.

    destruct PR as [PR | PR].
    - apply LE in PR. apply LEz in PR.
      eapply gf_mon. apply PR.
      intros. apply rclo1_base. apply PR0.
    - eapply gf_mon; [apply PR|]. clear x0 PR; intros.
      eapply rclo1_cpn.
      eapply cpn1_mon. apply PR. clear x0 PR; intros.
      destruct PR as [PR | PR].
      + apply rclo1_step. eapply gf_mon. apply LEz, PR.
        intros. apply rclo1_base, PR0.
      + apply rclo1_clo. split.
        * intros. apply rclo1_step.
          eapply gf_mon. apply LEz. apply PR0.
          intros. apply rclo1_base. apply PR1.
        * apply PR.
  }
  { intros. apply (cbound1_distr bnd_compat) in PR.
    destruct PR, IN.
    uunfold H0. destruct H0. specialize (PTW _ IN).
    eapply (compat1_bound (cpn1_compat gf_mon bnd_compat)) in PTW.
    destruct PTW as [BND|BND].
    - apply (cbound1_distr bnd_compat) in BND. destruct BND.
      destruct IN0.
      + left. apply PTW, H, LE, H0.
      + specialize (PTW _ H0).
        apply (cbound1_compat bnd_compat) in PTW.
        right. eapply gf_mon. apply PTW.
        intros. apply rclo1_cpn, cpn1_bound; [apply bnd_compat|].
        eapply cbound1_mon. apply bnd_compat. apply PR.
        intros. apply rclo1_cpn.
        eapply cpn1_mon. apply PR0.
        intros. destruct PR1.
        * apply rclo1_base. apply H, H1.
        * apply rclo1_clo. econstructor; [|apply H1].
          intros. apply rclo1_base. apply H, PR1.
    - right. eapply gf_mon. apply BND.
      intros. apply rclo1_cpn.
      eapply cpn1_mon. apply PR.
      intros. destruct PR0.
      + apply rclo1_base. apply H, LE, H0.
      + apply rclo1_step.
        eapply gf_mon. apply H0.
        intros. apply rclo1_cpn.
        eapply cpn1_mon. apply PR0.
        intros. destruct PR1.
        * apply rclo1_base. apply H, H1.
        * apply rclo1_clo. econstructor; [|apply H1].
          intros. apply rclo1_base. apply H, PR1.
  }
Qed.

Lemma gfix1_le_cpn r rg (LE: r <1= rg) :
  gfix1 r rg <1= cpn1 gf bnd rg.
Proof.
  intros. eexists.
  - apply wcompat1_compat, gcut1_wcomp. apply gf_mon. apply bnd_compat. apply LE.
  - apply rclo1_clo. split.
    + intros. apply rclo1_base. apply PR0.
    + apply PR.
Qed.

Lemma gfix1_le_gcpn r rg (LE: r <1= rg):
  gfix1 r rg <1= gcpn1 r rg.
Proof.
  (*
    fix
    =
    c(r + gc(rg + fix))
    <=
    c(r + gc(rg + c(rg)))  (by Lemma fix1_le_cpn)
    <=
    c(r + gc(rg))
   *)
  
  intros. uunfold PR.
  destruct PR. constructor.
  eapply cpn1_mon. apply IN. intros.
  destruct PR. left; apply H. right.
  eapply gf_mon.  apply H. intros.
  ucpn.
  eapply cpn1_mon. apply PR. intros.
  destruct PR0.
  - ubase. apply H0.
  - eapply gfix1_le_cpn. apply LE. apply H0.
Qed.

Lemma gcpn1_cofix: forall
    r rg (LE: r <1= rg)
    l (OBG: forall rr (INC: rg <1= rr) (CIH: l <1= rr), l <1= gcpn1 r rr),
  l <1= gcpn1 r rg.
Proof.
  intros. apply gfix1_le_gcpn. apply LE.
  eapply cpn1_algebra, PR. apply gfixF1_mon. apply cbound1_bot.
  intros. eapply OBG; intros.
  - left. apply PR1.
  - right. apply PR1.
  - apply PR0.
Qed.

End WCompanion1_main.

Lemma gcpn1_mon_bot bnd bnd' (gf gf': rel -> rel) e0 r rg
      (IN: @gcpn1 gf bnd bot1 bot1 e0)
      (MON: monotone1 gf)
      (MON': monotone1 gf')
      (BASE: compatible_bound1 gf bnd)
      (BASE': compatible_bound1 gf' bnd')
      (LE: gf <2= gf'):
  @gcpn1 gf' bnd' r rg e0.
Proof.
  destruct IN. constructor.
  eapply cpn1_mon; [| intros; right; eapply PR].
  ubase.
  eapply fcpn1_mon_bot, LE; [|apply MON|apply MON'|apply BASE|apply BASE'].
  eapply MON, cpn1_cpn; [|apply MON|apply BASE].
  eapply (compat1_compat (cpn1_compat MON BASE)).
  eapply cpn1_mon. apply IN.
  intros. destruct PR. contradiction. apply H.
Qed.

End WCompanion1.

Hint Resolve gcpn1_base : paco.
Hint Resolve gcpn1_step : paco.

