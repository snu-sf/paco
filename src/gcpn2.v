Require Import paco2 cpn2 cpntac.
Set Implicit Arguments.

Section WCompanion2.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.

Local Notation rel := (rel2 T0 T1).

Section WCompanion2_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone2 gf.

Variable bnd: rel -> rel.
Hypothesis bnd_compat : compatible_bound2 gf bnd.

Inductive gcpn2 (r rg : rel) e0 e1 : Prop :=
| gcpn2_intro (IN: cpn2 gf bnd (r \2/ fcpn2 gf bnd rg) e0 e1)
.              

Lemma gcpn2_mon r r' rg rg' e0 e1
      (IN: @gcpn2 r rg e0 e1)
      (LEr: r <2= r')
      (LErg: rg <2= rg'):
  @gcpn2 r' rg' e0 e1.
Proof.
  destruct IN. constructor.
  eapply cpn2_mon. apply IN. intros.
  destruct PR. left. apply LEr, H. right.
  eapply fcpn2_mon. apply gf_mon. apply H. apply LErg.
Qed.

Lemma gcpn2_init r: gcpn2 r r <2= cpn2 gf bnd r.
Proof.
  intros. destruct PR.
  ucpn.
  eapply cpn2_mon; [apply IN|].
  intros. destruct PR.
  - ubase. apply H.
  - ustep. apply H.
Qed.

Lemma gcpn2_final r rg: cpn2 gf bnd r <2= gcpn2 r rg.
Proof.
  constructor. eapply cpn2_mon. apply PR.
  intros. left. apply PR0.
Qed.

Lemma gcpn2_unfold:
  gcpn2 bot2 bot2 <2= gf (gcpn2 bot2 bot2).
Proof.
  intros. apply gcpn2_init in PR. uunfold PR.
  eapply gf_mon; [apply PR|].
  intros. apply gcpn2_final. apply PR0.
Qed.

Lemma gcpn2_base r rg:
  r <2= gcpn2 r rg.
Proof.
  intros. constructor. ubase. left. apply PR.
Qed.

Lemma gcpn2_bound r rg:
  bnd r <2= gcpn2 r rg.
Proof.
  intros. econstructor. apply cpn2_bound. apply bnd_compat.
  eapply cbound2_mon.
  - apply bnd_compat.
  - apply PR.
  - intros. left. apply PR0.
Qed.

Lemma gcpn2_step r rg:
  gf (gcpn2 rg rg) <2= gcpn2 r rg.
Proof.
  intros. constructor. ubase. right.
  eapply gf_mon. apply PR.
  intros. apply gcpn2_init. apply PR0.
Qed.

Lemma gcpn2_cpn r rg:
  cpn2 gf bnd (gcpn2 r rg) <2= gcpn2 r rg.
Proof.
  intros. constructor. ucpn.
  eapply cpn2_mon. apply PR.
  intros. destruct PR0. apply IN.
Qed.

Lemma gcpn2_clo r rg
      clo (LE: clo <3= cpn2 gf bnd):
  clo (gcpn2 r rg) <2= gcpn2 r rg.
Proof.
  intros. apply gcpn2_cpn, LE, PR.
Qed.

(*
  Fixpoint theorem of gcpn2
 *)

Definition gcut2 (x y z: rel) : rel := fun e0 e1 => y <2= z /\ x e0 e1.

Definition gfixF2 (r rg z: rel) : rel := gcpn2 r (rg \2/ z).

Definition gfix2 (r rg: rel) : rel := cpn2 (gfixF2 r rg) bot3 bot2.

Lemma gfixF2_mon r rg:
  monotone2 (gfixF2 r rg).
Proof.
  red; intros.
  eapply gcpn2_mon. apply IN. intros. apply PR.
  intros. destruct PR. left. apply H. right. apply LE, H.
Qed.

Local Hint Resolve gfixF2_mon.

Lemma gcut2_mon x y : monotone2 (gcut2 x y).
Proof.
  repeat red. intros. destruct IN. split.
  - intros. apply LE, H, PR.
  - apply H0.
Qed.

Lemma gcut2_wcomp r rg (LE: r <2= rg) :
  wcompatible2 gf bnd (gcut2 (gfix2 r rg) rg).
Proof.
  econstructor; [apply gcut2_mon| |].
  { intros.
    destruct PR as [LEz FIX].
    uunfold FIX.
    eapply gf_mon, rclo2_cpn.
    apply cpn2_compat; [apply gf_mon|apply bnd_compat|].
    eapply cpn2_mon; [apply FIX|]. clear x0 x1 FIX; intros.

    destruct PR as [PR | PR].
    - apply LE in PR. apply LEz in PR.
      eapply gf_mon. apply PR.
      intros. apply rclo2_base. apply PR0.
    - eapply gf_mon; [apply PR|]. clear x0 x1 PR; intros.
      eapply rclo2_cpn.
      eapply cpn2_mon. apply PR. clear x0 x1 PR; intros.
      destruct PR as [PR | PR].
      + apply rclo2_step. eapply gf_mon. apply LEz, PR.
        intros. apply rclo2_base, PR0.
      + apply rclo2_clo. split.
        * intros. apply rclo2_step.
          eapply gf_mon. apply LEz. apply PR0.
          intros. apply rclo2_base. apply PR1.
        * apply PR.
  }
  { intros. apply (cbound2_distr bnd_compat) in PR.
    destruct PR, IN.
    uunfold H0. destruct H0. specialize (PTW _ IN).
    eapply (compat2_bound (cpn2_compat gf_mon bnd_compat)) in PTW.
    destruct PTW as [BND|BND].
    - apply (cbound2_distr bnd_compat) in BND. destruct BND.
      destruct IN0.
      + left. apply PTW, H, LE, H0.
      + specialize (PTW _ H0).
        apply (cbound2_compat bnd_compat) in PTW.
        right. eapply gf_mon. apply PTW.
        intros. apply rclo2_cpn, cpn2_bound; [apply bnd_compat|].
        eapply cbound2_mon. apply bnd_compat. apply PR.
        intros. apply rclo2_cpn.
        eapply cpn2_mon. apply PR0.
        intros. destruct PR1.
        * apply rclo2_base. apply H, H1.
        * apply rclo2_clo. econstructor; [|apply H1].
          intros. apply rclo2_base. apply H, PR1.
    - right. eapply gf_mon. apply BND.
      intros. apply rclo2_cpn.
      eapply cpn2_mon. apply PR.
      intros. destruct PR0.
      + apply rclo2_base. apply H, LE, H0.
      + apply rclo2_step.
        eapply gf_mon. apply H0.
        intros. apply rclo2_cpn.
        eapply cpn2_mon. apply PR0.
        intros. destruct PR1.
        * apply rclo2_base. apply H, H1.
        * apply rclo2_clo. econstructor; [|apply H1].
          intros. apply rclo2_base. apply H, PR1.
  }
Qed.

Lemma gfix2_le_cpn r rg (LE: r <2= rg) :
  gfix2 r rg <2= cpn2 gf bnd rg.
Proof.
  intros. eexists.
  - apply wcompat2_compat, gcut2_wcomp. apply gf_mon. apply bnd_compat. apply LE.
  - apply rclo2_clo. split.
    + intros. apply rclo2_base. apply PR0.
    + apply PR.
Qed.

Lemma gfix2_le_gcpn r rg (LE: r <2= rg):
  gfix2 r rg <2= gcpn2 r rg.
Proof.
  (*
    fix
    =
    c(r + gc(rg + fix))
    <=
    c(r + gc(rg + c(rg)))  (by Lemma fix2_le_cpn)
    <=
    c(r + gc(rg))
   *)
  
  intros. uunfold PR.
  destruct PR. constructor.
  eapply cpn2_mon. apply IN. intros.
  destruct PR. left; apply H. right.
  eapply gf_mon.  apply H. intros.
  ucpn.
  eapply cpn2_mon. apply PR. intros.
  destruct PR0.
  - ubase. apply H0.
  - eapply gfix2_le_cpn. apply LE. apply H0.
Qed.

Lemma gcpn2_cofix: forall
    r rg (LE: r <2= rg)
    l (OBG: forall rr (INC: rg <2= rr) (CIH: l <2= rr), l <2= gcpn2 r rr),
  l <2= gcpn2 r rg.
Proof.
  intros. apply gfix2_le_gcpn. apply LE.
  eapply cpn2_algebra, PR. apply gfixF2_mon. apply cbound2_bot.
  intros. eapply OBG; intros.
  - left. apply PR1.
  - right. apply PR1.
  - apply PR0.
Qed.

End WCompanion2_main.

Lemma gcpn2_mon_bot bnd bnd' (gf gf': rel -> rel) e0 e1 r rg
      (IN: @gcpn2 gf bnd bot2 bot2 e0 e1)
      (MON: monotone2 gf)
      (MON': monotone2 gf')
      (BASE: compatible_bound2 gf bnd)
      (BASE': compatible_bound2 gf' bnd')
      (LE: gf <3= gf'):
  @gcpn2 gf' bnd' r rg e0 e1.
Proof.
  destruct IN. constructor.
  eapply cpn2_mon; [| intros; right; eapply PR].
  ubase.
  eapply fcpn2_mon_bot, LE; [|apply MON|apply MON'|apply BASE|apply BASE'].
  eapply MON, cpn2_cpn; [|apply MON|apply BASE].
  eapply (compat2_compat (cpn2_compat MON BASE)).
  eapply cpn2_mon. apply IN.
  intros. destruct PR. contradiction. apply H.
Qed.

End WCompanion2.

Hint Resolve gcpn2_base : paco.
Hint Resolve gcpn2_step : paco.

