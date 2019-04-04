Require Import paco3 pcpn3 pcpntac.
Set Implicit Arguments.

Section WCompanion3.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.

Local Notation rel := (rel3 T0 T1 T2).

Section WCompanion3_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone3 gf.

Variable bnd: rel -> rel.
Hypothesis bnd_compat : compatible_bound3 gf bnd.

Inductive gcpn3 (r rg : rel) e0 e1 e2 : Prop :=
| gcpn3_intro (IN: cpn3 gf bnd (r \3/ fcpn3 gf bnd rg) e0 e1 e2)
.              

Lemma gcpn3_mon r r' rg rg' e0 e1 e2
      (IN: @gcpn3 r rg e0 e1 e2)
      (LEr: r <3= r')
      (LErg: rg <3= rg'):
  @gcpn3 r' rg' e0 e1 e2.
Proof.
  destruct IN. constructor.
  eapply cpn3_mon. apply IN. intros.
  destruct PR. left. apply LEr, H. right.
  eapply fcpn3_mon. apply gf_mon. apply H. apply LErg.
Qed.

Lemma gcpn3_init r: gcpn3 r r <3= cpn3 gf bnd r.
Proof.
  intros. destruct PR.
  ucpn.
  eapply cpn3_mon; [apply IN|].
  intros. destruct PR.
  - ubase. apply H.
  - ustep. apply H.
Qed.

Lemma gcpn3_final r rg: cpn3 gf bnd r <3= gcpn3 r rg.
Proof.
  constructor. eapply cpn3_mon. apply PR.
  intros. left. apply PR0.
Qed.

Lemma gcpn3_unfold:
  gcpn3 bot3 bot3 <3= gf (gcpn3 bot3 bot3).
Proof.
  intros. apply gcpn3_init in PR. uunfold PR.
  eapply gf_mon; [apply PR|].
  intros. apply gcpn3_final. apply PR0.
Qed.

Lemma gcpn3_base r rg:
  r <3= gcpn3 r rg.
Proof.
  intros. constructor. ubase. left. apply PR.
Qed.

Lemma gcpn3_bound r rg:
  bnd r <3= gcpn3 r rg.
Proof.
  intros. econstructor. apply cpn3_bound. apply bnd_compat.
  eapply cbound3_mon.
  - apply bnd_compat.
  - apply PR.
  - intros. left. apply PR0.
Qed.

Lemma gcpn3_step r rg:
  gf (gcpn3 rg rg) <3= gcpn3 r rg.
Proof.
  intros. constructor. ubase. right.
  eapply gf_mon. apply PR.
  intros. apply gcpn3_init. apply PR0.
Qed.

Lemma gcpn3_cpn r rg:
  cpn3 gf bnd (gcpn3 r rg) <3= gcpn3 r rg.
Proof.
  intros. constructor. ucpn.
  eapply cpn3_mon. apply PR.
  intros. destruct PR0. apply IN.
Qed.

Lemma gcpn3_clo r rg
      clo (LE: clo <4= cpn3 gf bnd):
  clo (gcpn3 r rg) <3= gcpn3 r rg.
Proof.
  intros. apply gcpn3_cpn, LE, PR.
Qed.

(*
  Fixpoint theorem of gcpn3
 *)

Definition gcut3 (x y z: rel) : rel := fun e0 e1 e2 => y <3= z /\ x e0 e1 e2.

Definition gfixF3 (r rg z: rel) : rel := gcpn3 r (rg \3/ z).

Definition gfix3 (r rg: rel) : rel := cpn3 (gfixF3 r rg) bot4 bot3.

Lemma gfixF3_mon r rg:
  monotone3 (gfixF3 r rg).
Proof.
  red; intros.
  eapply gcpn3_mon. apply IN. intros. apply PR.
  intros. destruct PR. left. apply H. right. apply LE, H.
Qed.

Local Hint Resolve gfixF3_mon.

Lemma gcut3_mon x y : monotone3 (gcut3 x y).
Proof.
  repeat red. intros. destruct IN. split.
  - intros. apply LE, H, PR.
  - apply H0.
Qed.

Lemma gcut3_wcomp r rg (LE: r <3= rg) :
  wcompatible3 gf bnd (gcut3 (gfix3 r rg) rg).
Proof.
  econstructor; [apply gcut3_mon| |].
  { intros.
    destruct PR as [LEz FIX].
    uunfold FIX.
    eapply gf_mon, rclo3_cpn.
    apply cpn3_compat; [apply gf_mon|apply bnd_compat|].
    eapply cpn3_mon; [apply FIX|]. clear x0 x1 x2 FIX; intros.

    destruct PR as [PR | PR].
    - apply LE in PR. apply LEz in PR.
      eapply gf_mon. apply PR.
      intros. apply rclo3_base. apply PR0.
    - eapply gf_mon; [apply PR|]. clear x0 x1 x2 PR; intros.
      eapply rclo3_cpn.
      eapply cpn3_mon. apply PR. clear x0 x1 x2 PR; intros.
      destruct PR as [PR | PR].
      + apply rclo3_step. eapply gf_mon. apply LEz, PR.
        intros. apply rclo3_base, PR0.
      + apply rclo3_clo. split.
        * intros. apply rclo3_step.
          eapply gf_mon. apply LEz. apply PR0.
          intros. apply rclo3_base. apply PR1.
        * apply PR.
  }
  { intros. apply (cbound3_distr bnd_compat) in PR.
    destruct PR, IN.
    uunfold H0. destruct H0. specialize (PTW _ IN).
    eapply (compat3_bound (cpn3_compat gf_mon bnd_compat)) in PTW.
    destruct PTW as [BND|BND].
    - apply (cbound3_distr bnd_compat) in BND. destruct BND.
      destruct IN0.
      + left. apply PTW, H, LE, H0.
      + specialize (PTW _ H0).
        apply (cbound3_compat bnd_compat) in PTW.
        right. eapply gf_mon. apply PTW.
        intros. apply rclo3_cpn, cpn3_bound; [apply bnd_compat|].
        eapply cbound3_mon. apply bnd_compat. apply PR.
        intros. apply rclo3_cpn.
        eapply cpn3_mon. apply PR0.
        intros. destruct PR1.
        * apply rclo3_base. apply H, H1.
        * apply rclo3_clo. econstructor; [|apply H1].
          intros. apply rclo3_base. apply H, PR1.
    - right. eapply gf_mon. apply BND.
      intros. apply rclo3_cpn.
      eapply cpn3_mon. apply PR.
      intros. destruct PR0.
      + apply rclo3_base. apply H, LE, H0.
      + apply rclo3_step.
        eapply gf_mon. apply H0.
        intros. apply rclo3_cpn.
        eapply cpn3_mon. apply PR0.
        intros. destruct PR1.
        * apply rclo3_base. apply H, H1.
        * apply rclo3_clo. econstructor; [|apply H1].
          intros. apply rclo3_base. apply H, PR1.
  }
Qed.

Lemma gfix3_le_cpn r rg (LE: r <3= rg) :
  gfix3 r rg <3= cpn3 gf bnd rg.
Proof.
  intros. eexists.
  - apply wcompat3_compat, gcut3_wcomp. apply gf_mon. apply bnd_compat. apply LE.
  - apply rclo3_clo. split.
    + intros. apply rclo3_base. apply PR0.
    + apply PR.
Qed.

Lemma gfix3_le_gcpn r rg (LE: r <3= rg):
  gfix3 r rg <3= gcpn3 r rg.
Proof.
  (*
    fix
    =
    c(r + gc(rg + fix))
    <=
    c(r + gc(rg + c(rg)))  (by Lemma fix3_le_cpn)
    <=
    c(r + gc(rg))
   *)
  
  intros. uunfold PR.
  destruct PR. constructor.
  eapply cpn3_mon. apply IN. intros.
  destruct PR. left; apply H. right.
  eapply gf_mon.  apply H. intros.
  ucpn.
  eapply cpn3_mon. apply PR. intros.
  destruct PR0.
  - ubase. apply H0.
  - eapply gfix3_le_cpn. apply LE. apply H0.
Qed.

Lemma gcpn3_cofix: forall
    r rg (LE: r <3= rg)
    l (OBG: forall rr (INC: rg <3= rr) (CIH: l <3= rr), l <3= gcpn3 r rr),
  l <3= gcpn3 r rg.
Proof.
  intros. apply gfix3_le_gcpn. apply LE.
  eapply cpn3_algebra, PR. apply gfixF3_mon. apply cbound3_bot.
  intros. eapply OBG; intros.
  - left. apply PR1.
  - right. apply PR1.
  - apply PR0.
Qed.

End WCompanion3_main.

Lemma gcpn3_mon_bot bnd bnd' (gf gf': rel -> rel) e0 e1 e2 r rg
      (IN: @gcpn3 gf bnd bot3 bot3 e0 e1 e2)
      (MON: monotone3 gf)
      (MON': monotone3 gf')
      (BASE: compatible_bound3 gf bnd)
      (BASE': compatible_bound3 gf' bnd')
      (LE: gf <4= gf'):
  @gcpn3 gf' bnd' r rg e0 e1 e2.
Proof.
  destruct IN. constructor.
  eapply cpn3_mon; [| intros; right; eapply PR].
  ubase.
  eapply fcpn3_mon_bot, LE; [|apply MON|apply MON'|apply BASE|apply BASE'].
  eapply MON, cpn3_cpn; [|apply MON|apply BASE].
  eapply (compat3_compat (cpn3_compat MON BASE)).
  eapply cpn3_mon. apply IN.
  intros. destruct PR. contradiction. apply H.
Qed.

End WCompanion3.

Hint Resolve gcpn3_base : paco.
Hint Resolve gcpn3_step : paco.

