Require Import paco5 cpn5 cpntac.
Set Implicit Arguments.

Section WCompanion5.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.

Local Notation rel := (rel5 T0 T1 T2 T3 T4).

Section WCompanion5_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone5 gf.

Variable bnd: rel -> rel.
Hypothesis bnd_compat : compatible_bound5 gf bnd.

Inductive gcpn5 (r rg : rel) e0 e1 e2 e3 e4 : Prop :=
| gcpn5_intro (IN: cpn5 gf bnd (r \5/ fcpn5 gf bnd rg) e0 e1 e2 e3 e4)
.              

Lemma gcpn5_mon r r' rg rg' e0 e1 e2 e3 e4
      (IN: @gcpn5 r rg e0 e1 e2 e3 e4)
      (LEr: r <5= r')
      (LErg: rg <5= rg'):
  @gcpn5 r' rg' e0 e1 e2 e3 e4.
Proof.
  destruct IN. constructor.
  eapply cpn5_mon. apply IN. intros.
  destruct PR. left. apply LEr, H. right.
  eapply fcpn5_mon. apply gf_mon. apply H. apply LErg.
Qed.

Lemma gcpn5_init r: gcpn5 r r <5= cpn5 gf bnd r.
Proof.
  intros. destruct PR.
  ucpn.
  eapply cpn5_mon; [apply IN|].
  intros. destruct PR.
  - ubase. apply H.
  - ustep. apply H.
Qed.

Lemma gcpn5_final r rg: cpn5 gf bnd r <5= gcpn5 r rg.
Proof.
  constructor. eapply cpn5_mon. apply PR.
  intros. left. apply PR0.
Qed.

Lemma gcpn5_unfold:
  gcpn5 bot5 bot5 <5= gf (gcpn5 bot5 bot5).
Proof.
  intros. apply gcpn5_init in PR. uunfold PR.
  eapply gf_mon; [apply PR|].
  intros. apply gcpn5_final. apply PR0.
Qed.

Lemma gcpn5_base r rg:
  r <5= gcpn5 r rg.
Proof.
  intros. constructor. ubase. left. apply PR.
Qed.

Lemma gcpn5_bound r rg:
  bnd r <5= gcpn5 r rg.
Proof.
  intros. econstructor. apply cpn5_bound. apply bnd_compat.
  eapply cbound5_mon.
  - apply bnd_compat.
  - apply PR.
  - intros. left. apply PR0.
Qed.

Lemma gcpn5_step r rg:
  gf (gcpn5 rg rg) <5= gcpn5 r rg.
Proof.
  intros. constructor. ubase. right.
  eapply gf_mon. apply PR.
  intros. apply gcpn5_init. apply PR0.
Qed.

Lemma gcpn5_cpn r rg:
  cpn5 gf bnd (gcpn5 r rg) <5= gcpn5 r rg.
Proof.
  intros. constructor. ucpn.
  eapply cpn5_mon. apply PR.
  intros. destruct PR0. apply IN.
Qed.

Lemma gcpn5_clo r rg
      clo (LE: clo <6= cpn5 gf bnd):
  clo (gcpn5 r rg) <5= gcpn5 r rg.
Proof.
  intros. apply gcpn5_cpn, LE, PR.
Qed.

(*
  Fixpoint theorem of gcpn5
 *)

Definition gcut5 (x y z: rel) : rel := fun e0 e1 e2 e3 e4 => y <5= z /\ x e0 e1 e2 e3 e4.

Definition gfixF5 (r rg z: rel) : rel := gcpn5 r (rg \5/ z).

Definition gfix5 (r rg: rel) : rel := cpn5 (gfixF5 r rg) bot6 bot5.

Lemma gfixF5_mon r rg:
  monotone5 (gfixF5 r rg).
Proof.
  red; intros.
  eapply gcpn5_mon. apply IN. intros. apply PR.
  intros. destruct PR. left. apply H. right. apply LE, H.
Qed.

Local Hint Resolve gfixF5_mon.

Lemma gcut5_mon x y : monotone5 (gcut5 x y).
Proof.
  repeat red. intros. destruct IN. split.
  - intros. apply LE, H, PR.
  - apply H0.
Qed.

Lemma gcut5_wcomp r rg (LE: r <5= rg) :
  wcompatible5 gf bnd (gcut5 (gfix5 r rg) rg).
Proof.
  econstructor; [apply gcut5_mon| |].
  { intros.
    destruct PR as [LEz FIX].
    uunfold FIX.
    eapply gf_mon, rclo5_cpn.
    apply cpn5_compat; [apply gf_mon|apply bnd_compat|].
    eapply cpn5_mon; [apply FIX|]. clear x0 x1 x2 x3 x4 FIX; intros.

    destruct PR as [PR | PR].
    - apply LE in PR. apply LEz in PR.
      eapply gf_mon. apply PR.
      intros. apply rclo5_base. apply PR0.
    - eapply gf_mon; [apply PR|]. clear x0 x1 x2 x3 x4 PR; intros.
      eapply rclo5_cpn.
      eapply cpn5_mon. apply PR. clear x0 x1 x2 x3 x4 PR; intros.
      destruct PR as [PR | PR].
      + apply rclo5_step. eapply gf_mon. apply LEz, PR.
        intros. apply rclo5_base, PR0.
      + apply rclo5_clo. split.
        * intros. apply rclo5_step.
          eapply gf_mon. apply LEz. apply PR0.
          intros. apply rclo5_base. apply PR1.
        * apply PR.
  }
  { intros. apply (cbound5_distr bnd_compat) in PR.
    destruct PR, IN.
    uunfold H0. destruct H0. specialize (PTW _ IN).
    eapply (compat5_bound (cpn5_compat gf_mon bnd_compat)) in PTW.
    destruct PTW as [BND|BND].
    - apply (cbound5_distr bnd_compat) in BND. destruct BND.
      destruct IN0.
      + left. apply PTW, H, LE, H0.
      + specialize (PTW _ H0).
        apply (cbound5_compat bnd_compat) in PTW.
        right. eapply gf_mon. apply PTW.
        intros. apply rclo5_cpn, cpn5_bound; [apply bnd_compat|].
        eapply cbound5_mon. apply bnd_compat. apply PR.
        intros. apply rclo5_cpn.
        eapply cpn5_mon. apply PR0.
        intros. destruct PR1.
        * apply rclo5_base. apply H, H1.
        * apply rclo5_clo. econstructor; [|apply H1].
          intros. apply rclo5_base. apply H, PR1.
    - right. eapply gf_mon. apply BND.
      intros. apply rclo5_cpn.
      eapply cpn5_mon. apply PR.
      intros. destruct PR0.
      + apply rclo5_base. apply H, LE, H0.
      + apply rclo5_step.
        eapply gf_mon. apply H0.
        intros. apply rclo5_cpn.
        eapply cpn5_mon. apply PR0.
        intros. destruct PR1.
        * apply rclo5_base. apply H, H1.
        * apply rclo5_clo. econstructor; [|apply H1].
          intros. apply rclo5_base. apply H, PR1.
  }
Qed.

Lemma gfix5_le_cpn r rg (LE: r <5= rg) :
  gfix5 r rg <5= cpn5 gf bnd rg.
Proof.
  intros. eexists.
  - apply wcompat5_compat, gcut5_wcomp. apply gf_mon. apply bnd_compat. apply LE.
  - apply rclo5_clo. split.
    + intros. apply rclo5_base. apply PR0.
    + apply PR.
Qed.

Lemma gfix5_le_gcpn r rg (LE: r <5= rg):
  gfix5 r rg <5= gcpn5 r rg.
Proof.
  (*
    fix
    =
    c(r + gc(rg + fix))
    <=
    c(r + gc(rg + c(rg)))  (by Lemma fix5_le_cpn)
    <=
    c(r + gc(rg))
   *)
  
  intros. uunfold PR.
  destruct PR. constructor.
  eapply cpn5_mon. apply IN. intros.
  destruct PR. left; apply H. right.
  eapply gf_mon.  apply H. intros.
  ucpn.
  eapply cpn5_mon. apply PR. intros.
  destruct PR0.
  - ubase. apply H0.
  - eapply gfix5_le_cpn. apply LE. apply H0.
Qed.

Lemma gcpn5_cofix: forall
    r rg (LE: r <5= rg)
    l (OBG: forall rr (INC: rg <5= rr) (CIH: l <5= rr), l <5= gcpn5 r rr),
  l <5= gcpn5 r rg.
Proof.
  intros. apply gfix5_le_gcpn. apply LE.
  eapply cpn5_algebra, PR. apply gfixF5_mon. apply cbound5_bot.
  intros. eapply OBG; intros.
  - left. apply PR1.
  - right. apply PR1.
  - apply PR0.
Qed.

End WCompanion5_main.

Lemma gcpn5_mon_bot bnd bnd' (gf gf': rel -> rel) e0 e1 e2 e3 e4 r rg
      (IN: @gcpn5 gf bnd bot5 bot5 e0 e1 e2 e3 e4)
      (MON: monotone5 gf)
      (MON': monotone5 gf')
      (BASE: compatible_bound5 gf bnd)
      (BASE': compatible_bound5 gf' bnd')
      (LE: gf <6= gf'):
  @gcpn5 gf' bnd' r rg e0 e1 e2 e3 e4.
Proof.
  destruct IN. constructor.
  eapply cpn5_mon; [| intros; right; eapply PR].
  ubase.
  eapply fcpn5_mon_bot, LE; [|apply MON|apply MON'|apply BASE|apply BASE'].
  eapply MON, cpn5_cpn; [|apply MON|apply BASE].
  eapply (compat5_compat (cpn5_compat MON BASE)).
  eapply cpn5_mon. apply IN.
  intros. destruct PR. contradiction. apply H.
Qed.

End WCompanion5.

Hint Resolve gcpn5_base : paco.
Hint Resolve gcpn5_step : paco.

