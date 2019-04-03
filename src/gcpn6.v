Require Import paco6 cpn6 cpntac.
Set Implicit Arguments.

Section WCompanion6.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.

Local Notation rel := (rel6 T0 T1 T2 T3 T4 T5).

Section WCompanion6_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone6 gf.

Variable bnd: rel -> rel.
Hypothesis bnd_compat : compatible_bound6 gf bnd.

Inductive gcpn6 (r rg : rel) e0 e1 e2 e3 e4 e5 : Prop :=
| gcpn6_intro (IN: cpn6 gf bnd (r \6/ fcpn6 gf bnd rg) e0 e1 e2 e3 e4 e5)
.              

Lemma gcpn6_mon r r' rg rg' e0 e1 e2 e3 e4 e5
      (IN: @gcpn6 r rg e0 e1 e2 e3 e4 e5)
      (LEr: r <6= r')
      (LErg: rg <6= rg'):
  @gcpn6 r' rg' e0 e1 e2 e3 e4 e5.
Proof.
  destruct IN. constructor.
  eapply cpn6_mon. apply IN. intros.
  destruct PR. left. apply LEr, H. right.
  eapply fcpn6_mon. apply gf_mon. apply H. apply LErg.
Qed.

Lemma gcpn6_init r: gcpn6 r r <6= cpn6 gf bnd r.
Proof.
  intros. destruct PR.
  ucpn.
  eapply cpn6_mon; [apply IN|].
  intros. destruct PR.
  - ubase. apply H.
  - ustep. apply H.
Qed.

Lemma gcpn6_final r rg: cpn6 gf bnd r <6= gcpn6 r rg.
Proof.
  constructor. eapply cpn6_mon. apply PR.
  intros. left. apply PR0.
Qed.

Lemma gcpn6_unfold:
  gcpn6 bot6 bot6 <6= gf (gcpn6 bot6 bot6).
Proof.
  intros. apply gcpn6_init in PR. uunfold PR.
  eapply gf_mon; [apply PR|].
  intros. apply gcpn6_final. apply PR0.
Qed.

Lemma gcpn6_base r rg:
  r <6= gcpn6 r rg.
Proof.
  intros. constructor. ubase. left. apply PR.
Qed.

Lemma gcpn6_bound r rg:
  bnd r <6= gcpn6 r rg.
Proof.
  intros. econstructor. apply cpn6_bound. apply bnd_compat.
  eapply cbound6_mon.
  - apply bnd_compat.
  - apply PR.
  - intros. left. apply PR0.
Qed.

Lemma gcpn6_step r rg:
  gf (gcpn6 rg rg) <6= gcpn6 r rg.
Proof.
  intros. constructor. ubase. right.
  eapply gf_mon. apply PR.
  intros. apply gcpn6_init. apply PR0.
Qed.

Lemma gcpn6_cpn r rg:
  cpn6 gf bnd (gcpn6 r rg) <6= gcpn6 r rg.
Proof.
  intros. constructor. ucpn.
  eapply cpn6_mon. apply PR.
  intros. destruct PR0. apply IN.
Qed.

Lemma gcpn6_clo r rg
      clo (LE: clo <7= cpn6 gf bnd):
  clo (gcpn6 r rg) <6= gcpn6 r rg.
Proof.
  intros. apply gcpn6_cpn, LE, PR.
Qed.

(*
  Fixpoint theorem of gcpn6
 *)

Definition gcut6 (x y z: rel) : rel := fun e0 e1 e2 e3 e4 e5 => y <6= z /\ x e0 e1 e2 e3 e4 e5.

Definition gfixF6 (r rg z: rel) : rel := gcpn6 r (rg \6/ z).

Definition gfix6 (r rg: rel) : rel := cpn6 (gfixF6 r rg) bot7 bot6.

Lemma gfixF6_mon r rg:
  monotone6 (gfixF6 r rg).
Proof.
  red; intros.
  eapply gcpn6_mon. apply IN. intros. apply PR.
  intros. destruct PR. left. apply H. right. apply LE, H.
Qed.

Local Hint Resolve gfixF6_mon.

Lemma gcut6_mon x y : monotone6 (gcut6 x y).
Proof.
  repeat red. intros. destruct IN. split.
  - intros. apply LE, H, PR.
  - apply H0.
Qed.

Lemma gcut6_wcomp r rg (LE: r <6= rg) :
  wcompatible6 gf bnd (gcut6 (gfix6 r rg) rg).
Proof.
  econstructor; [apply gcut6_mon| |].
  { intros.
    destruct PR as [LEz FIX].
    uunfold FIX.
    eapply gf_mon, rclo6_cpn.
    apply cpn6_compat; [apply gf_mon|apply bnd_compat|].
    eapply cpn6_mon; [apply FIX|]. clear x0 x1 x2 x3 x4 x5 FIX; intros.

    destruct PR as [PR | PR].
    - apply LE in PR. apply LEz in PR.
      eapply gf_mon. apply PR.
      intros. apply rclo6_base. apply PR0.
    - eapply gf_mon; [apply PR|]. clear x0 x1 x2 x3 x4 x5 PR; intros.
      eapply rclo6_cpn.
      eapply cpn6_mon. apply PR. clear x0 x1 x2 x3 x4 x5 PR; intros.
      destruct PR as [PR | PR].
      + apply rclo6_step. eapply gf_mon. apply LEz, PR.
        intros. apply rclo6_base, PR0.
      + apply rclo6_clo. split.
        * intros. apply rclo6_step.
          eapply gf_mon. apply LEz. apply PR0.
          intros. apply rclo6_base. apply PR1.
        * apply PR.
  }
  { intros. apply (cbound6_distr bnd_compat) in PR.
    destruct PR, IN.
    uunfold H0. destruct H0. specialize (PTW _ IN).
    eapply (compat6_bound (cpn6_compat gf_mon bnd_compat)) in PTW.
    destruct PTW as [BND|BND].
    - apply (cbound6_distr bnd_compat) in BND. destruct BND.
      destruct IN0.
      + left. apply PTW, H, LE, H0.
      + specialize (PTW _ H0).
        apply (cbound6_compat bnd_compat) in PTW.
        right. eapply gf_mon. apply PTW.
        intros. apply rclo6_cpn, cpn6_bound; [apply bnd_compat|].
        eapply cbound6_mon. apply bnd_compat. apply PR.
        intros. apply rclo6_cpn.
        eapply cpn6_mon. apply PR0.
        intros. destruct PR1.
        * apply rclo6_base. apply H, H1.
        * apply rclo6_clo. econstructor; [|apply H1].
          intros. apply rclo6_base. apply H, PR1.
    - right. eapply gf_mon. apply BND.
      intros. apply rclo6_cpn.
      eapply cpn6_mon. apply PR.
      intros. destruct PR0.
      + apply rclo6_base. apply H, LE, H0.
      + apply rclo6_step.
        eapply gf_mon. apply H0.
        intros. apply rclo6_cpn.
        eapply cpn6_mon. apply PR0.
        intros. destruct PR1.
        * apply rclo6_base. apply H, H1.
        * apply rclo6_clo. econstructor; [|apply H1].
          intros. apply rclo6_base. apply H, PR1.
  }
Qed.

Lemma gfix6_le_cpn r rg (LE: r <6= rg) :
  gfix6 r rg <6= cpn6 gf bnd rg.
Proof.
  intros. eexists.
  - apply wcompat6_compat, gcut6_wcomp. apply gf_mon. apply bnd_compat. apply LE.
  - apply rclo6_clo. split.
    + intros. apply rclo6_base. apply PR0.
    + apply PR.
Qed.

Lemma gfix6_le_gcpn r rg (LE: r <6= rg):
  gfix6 r rg <6= gcpn6 r rg.
Proof.
  (*
    fix
    =
    c(r + gc(rg + fix))
    <=
    c(r + gc(rg + c(rg)))  (by Lemma fix6_le_cpn)
    <=
    c(r + gc(rg))
   *)
  
  intros. uunfold PR.
  destruct PR. constructor.
  eapply cpn6_mon. apply IN. intros.
  destruct PR. left; apply H. right.
  eapply gf_mon.  apply H. intros.
  ucpn.
  eapply cpn6_mon. apply PR. intros.
  destruct PR0.
  - ubase. apply H0.
  - eapply gfix6_le_cpn. apply LE. apply H0.
Qed.

Lemma gcpn6_cofix: forall
    r rg (LE: r <6= rg)
    l (OBG: forall rr (INC: rg <6= rr) (CIH: l <6= rr), l <6= gcpn6 r rr),
  l <6= gcpn6 r rg.
Proof.
  intros. apply gfix6_le_gcpn. apply LE.
  eapply cpn6_algebra, PR. apply gfixF6_mon. apply cbound6_bot.
  intros. eapply OBG; intros.
  - left. apply PR1.
  - right. apply PR1.
  - apply PR0.
Qed.

End WCompanion6_main.

Lemma gcpn6_mon_bot bnd bnd' (gf gf': rel -> rel) e0 e1 e2 e3 e4 e5 r rg
      (IN: @gcpn6 gf bnd bot6 bot6 e0 e1 e2 e3 e4 e5)
      (MON: monotone6 gf)
      (MON': monotone6 gf')
      (BASE: compatible_bound6 gf bnd)
      (BASE': compatible_bound6 gf' bnd')
      (LE: gf <7= gf'):
  @gcpn6 gf' bnd' r rg e0 e1 e2 e3 e4 e5.
Proof.
  destruct IN. constructor.
  eapply cpn6_mon; [| intros; right; eapply PR].
  ubase.
  eapply fcpn6_mon_bot, LE; [|apply MON|apply MON'|apply BASE|apply BASE'].
  eapply MON, cpn6_cpn; [|apply MON|apply BASE].
  eapply (compat6_compat (cpn6_compat MON BASE)).
  eapply cpn6_mon. apply IN.
  intros. destruct PR. contradiction. apply H.
Qed.

End WCompanion6.

Hint Resolve gcpn6_base : paco.
Hint Resolve gcpn6_step : paco.

