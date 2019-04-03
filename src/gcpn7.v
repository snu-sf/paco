Require Import paco7 cpn7 cpntac.
Set Implicit Arguments.

Section WCompanion7.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.

Local Notation rel := (rel7 T0 T1 T2 T3 T4 T5 T6).

Section WCompanion7_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone7 gf.

Variable bnd: rel -> rel.
Hypothesis bnd_compat : compatible_bound7 gf bnd.

Inductive gcpn7 (r rg : rel) e0 e1 e2 e3 e4 e5 e6 : Prop :=
| gcpn7_intro (IN: cpn7 gf bnd (r \7/ fcpn7 gf bnd rg) e0 e1 e2 e3 e4 e5 e6)
.              

Lemma gcpn7_mon r r' rg rg' e0 e1 e2 e3 e4 e5 e6
      (IN: @gcpn7 r rg e0 e1 e2 e3 e4 e5 e6)
      (LEr: r <7= r')
      (LErg: rg <7= rg'):
  @gcpn7 r' rg' e0 e1 e2 e3 e4 e5 e6.
Proof.
  destruct IN. constructor.
  eapply cpn7_mon. apply IN. intros.
  destruct PR. left. apply LEr, H. right.
  eapply fcpn7_mon. apply gf_mon. apply H. apply LErg.
Qed.

Lemma gcpn7_init r: gcpn7 r r <7= cpn7 gf bnd r.
Proof.
  intros. destruct PR.
  ucpn.
  eapply cpn7_mon; [apply IN|].
  intros. destruct PR.
  - ubase. apply H.
  - ustep. apply H.
Qed.

Lemma gcpn7_final r rg: cpn7 gf bnd r <7= gcpn7 r rg.
Proof.
  constructor. eapply cpn7_mon. apply PR.
  intros. left. apply PR0.
Qed.

Lemma gcpn7_unfold:
  gcpn7 bot7 bot7 <7= gf (gcpn7 bot7 bot7).
Proof.
  intros. apply gcpn7_init in PR. uunfold PR.
  eapply gf_mon; [apply PR|].
  intros. apply gcpn7_final. apply PR0.
Qed.

Lemma gcpn7_base r rg:
  r <7= gcpn7 r rg.
Proof.
  intros. constructor. ubase. left. apply PR.
Qed.

Lemma gcpn7_bound r rg:
  bnd r <7= gcpn7 r rg.
Proof.
  intros. econstructor. apply cpn7_bound. apply bnd_compat.
  eapply cbound7_mon.
  - apply bnd_compat.
  - apply PR.
  - intros. left. apply PR0.
Qed.

Lemma gcpn7_step r rg:
  gf (gcpn7 rg rg) <7= gcpn7 r rg.
Proof.
  intros. constructor. ubase. right.
  eapply gf_mon. apply PR.
  intros. apply gcpn7_init. apply PR0.
Qed.

Lemma gcpn7_cpn r rg:
  cpn7 gf bnd (gcpn7 r rg) <7= gcpn7 r rg.
Proof.
  intros. constructor. ucpn.
  eapply cpn7_mon. apply PR.
  intros. destruct PR0. apply IN.
Qed.

Lemma gcpn7_clo r rg
      clo (LE: clo <8= cpn7 gf bnd):
  clo (gcpn7 r rg) <7= gcpn7 r rg.
Proof.
  intros. apply gcpn7_cpn, LE, PR.
Qed.

(*
  Fixpoint theorem of gcpn7
 *)

Definition gcut7 (x y z: rel) : rel := fun e0 e1 e2 e3 e4 e5 e6 => y <7= z /\ x e0 e1 e2 e3 e4 e5 e6.

Definition gfixF7 (r rg z: rel) : rel := gcpn7 r (rg \7/ z).

Definition gfix7 (r rg: rel) : rel := cpn7 (gfixF7 r rg) bot8 bot7.

Lemma gfixF7_mon r rg:
  monotone7 (gfixF7 r rg).
Proof.
  red; intros.
  eapply gcpn7_mon. apply IN. intros. apply PR.
  intros. destruct PR. left. apply H. right. apply LE, H.
Qed.

Local Hint Resolve gfixF7_mon.

Lemma gcut7_mon x y : monotone7 (gcut7 x y).
Proof.
  repeat red. intros. destruct IN. split.
  - intros. apply LE, H, PR.
  - apply H0.
Qed.

Lemma gcut7_wcomp r rg (LE: r <7= rg) :
  wcompatible7 gf bnd (gcut7 (gfix7 r rg) rg).
Proof.
  econstructor; [apply gcut7_mon| |].
  { intros.
    destruct PR as [LEz FIX].
    uunfold FIX.
    eapply gf_mon, rclo7_cpn.
    apply cpn7_compat; [apply gf_mon|apply bnd_compat|].
    eapply cpn7_mon; [apply FIX|]. clear x0 x1 x2 x3 x4 x5 x6 FIX; intros.

    destruct PR as [PR | PR].
    - apply LE in PR. apply LEz in PR.
      eapply gf_mon. apply PR.
      intros. apply rclo7_base. apply PR0.
    - eapply gf_mon; [apply PR|]. clear x0 x1 x2 x3 x4 x5 x6 PR; intros.
      eapply rclo7_cpn.
      eapply cpn7_mon. apply PR. clear x0 x1 x2 x3 x4 x5 x6 PR; intros.
      destruct PR as [PR | PR].
      + apply rclo7_step. eapply gf_mon. apply LEz, PR.
        intros. apply rclo7_base, PR0.
      + apply rclo7_clo. split.
        * intros. apply rclo7_step.
          eapply gf_mon. apply LEz. apply PR0.
          intros. apply rclo7_base. apply PR1.
        * apply PR.
  }
  { intros. apply (cbound7_distr bnd_compat) in PR.
    destruct PR, IN.
    uunfold H0. destruct H0. specialize (PTW _ IN).
    eapply (compat7_bound (cpn7_compat gf_mon bnd_compat)) in PTW.
    destruct PTW as [BND|BND].
    - apply (cbound7_distr bnd_compat) in BND. destruct BND.
      destruct IN0.
      + left. apply PTW, H, LE, H0.
      + specialize (PTW _ H0).
        apply (cbound7_compat bnd_compat) in PTW.
        right. eapply gf_mon. apply PTW.
        intros. apply rclo7_cpn, cpn7_bound; [apply bnd_compat|].
        eapply cbound7_mon. apply bnd_compat. apply PR.
        intros. apply rclo7_cpn.
        eapply cpn7_mon. apply PR0.
        intros. destruct PR1.
        * apply rclo7_base. apply H, H1.
        * apply rclo7_clo. econstructor; [|apply H1].
          intros. apply rclo7_base. apply H, PR1.
    - right. eapply gf_mon. apply BND.
      intros. apply rclo7_cpn.
      eapply cpn7_mon. apply PR.
      intros. destruct PR0.
      + apply rclo7_base. apply H, LE, H0.
      + apply rclo7_step.
        eapply gf_mon. apply H0.
        intros. apply rclo7_cpn.
        eapply cpn7_mon. apply PR0.
        intros. destruct PR1.
        * apply rclo7_base. apply H, H1.
        * apply rclo7_clo. econstructor; [|apply H1].
          intros. apply rclo7_base. apply H, PR1.
  }
Qed.

Lemma gfix7_le_cpn r rg (LE: r <7= rg) :
  gfix7 r rg <7= cpn7 gf bnd rg.
Proof.
  intros. eexists.
  - apply wcompat7_compat, gcut7_wcomp. apply gf_mon. apply bnd_compat. apply LE.
  - apply rclo7_clo. split.
    + intros. apply rclo7_base. apply PR0.
    + apply PR.
Qed.

Lemma gfix7_le_gcpn r rg (LE: r <7= rg):
  gfix7 r rg <7= gcpn7 r rg.
Proof.
  (*
    fix
    =
    c(r + gc(rg + fix))
    <=
    c(r + gc(rg + c(rg)))  (by Lemma fix7_le_cpn)
    <=
    c(r + gc(rg))
   *)
  
  intros. uunfold PR.
  destruct PR. constructor.
  eapply cpn7_mon. apply IN. intros.
  destruct PR. left; apply H. right.
  eapply gf_mon.  apply H. intros.
  ucpn.
  eapply cpn7_mon. apply PR. intros.
  destruct PR0.
  - ubase. apply H0.
  - eapply gfix7_le_cpn. apply LE. apply H0.
Qed.

Lemma gcpn7_cofix: forall
    r rg (LE: r <7= rg)
    l (OBG: forall rr (INC: rg <7= rr) (CIH: l <7= rr), l <7= gcpn7 r rr),
  l <7= gcpn7 r rg.
Proof.
  intros. apply gfix7_le_gcpn. apply LE.
  eapply cpn7_algebra, PR. apply gfixF7_mon. apply cbound7_bot.
  intros. eapply OBG; intros.
  - left. apply PR1.
  - right. apply PR1.
  - apply PR0.
Qed.

End WCompanion7_main.

Lemma gcpn7_mon_bot bnd bnd' (gf gf': rel -> rel) e0 e1 e2 e3 e4 e5 e6 r rg
      (IN: @gcpn7 gf bnd bot7 bot7 e0 e1 e2 e3 e4 e5 e6)
      (MON: monotone7 gf)
      (MON': monotone7 gf')
      (BASE: compatible_bound7 gf bnd)
      (BASE': compatible_bound7 gf' bnd')
      (LE: gf <8= gf'):
  @gcpn7 gf' bnd' r rg e0 e1 e2 e3 e4 e5 e6.
Proof.
  destruct IN. constructor.
  eapply cpn7_mon; [| intros; right; eapply PR].
  ubase.
  eapply fcpn7_mon_bot, LE; [|apply MON|apply MON'|apply BASE|apply BASE'].
  eapply MON, cpn7_cpn; [|apply MON|apply BASE].
  eapply (compat7_compat (cpn7_compat MON BASE)).
  eapply cpn7_mon. apply IN.
  intros. destruct PR. contradiction. apply H.
Qed.

End WCompanion7.

Hint Resolve gcpn7_base : paco.
Hint Resolve gcpn7_step : paco.

