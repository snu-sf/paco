Require Import paco15 cpn15 cpntac.
Set Implicit Arguments.

Section WCompanion15.

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
Variable T11 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9), Type.
Variable T12 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10), Type.
Variable T13 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) (x12: @T12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11), Type.
Variable T14 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) (x12: @T12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) (x13: @T13 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12), Type.

Local Notation rel := (rel15 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14).

Section WCompanion15_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone15 gf.

Variable bnd: rel -> rel.
Hypothesis bnd_compat : compatible_bound15 gf bnd.

Inductive gcpn15 (r rg : rel) e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 : Prop :=
| gcpn15_intro (IN: cpn15 gf bnd (r \15/ fcpn15 gf bnd rg) e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14)
.              

Lemma gcpn15_mon r r' rg rg' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14
      (IN: @gcpn15 r rg e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14)
      (LEr: r <15= r')
      (LErg: rg <15= rg'):
  @gcpn15 r' rg' e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14.
Proof.
  destruct IN. constructor.
  eapply cpn15_mon. apply IN. intros.
  destruct PR. left. apply LEr, H. right.
  eapply fcpn15_mon. apply gf_mon. apply H. apply LErg.
Qed.

Lemma gcpn15_init r: gcpn15 r r <15= cpn15 gf bnd r.
Proof.
  intros. destruct PR.
  ucpn.
  eapply cpn15_mon; [apply IN|].
  intros. destruct PR.
  - ubase. apply H.
  - ustep. apply H.
Qed.

Lemma gcpn15_final r rg: cpn15 gf bnd r <15= gcpn15 r rg.
Proof.
  constructor. eapply cpn15_mon. apply PR.
  intros. left. apply PR0.
Qed.

Lemma gcpn15_unfold:
  gcpn15 bot15 bot15 <15= gf (gcpn15 bot15 bot15).
Proof.
  intros. apply gcpn15_init in PR. uunfold PR.
  eapply gf_mon; [apply PR|].
  intros. apply gcpn15_final. apply PR0.
Qed.

Lemma gcpn15_base r rg:
  r <15= gcpn15 r rg.
Proof.
  intros. constructor. ubase. left. apply PR.
Qed.

Lemma gcpn15_bound r rg:
  bnd r <15= gcpn15 r rg.
Proof.
  intros. econstructor. apply cpn15_bound. apply bnd_compat.
  eapply cbound15_mon.
  - apply bnd_compat.
  - apply PR.
  - intros. left. apply PR0.
Qed.

Lemma gcpn15_step r rg:
  gf (gcpn15 rg rg) <15= gcpn15 r rg.
Proof.
  intros. constructor. ubase. right.
  eapply gf_mon. apply PR.
  intros. apply gcpn15_init. apply PR0.
Qed.

Lemma gcpn15_cpn r rg:
  cpn15 gf bnd (gcpn15 r rg) <15= gcpn15 r rg.
Proof.
  intros. constructor. ucpn.
  eapply cpn15_mon. apply PR.
  intros. destruct PR0. apply IN.
Qed.

Lemma gcpn15_clo r rg
      clo (LE: clo <16= cpn15 gf bnd):
  clo (gcpn15 r rg) <15= gcpn15 r rg.
Proof.
  intros. apply gcpn15_cpn, LE, PR.
Qed.

(*
  Fixpoint theorem of gcpn15
 *)

Definition gcut15 (x y z: rel) : rel := fun e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 => y <15= z /\ x e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14.

Definition gfixF15 (r rg z: rel) : rel := gcpn15 r (rg \15/ z).

Definition gfix15 (r rg: rel) : rel := cpn15 (gfixF15 r rg) bot16 bot15.

Lemma gfixF15_mon r rg:
  monotone15 (gfixF15 r rg).
Proof.
  red; intros.
  eapply gcpn15_mon. apply IN. intros. apply PR.
  intros. destruct PR. left. apply H. right. apply LE, H.
Qed.

Local Hint Resolve gfixF15_mon.

Lemma gcut15_mon x y : monotone15 (gcut15 x y).
Proof.
  repeat red. intros. destruct IN. split.
  - intros. apply LE, H, PR.
  - apply H0.
Qed.

Lemma gcut15_wcomp r rg (LE: r <15= rg) :
  wcompatible15 gf bnd (gcut15 (gfix15 r rg) rg).
Proof.
  econstructor; [apply gcut15_mon| |].
  { intros.
    destruct PR as [LEz FIX].
    uunfold FIX.
    eapply gf_mon, rclo15_cpn.
    apply cpn15_compat; [apply gf_mon|apply bnd_compat|].
    eapply cpn15_mon; [apply FIX|]. clear x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 FIX; intros.

    destruct PR as [PR | PR].
    - apply LE in PR. apply LEz in PR.
      eapply gf_mon. apply PR.
      intros. apply rclo15_base. apply PR0.
    - eapply gf_mon; [apply PR|]. clear x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 PR; intros.
      eapply rclo15_cpn.
      eapply cpn15_mon. apply PR. clear x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 PR; intros.
      destruct PR as [PR | PR].
      + apply rclo15_step. eapply gf_mon. apply LEz, PR.
        intros. apply rclo15_base, PR0.
      + apply rclo15_clo. split.
        * intros. apply rclo15_step.
          eapply gf_mon. apply LEz. apply PR0.
          intros. apply rclo15_base. apply PR1.
        * apply PR.
  }
  { intros. apply (cbound15_distr bnd_compat) in PR.
    destruct PR, IN.
    uunfold H0. destruct H0. specialize (PTW _ IN).
    eapply (compat15_bound (cpn15_compat gf_mon bnd_compat)) in PTW.
    destruct PTW as [BND|BND].
    - apply (cbound15_distr bnd_compat) in BND. destruct BND.
      destruct IN0.
      + left. apply PTW, H, LE, H0.
      + specialize (PTW _ H0).
        apply (cbound15_compat bnd_compat) in PTW.
        right. eapply gf_mon. apply PTW.
        intros. apply rclo15_cpn, cpn15_bound; [apply bnd_compat|].
        eapply cbound15_mon. apply bnd_compat. apply PR.
        intros. apply rclo15_cpn.
        eapply cpn15_mon. apply PR0.
        intros. destruct PR1.
        * apply rclo15_base. apply H, H1.
        * apply rclo15_clo. econstructor; [|apply H1].
          intros. apply rclo15_base. apply H, PR1.
    - right. eapply gf_mon. apply BND.
      intros. apply rclo15_cpn.
      eapply cpn15_mon. apply PR.
      intros. destruct PR0.
      + apply rclo15_base. apply H, LE, H0.
      + apply rclo15_step.
        eapply gf_mon. apply H0.
        intros. apply rclo15_cpn.
        eapply cpn15_mon. apply PR0.
        intros. destruct PR1.
        * apply rclo15_base. apply H, H1.
        * apply rclo15_clo. econstructor; [|apply H1].
          intros. apply rclo15_base. apply H, PR1.
  }
Qed.

Lemma gfix15_le_cpn r rg (LE: r <15= rg) :
  gfix15 r rg <15= cpn15 gf bnd rg.
Proof.
  intros. eexists.
  - apply wcompat15_compat, gcut15_wcomp. apply gf_mon. apply bnd_compat. apply LE.
  - apply rclo15_clo. split.
    + intros. apply rclo15_base. apply PR0.
    + apply PR.
Qed.

Lemma gfix15_le_gcpn r rg (LE: r <15= rg):
  gfix15 r rg <15= gcpn15 r rg.
Proof.
  (*
    fix
    =
    c(r + gc(rg + fix))
    <=
    c(r + gc(rg + c(rg)))  (by Lemma fix15_le_cpn)
    <=
    c(r + gc(rg))
   *)
  
  intros. uunfold PR.
  destruct PR. constructor.
  eapply cpn15_mon. apply IN. intros.
  destruct PR. left; apply H. right.
  eapply gf_mon.  apply H. intros.
  ucpn.
  eapply cpn15_mon. apply PR. intros.
  destruct PR0.
  - ubase. apply H0.
  - eapply gfix15_le_cpn. apply LE. apply H0.
Qed.

Lemma gcpn15_cofix: forall
    r rg (LE: r <15= rg)
    l (OBG: forall rr (INC: rg <15= rr) (CIH: l <15= rr), l <15= gcpn15 r rr),
  l <15= gcpn15 r rg.
Proof.
  intros. apply gfix15_le_gcpn. apply LE.
  eapply cpn15_algebra, PR. apply gfixF15_mon. apply cbound15_bot.
  intros. eapply OBG; intros.
  - left. apply PR1.
  - right. apply PR1.
  - apply PR0.
Qed.

End WCompanion15_main.

Lemma gcpn15_mon_bot bnd bnd' (gf gf': rel -> rel) e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 r rg
      (IN: @gcpn15 gf bnd bot15 bot15 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14)
      (MON: monotone15 gf)
      (MON': monotone15 gf')
      (BASE: compatible_bound15 gf bnd)
      (BASE': compatible_bound15 gf' bnd')
      (LE: gf <16= gf'):
  @gcpn15 gf' bnd' r rg e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14.
Proof.
  destruct IN. constructor.
  eapply cpn15_mon; [| intros; right; eapply PR].
  ubase.
  eapply fcpn15_mon_bot, LE; [|apply MON|apply MON'|apply BASE|apply BASE'].
  eapply MON, cpn15_cpn; [|apply MON|apply BASE].
  eapply (compat15_compat (cpn15_compat MON BASE)).
  eapply cpn15_mon. apply IN.
  intros. destruct PR. contradiction. apply H.
Qed.

End WCompanion15.

Hint Resolve gcpn15_base : paco.
Hint Resolve gcpn15_step : paco.

