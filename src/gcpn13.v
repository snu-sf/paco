Require Import paco13 pcpn13 pcpntac.
Set Implicit Arguments.

Section GeneralizedCompanion13.

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

Local Notation rel := (rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12).

Section GeneralizedCompanion13_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone13 gf.

Inductive gcpn13 (r rg : rel) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : Prop :=
| gcpn13_intro (IN: ucpn13 gf (r \13/ pcpn13 gf rg) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)
.

Lemma gcpn13_mon r r' rg rg' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12
      (IN: @gcpn13 r rg x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)
      (LEr: r <13= r')
      (LErg: rg <13= rg'):
  @gcpn13 r' rg' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12.
Proof.
  destruct IN. constructor.
  eapply ucpn13_mon. apply IN. intros.
  destruct PR. left. apply LEr, H. right.
  eapply pcpn13_mon. apply H. apply LErg.
Qed.

Lemma gcpn13_init r: gcpn13 r r <13= ucpn13 gf r.
Proof.
  intros. ucpn. destruct PR.
  eapply ucpn13_mon; [apply IN|].
  intros. destruct PR.
  - ubase. apply H.
  - uunfold H. ustep. apply H.
Qed.

Lemma gcpn13_final r rg: ucpn13 gf r <13= gcpn13 r rg.
Proof.
  constructor. eapply ucpn13_mon. apply PR.
  intros. left. apply PR0.
Qed.

Lemma gcpn13_unfold:
  gcpn13 bot13 bot13 <13= gf (gcpn13 bot13 bot13).
Proof.
  intros. destruct PR. destruct IN.
  - uunfold H. eapply gf_mon. apply H.
    intros. econstructor. apply PR.
  - eapply gf_mon; [| intros; econstructor; right; apply PR].
    eapply (dcompat13_compat (dcpn13_compat gf_mon)).
    eapply dcpn13_mon. apply H.
    intros. destruct PR; try contradiction.
    uunfold H0. eapply gf_mon. apply H0.
    intros. right.
    apply pcpn13_final, ucpn13_init. apply gf_mon. apply PR.
Qed.

Lemma gcpn13_base r rg:
  r <13= gcpn13 r rg.
Proof.
  intros. constructor. ubase. left. apply PR.
Qed.

Lemma gcpn13_step r rg:
  gf (gcpn13 rg rg) <13= gcpn13 r rg.
Proof.
  intros. constructor. ubase. right. ustep.
  eapply gf_mon. apply PR.
  intros. destruct PR0.
  apply ucpn13_ucpn. apply gf_mon.
  eapply ucpn13_mon. apply IN.
  intros. destruct PR0.
  - ubase. apply H.
  - left. apply H.
Qed.

Lemma gcpn13_ucpn r rg:
  ucpn13 gf (gcpn13 r rg) <13= gcpn13 r rg.
Proof.
  intros. constructor. ucpn.
  eapply ucpn13_mon. apply PR.
  intros. destruct PR0. apply IN.
Qed.

Lemma gcpn13_clo r rg
      clo (LE: clo <14= ucpn13 gf):
  clo (gcpn13 r rg) <13= gcpn13 r rg.
Proof.
  intros. apply gcpn13_ucpn, LE, PR.
Qed.

(*
  Fixpoint theorem of gcpn13
 *)

Lemma gcpn13_cofix: forall
    r rg (LE: r <13= rg)
    l (OBG: forall rr (INC: rg <13= rr) (CIH: l <13= rr), l <13= gcpn13 r rr),
  l <13= gcpn13 r rg.
Proof.
Admitted.

End GeneralizedCompanion13_main.

Lemma gcpn13_mon_bot (gf gf': rel -> rel) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 r rg
      (IN: @gcpn13 gf bot13 bot13 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)
      (MON: monotone13 gf)
      (MON': monotone13 gf')
      (LE: gf <14= gf'):
  @gcpn13 gf' r rg x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12.
Proof.
  destruct IN. constructor.
  eapply ucpn13_mon; [| intros; right; eapply PR].
  ubase.
  eapply pcpn13_mon_bot, LE; [|apply MON].
  ustep.
  eapply MON, ucpn13_ucpn, MON.
  eapply ucpn13_compat; [apply MON|].
  eapply ucpn13_mon. apply IN.
  intros. destruct PR. contradiction. uunfold H. apply H.
Qed.

End GeneralizedCompanion13.

Hint Resolve gcpn13_base : paco.
Hint Resolve gcpn13_step : paco.

