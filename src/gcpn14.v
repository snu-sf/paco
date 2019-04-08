Require Import paco14 pcpn14 pcpntac.
Set Implicit Arguments.

Section GeneralizedCompanion14.

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

Local Notation rel := (rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13).

Section GeneralizedCompanion14_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone14 gf.

Inductive gcpn14 (r rg : rel) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : Prop :=
| gcpn14_intro (IN: ucpn14 gf (r \14/ pcpn14 gf rg) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13)
.

Lemma gcpn14_mon r r' rg rg' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13
      (IN: @gcpn14 r rg x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13)
      (LEr: r <14= r')
      (LErg: rg <14= rg'):
  @gcpn14 r' rg' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13.
Proof.
  destruct IN. constructor.
  eapply ucpn14_mon. apply IN. intros.
  destruct PR. left. apply LEr, H. right.
  eapply pcpn14_mon. apply H. apply LErg.
Qed.

Lemma gcpn14_init r: gcpn14 r r <14= ucpn14 gf r.
Proof.
  intros. ucpn. destruct PR.
  eapply ucpn14_mon; [apply IN|].
  intros. destruct PR.
  - ubase. apply H.
  - uunfold H. ustep. apply H.
Qed.

Lemma gcpn14_final r rg: ucpn14 gf r <14= gcpn14 r rg.
Proof.
  constructor. eapply ucpn14_mon. apply PR.
  intros. left. apply PR0.
Qed.

Lemma gcpn14_unfold:
  gcpn14 bot14 bot14 <14= gf (gcpn14 bot14 bot14).
Proof.
  intros. destruct PR. destruct IN.
  - uunfold H. eapply gf_mon. apply H.
    intros. econstructor. apply PR.
  - eapply gf_mon; [| intros; econstructor; right; apply PR].
    eapply (dcompat14_compat (dcpn14_compat gf_mon)).
    eapply dcpn14_mon. apply H.
    intros. destruct PR; try contradiction.
    uunfold H0. eapply gf_mon. apply H0.
    intros. right.
    apply pcpn14_final, ucpn14_init. apply gf_mon. apply PR.
Qed.

Lemma gcpn14_base r rg:
  r <14= gcpn14 r rg.
Proof.
  intros. constructor. ubase. left. apply PR.
Qed.

Lemma gcpn14_step r rg:
  gf (gcpn14 rg rg) <14= gcpn14 r rg.
Proof.
  intros. constructor. ubase. right. ustep.
  eapply gf_mon. apply PR.
  intros. destruct PR0.
  apply ucpn14_ucpn. apply gf_mon.
  eapply ucpn14_mon. apply IN.
  intros. destruct PR0.
  - ubase. apply H.
  - left. apply H.
Qed.

Lemma gcpn14_ucpn r rg:
  ucpn14 gf (gcpn14 r rg) <14= gcpn14 r rg.
Proof.
  intros. constructor. ucpn.
  eapply ucpn14_mon. apply PR.
  intros. destruct PR0. apply IN.
Qed.

Lemma gcpn14_clo r rg
      clo (LE: clo <15= ucpn14 gf):
  clo (gcpn14 r rg) <14= gcpn14 r rg.
Proof.
  intros. apply gcpn14_ucpn, LE, PR.
Qed.

(*
  Fixpoint theorem of gcpn14
 *)

Lemma gcpn14_cofix: forall
    r rg (LE: r <14= rg)
    l (OBG: forall rr (INC: rg <14= rr) (CIH: l <14= rr), l <14= gcpn14 r rr),
  l <14= gcpn14 r rg.
Proof.
Admitted.

End GeneralizedCompanion14_main.

Lemma gcpn14_mon_bot (gf gf': rel -> rel) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 r rg
      (IN: @gcpn14 gf bot14 bot14 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13)
      (MON: monotone14 gf)
      (MON': monotone14 gf')
      (LE: gf <15= gf'):
  @gcpn14 gf' r rg x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13.
Proof.
  destruct IN. constructor.
  eapply ucpn14_mon; [| intros; right; eapply PR].
  ubase.
  eapply pcpn14_mon_bot, LE; [|apply MON].
  ustep.
  eapply MON, ucpn14_ucpn, MON.
  eapply ucpn14_compat; [apply MON|].
  eapply ucpn14_mon. apply IN.
  intros. destruct PR. contradiction. uunfold H. apply H.
Qed.

End GeneralizedCompanion14.

Hint Resolve gcpn14_base : paco.
Hint Resolve gcpn14_step : paco.

