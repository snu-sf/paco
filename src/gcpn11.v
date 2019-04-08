Require Import paco11 pcpn11 pcpntac.
Set Implicit Arguments.

Section GeneralizedCompanion11.

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

Local Notation rel := (rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10).

Section GeneralizedCompanion11_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone11 gf.

Inductive gcpn11 (r rg : rel) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : Prop :=
| gcpn11_intro (IN: ucpn11 gf (r \11/ pcpn11 gf rg) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
.

Lemma gcpn11_mon r r' rg rg' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
      (IN: @gcpn11 r rg x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
      (LEr: r <11= r')
      (LErg: rg <11= rg'):
  @gcpn11 r' rg' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10.
Proof.
  destruct IN. constructor.
  eapply ucpn11_mon. apply IN. intros.
  destruct PR. left. apply LEr, H. right.
  eapply pcpn11_mon. apply H. apply LErg.
Qed.

Lemma gcpn11_init r: gcpn11 r r <11= ucpn11 gf r.
Proof.
  intros. ucpn. destruct PR.
  eapply ucpn11_mon; [apply IN|].
  intros. destruct PR.
  - ubase. apply H.
  - uunfold H. ustep. apply H.
Qed.

Lemma gcpn11_final r rg: ucpn11 gf r <11= gcpn11 r rg.
Proof.
  constructor. eapply ucpn11_mon. apply PR.
  intros. left. apply PR0.
Qed.

Lemma gcpn11_unfold:
  gcpn11 bot11 bot11 <11= gf (gcpn11 bot11 bot11).
Proof.
  intros. destruct PR. destruct IN.
  - uunfold H. eapply gf_mon. apply H.
    intros. econstructor. apply PR.
  - eapply gf_mon; [| intros; econstructor; right; apply PR].
    eapply (dcompat11_compat (dcpn11_compat gf_mon)).
    eapply dcpn11_mon. apply H.
    intros. destruct PR; try contradiction.
    uunfold H0. eapply gf_mon. apply H0.
    intros. right.
    apply pcpn11_final, ucpn11_init. apply gf_mon. apply PR.
Qed.

Lemma gcpn11_base r rg:
  r <11= gcpn11 r rg.
Proof.
  intros. constructor. ubase. left. apply PR.
Qed.

Lemma gcpn11_step r rg:
  gf (gcpn11 rg rg) <11= gcpn11 r rg.
Proof.
  intros. constructor. ubase. right. ustep.
  eapply gf_mon. apply PR.
  intros. destruct PR0.
  apply ucpn11_ucpn. apply gf_mon.
  eapply ucpn11_mon. apply IN.
  intros. destruct PR0.
  - ubase. apply H.
  - left. apply H.
Qed.

Lemma gcpn11_ucpn r rg:
  ucpn11 gf (gcpn11 r rg) <11= gcpn11 r rg.
Proof.
  intros. constructor. ucpn.
  eapply ucpn11_mon. apply PR.
  intros. destruct PR0. apply IN.
Qed.

Lemma gcpn11_clo r rg
      clo (LE: clo <12= ucpn11 gf):
  clo (gcpn11 r rg) <11= gcpn11 r rg.
Proof.
  intros. apply gcpn11_ucpn, LE, PR.
Qed.

(*
  Fixpoint theorem of gcpn11
 *)

Lemma gcpn11_cofix: forall
    r rg (LE: r <11= rg)
    l (OBG: forall rr (INC: rg <11= rr) (CIH: l <11= rr), l <11= gcpn11 r rr),
  l <11= gcpn11 r rg.
Proof.
Admitted.

End GeneralizedCompanion11_main.

Lemma gcpn11_mon_bot (gf gf': rel -> rel) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 r rg
      (IN: @gcpn11 gf bot11 bot11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
      (MON: monotone11 gf)
      (MON': monotone11 gf')
      (LE: gf <12= gf'):
  @gcpn11 gf' r rg x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10.
Proof.
  destruct IN. constructor.
  eapply ucpn11_mon; [| intros; right; eapply PR].
  ubase.
  eapply pcpn11_mon_bot, LE; [|apply MON].
  ustep.
  eapply MON, ucpn11_ucpn, MON.
  eapply ucpn11_compat; [apply MON|].
  eapply ucpn11_mon. apply IN.
  intros. destruct PR. contradiction. uunfold H. apply H.
Qed.

End GeneralizedCompanion11.

Hint Resolve gcpn11_base : paco.
Hint Resolve gcpn11_step : paco.

