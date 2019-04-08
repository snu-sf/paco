Require Import paco10 pcpn10 pcpntac.
Set Implicit Arguments.

Section GeneralizedCompanion10.

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

Local Notation rel := (rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9).

Section GeneralizedCompanion10_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone10 gf.

Inductive gcpn10 (r rg : rel) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Prop :=
| gcpn10_intro (IN: ucpn10 gf (r \10/ pcpn10 gf rg) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)
.

Lemma gcpn10_mon r r' rg rg' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9
      (IN: @gcpn10 r rg x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)
      (LEr: r <10= r')
      (LErg: rg <10= rg'):
  @gcpn10 r' rg' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9.
Proof.
  destruct IN. constructor.
  eapply ucpn10_mon. apply IN. intros.
  destruct PR. left. apply LEr, H. right.
  eapply pcpn10_mon. apply H. apply LErg.
Qed.

Lemma gcpn10_init r: gcpn10 r r <10= ucpn10 gf r.
Proof.
  intros. ucpn. destruct PR.
  eapply ucpn10_mon; [apply IN|].
  intros. destruct PR.
  - ubase. apply H.
  - uunfold H. ustep. apply H.
Qed.

Lemma gcpn10_final r rg: ucpn10 gf r <10= gcpn10 r rg.
Proof.
  constructor. eapply ucpn10_mon. apply PR.
  intros. left. apply PR0.
Qed.

Lemma gcpn10_unfold:
  gcpn10 bot10 bot10 <10= gf (gcpn10 bot10 bot10).
Proof.
  intros. destruct PR. destruct IN.
  - uunfold H. eapply gf_mon. apply H.
    intros. econstructor. apply PR.
  - eapply gf_mon; [| intros; econstructor; right; apply PR].
    eapply (dcompat10_compat (dcpn10_compat gf_mon)).
    eapply dcpn10_mon. apply H.
    intros. destruct PR; try contradiction.
    uunfold H0. eapply gf_mon. apply H0.
    intros. right.
    apply pcpn10_final, ucpn10_init. apply gf_mon. apply PR.
Qed.

Lemma gcpn10_base r rg:
  r <10= gcpn10 r rg.
Proof.
  intros. constructor. ubase. left. apply PR.
Qed.

Lemma gcpn10_step r rg:
  gf (gcpn10 rg rg) <10= gcpn10 r rg.
Proof.
  intros. constructor. ubase. right. ustep.
  eapply gf_mon. apply PR.
  intros. destruct PR0.
  apply ucpn10_ucpn. apply gf_mon.
  eapply ucpn10_mon. apply IN.
  intros. destruct PR0.
  - ubase. apply H.
  - left. apply H.
Qed.

Lemma gcpn10_ucpn r rg:
  ucpn10 gf (gcpn10 r rg) <10= gcpn10 r rg.
Proof.
  intros. constructor. ucpn.
  eapply ucpn10_mon. apply PR.
  intros. destruct PR0. apply IN.
Qed.

Lemma gcpn10_clo r rg
      clo (LE: clo <11= ucpn10 gf):
  clo (gcpn10 r rg) <10= gcpn10 r rg.
Proof.
  intros. apply gcpn10_ucpn, LE, PR.
Qed.

(*
  Fixpoint theorem of gcpn10
 *)

Lemma gcpn10_cofix: forall
    r rg (LE: r <10= rg)
    l (OBG: forall rr (INC: rg <10= rr) (CIH: l <10= rr), l <10= gcpn10 r rr),
  l <10= gcpn10 r rg.
Proof.
Admitted.

End GeneralizedCompanion10_main.

Lemma gcpn10_mon_bot (gf gf': rel -> rel) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 r rg
      (IN: @gcpn10 gf bot10 bot10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)
      (MON: monotone10 gf)
      (MON': monotone10 gf')
      (LE: gf <11= gf'):
  @gcpn10 gf' r rg x0 x1 x2 x3 x4 x5 x6 x7 x8 x9.
Proof.
  destruct IN. constructor.
  eapply ucpn10_mon; [| intros; right; eapply PR].
  ubase.
  eapply pcpn10_mon_bot, LE; [|apply MON].
  ustep.
  eapply MON, ucpn10_ucpn, MON.
  eapply ucpn10_compat; [apply MON|].
  eapply ucpn10_mon. apply IN.
  intros. destruct PR. contradiction. uunfold H. apply H.
Qed.

End GeneralizedCompanion10.

Hint Resolve gcpn10_base : paco.
Hint Resolve gcpn10_step : paco.

