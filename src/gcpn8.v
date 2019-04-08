Require Import paco8 pcpn8 pcpntac.
Set Implicit Arguments.

Section GeneralizedCompanion8.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
Variable T7 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5), Type.

Local Notation rel := (rel8 T0 T1 T2 T3 T4 T5 T6 T7).

Section GeneralizedCompanion8_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone8 gf.

Inductive gcpn8 (r rg : rel) x0 x1 x2 x3 x4 x5 x6 x7 : Prop :=
| gcpn8_intro (IN: ucpn8 gf (r \8/ pcpn8 gf rg) x0 x1 x2 x3 x4 x5 x6 x7)
.

Lemma gcpn8_mon r r' rg rg' x0 x1 x2 x3 x4 x5 x6 x7
      (IN: @gcpn8 r rg x0 x1 x2 x3 x4 x5 x6 x7)
      (LEr: r <8= r')
      (LErg: rg <8= rg'):
  @gcpn8 r' rg' x0 x1 x2 x3 x4 x5 x6 x7.
Proof.
  destruct IN. constructor.
  eapply ucpn8_mon. apply IN. intros.
  destruct PR. left. apply LEr, H. right.
  eapply pcpn8_mon. apply H. apply LErg.
Qed.

Lemma gcpn8_init r: gcpn8 r r <8= ucpn8 gf r.
Proof.
  intros. ucpn. destruct PR.
  eapply ucpn8_mon; [apply IN|].
  intros. destruct PR.
  - ubase. apply H.
  - uunfold H. ustep. apply H.
Qed.

Lemma gcpn8_final r rg: ucpn8 gf r <8= gcpn8 r rg.
Proof.
  constructor. eapply ucpn8_mon. apply PR.
  intros. left. apply PR0.
Qed.

Lemma gcpn8_unfold:
  gcpn8 bot8 bot8 <8= gf (gcpn8 bot8 bot8).
Proof.
  intros. destruct PR. destruct IN.
  - uunfold H. eapply gf_mon. apply H.
    intros. econstructor. apply PR.
  - eapply gf_mon; [| intros; econstructor; right; apply PR].
    eapply (dcompat8_compat (dcpn8_compat gf_mon)).
    eapply dcpn8_mon. apply H.
    intros. destruct PR; try contradiction.
    uunfold H0. eapply gf_mon. apply H0.
    intros. right.
    apply pcpn8_final, ucpn8_init. apply gf_mon. apply PR.
Qed.

Lemma gcpn8_base r rg:
  r <8= gcpn8 r rg.
Proof.
  intros. constructor. ubase. left. apply PR.
Qed.

Lemma gcpn8_step r rg:
  gf (gcpn8 rg rg) <8= gcpn8 r rg.
Proof.
  intros. constructor. ubase. right. ustep.
  eapply gf_mon. apply PR.
  intros. destruct PR0.
  apply ucpn8_ucpn. apply gf_mon.
  eapply ucpn8_mon. apply IN.
  intros. destruct PR0.
  - ubase. apply H.
  - left. apply H.
Qed.

Lemma gcpn8_ucpn r rg:
  ucpn8 gf (gcpn8 r rg) <8= gcpn8 r rg.
Proof.
  intros. constructor. ucpn.
  eapply ucpn8_mon. apply PR.
  intros. destruct PR0. apply IN.
Qed.

Lemma gcpn8_clo r rg
      clo (LE: clo <9= ucpn8 gf):
  clo (gcpn8 r rg) <8= gcpn8 r rg.
Proof.
  intros. apply gcpn8_ucpn, LE, PR.
Qed.

(*
  Fixpoint theorem of gcpn8
 *)

Lemma gcpn8_cofix: forall
    r rg (LE: r <8= rg)
    l (OBG: forall rr (INC: rg <8= rr) (CIH: l <8= rr), l <8= gcpn8 r rr),
  l <8= gcpn8 r rg.
Proof.
Admitted.

End GeneralizedCompanion8_main.

Lemma gcpn8_mon_bot (gf gf': rel -> rel) x0 x1 x2 x3 x4 x5 x6 x7 r rg
      (IN: @gcpn8 gf bot8 bot8 x0 x1 x2 x3 x4 x5 x6 x7)
      (MON: monotone8 gf)
      (MON': monotone8 gf')
      (LE: gf <9= gf'):
  @gcpn8 gf' r rg x0 x1 x2 x3 x4 x5 x6 x7.
Proof.
  destruct IN. constructor.
  eapply ucpn8_mon; [| intros; right; eapply PR].
  ubase.
  eapply pcpn8_mon_bot, LE; [|apply MON].
  ustep.
  eapply MON, ucpn8_ucpn, MON.
  eapply ucpn8_compat; [apply MON|].
  eapply ucpn8_mon. apply IN.
  intros. destruct PR. contradiction. uunfold H. apply H.
Qed.

End GeneralizedCompanion8.

Hint Resolve gcpn8_base : paco.
Hint Resolve gcpn8_step : paco.

