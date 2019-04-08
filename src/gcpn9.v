Require Import paco9 pcpn9 pcpntac.
Set Implicit Arguments.

Section GeneralizedCompanion9.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
Variable T7 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5), Type.
Variable T8 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6), Type.

Local Notation rel := (rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8).

Section GeneralizedCompanion9_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone9 gf.

Inductive gcpn9 (r rg : rel) x0 x1 x2 x3 x4 x5 x6 x7 x8 : Prop :=
| gcpn9_intro (IN: ucpn9 gf (r \9/ pcpn9 gf rg) x0 x1 x2 x3 x4 x5 x6 x7 x8)
.

Lemma gcpn9_mon r r' rg rg' x0 x1 x2 x3 x4 x5 x6 x7 x8
      (IN: @gcpn9 r rg x0 x1 x2 x3 x4 x5 x6 x7 x8)
      (LEr: r <9= r')
      (LErg: rg <9= rg'):
  @gcpn9 r' rg' x0 x1 x2 x3 x4 x5 x6 x7 x8.
Proof.
  destruct IN. constructor.
  eapply ucpn9_mon. apply IN. intros.
  destruct PR. left. apply LEr, H. right.
  eapply pcpn9_mon. apply H. apply LErg.
Qed.

Lemma gcpn9_init r: gcpn9 r r <9= ucpn9 gf r.
Proof.
  intros. ucpn. destruct PR.
  eapply ucpn9_mon; [apply IN|].
  intros. destruct PR.
  - ubase. apply H.
  - uunfold H. ustep. apply H.
Qed.

Lemma gcpn9_final r rg: ucpn9 gf r <9= gcpn9 r rg.
Proof.
  constructor. eapply ucpn9_mon. apply PR.
  intros. left. apply PR0.
Qed.

Lemma gcpn9_unfold:
  gcpn9 bot9 bot9 <9= gf (gcpn9 bot9 bot9).
Proof.
  intros. destruct PR. destruct IN.
  - uunfold H. eapply gf_mon. apply H.
    intros. econstructor. apply PR.
  - eapply gf_mon; [| intros; econstructor; right; apply PR].
    eapply (dcompat9_compat (dcpn9_compat gf_mon)).
    eapply dcpn9_mon. apply H.
    intros. destruct PR; try contradiction.
    uunfold H0. eapply gf_mon. apply H0.
    intros. right.
    apply pcpn9_final, ucpn9_init. apply gf_mon. apply PR.
Qed.

Lemma gcpn9_base r rg:
  r <9= gcpn9 r rg.
Proof.
  intros. constructor. ubase. left. apply PR.
Qed.

Lemma gcpn9_step r rg:
  gf (gcpn9 rg rg) <9= gcpn9 r rg.
Proof.
  intros. constructor. ubase. right. ustep.
  eapply gf_mon. apply PR.
  intros. destruct PR0.
  apply ucpn9_ucpn. apply gf_mon.
  eapply ucpn9_mon. apply IN.
  intros. destruct PR0.
  - ubase. apply H.
  - left. apply H.
Qed.

Lemma gcpn9_ucpn r rg:
  ucpn9 gf (gcpn9 r rg) <9= gcpn9 r rg.
Proof.
  intros. constructor. ucpn.
  eapply ucpn9_mon. apply PR.
  intros. destruct PR0. apply IN.
Qed.

Lemma gcpn9_clo r rg
      clo (LE: clo <10= ucpn9 gf):
  clo (gcpn9 r rg) <9= gcpn9 r rg.
Proof.
  intros. apply gcpn9_ucpn, LE, PR.
Qed.

(*
  Fixpoint theorem of gcpn9
 *)

Lemma gcpn9_cofix: forall
    r rg (LE: r <9= rg)
    l (OBG: forall rr (INC: rg <9= rr) (CIH: l <9= rr), l <9= gcpn9 r rr),
  l <9= gcpn9 r rg.
Proof.
Admitted.

End GeneralizedCompanion9_main.

Lemma gcpn9_mon_bot (gf gf': rel -> rel) x0 x1 x2 x3 x4 x5 x6 x7 x8 r rg
      (IN: @gcpn9 gf bot9 bot9 x0 x1 x2 x3 x4 x5 x6 x7 x8)
      (MON: monotone9 gf)
      (MON': monotone9 gf')
      (LE: gf <10= gf'):
  @gcpn9 gf' r rg x0 x1 x2 x3 x4 x5 x6 x7 x8.
Proof.
  destruct IN. constructor.
  eapply ucpn9_mon; [| intros; right; eapply PR].
  ubase.
  eapply pcpn9_mon_bot, LE; [|apply MON].
  ustep.
  eapply MON, ucpn9_ucpn, MON.
  eapply ucpn9_compat; [apply MON|].
  eapply ucpn9_mon. apply IN.
  intros. destruct PR. contradiction. uunfold H. apply H.
Qed.

End GeneralizedCompanion9.

Hint Resolve gcpn9_base : paco.
Hint Resolve gcpn9_step : paco.

