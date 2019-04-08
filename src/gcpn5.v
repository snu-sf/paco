Require Import paco5 pcpn5 pcpntac.
Set Implicit Arguments.

Section GeneralizedCompanion5.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.

Local Notation rel := (rel5 T0 T1 T2 T3 T4).

Section GeneralizedCompanion5_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone5 gf.

Inductive gcpn5 (r rg : rel) x0 x1 x2 x3 x4 : Prop :=
| gcpn5_intro (IN: ucpn5 gf (r \5/ pcpn5 gf rg) x0 x1 x2 x3 x4)
.

Lemma gcpn5_mon r r' rg rg' x0 x1 x2 x3 x4
      (IN: @gcpn5 r rg x0 x1 x2 x3 x4)
      (LEr: r <5= r')
      (LErg: rg <5= rg'):
  @gcpn5 r' rg' x0 x1 x2 x3 x4.
Proof.
  destruct IN. constructor.
  eapply ucpn5_mon. apply IN. intros.
  destruct PR. left. apply LEr, H. right.
  eapply pcpn5_mon. apply H. apply LErg.
Qed.

Lemma gcpn5_init r: gcpn5 r r <5= ucpn5 gf r.
Proof.
  intros. ucpn. destruct PR.
  eapply ucpn5_mon; [apply IN|].
  intros. destruct PR.
  - ubase. apply H.
  - uunfold H. ustep. apply H.
Qed.

Lemma gcpn5_final r rg: ucpn5 gf r <5= gcpn5 r rg.
Proof.
  constructor. eapply ucpn5_mon. apply PR.
  intros. left. apply PR0.
Qed.

Lemma gcpn5_unfold:
  gcpn5 bot5 bot5 <5= gf (gcpn5 bot5 bot5).
Proof.
  intros. destruct PR. destruct IN.
  - uunfold H. eapply gf_mon. apply H.
    intros. econstructor. apply PR.
  - eapply gf_mon; [| intros; econstructor; right; apply PR].
    eapply (dcompat5_compat (dcpn5_compat gf_mon)).
    eapply dcpn5_mon. apply H.
    intros. destruct PR; try contradiction.
    uunfold H0. eapply gf_mon. apply H0.
    intros. right.
    apply pcpn5_final, ucpn5_init. apply gf_mon. apply PR.
Qed.

Lemma gcpn5_base r rg:
  r <5= gcpn5 r rg.
Proof.
  intros. constructor. ubase. left. apply PR.
Qed.

Lemma gcpn5_step r rg:
  gf (gcpn5 rg rg) <5= gcpn5 r rg.
Proof.
  intros. constructor. ubase. right. ustep.
  eapply gf_mon. apply PR.
  intros. destruct PR0.
  apply ucpn5_ucpn. apply gf_mon.
  eapply ucpn5_mon. apply IN.
  intros. destruct PR0.
  - ubase. apply H.
  - left. apply H.
Qed.

Lemma gcpn5_ucpn r rg:
  ucpn5 gf (gcpn5 r rg) <5= gcpn5 r rg.
Proof.
  intros. constructor. ucpn.
  eapply ucpn5_mon. apply PR.
  intros. destruct PR0. apply IN.
Qed.

Lemma gcpn5_clo r rg
      clo (LE: clo <6= ucpn5 gf):
  clo (gcpn5 r rg) <5= gcpn5 r rg.
Proof.
  intros. apply gcpn5_ucpn, LE, PR.
Qed.

(*
  Fixpoint theorem of gcpn5
 *)

Lemma gcpn5_cofix: forall
    r rg (LE: r <5= rg)
    l (OBG: forall rr (INC: rg <5= rr) (CIH: l <5= rr), l <5= gcpn5 r rr),
  l <5= gcpn5 r rg.
Proof.
Admitted.

End GeneralizedCompanion5_main.

Lemma gcpn5_mon_bot (gf gf': rel -> rel) x0 x1 x2 x3 x4 r rg
      (IN: @gcpn5 gf bot5 bot5 x0 x1 x2 x3 x4)
      (MON: monotone5 gf)
      (MON': monotone5 gf')
      (LE: gf <6= gf'):
  @gcpn5 gf' r rg x0 x1 x2 x3 x4.
Proof.
  destruct IN. constructor.
  eapply ucpn5_mon; [| intros; right; eapply PR].
  ubase.
  eapply pcpn5_mon_bot, LE; [|apply MON].
  ustep.
  eapply MON, ucpn5_ucpn, MON.
  eapply ucpn5_compat; [apply MON|].
  eapply ucpn5_mon. apply IN.
  intros. destruct PR. contradiction. uunfold H. apply H.
Qed.

End GeneralizedCompanion5.

Hint Resolve gcpn5_base : paco.
Hint Resolve gcpn5_step : paco.

