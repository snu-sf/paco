Require Import paco7 pcpn7 pcpntac.
Set Implicit Arguments.

Section GeneralizedCompanion7.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.

Local Notation rel := (rel7 T0 T1 T2 T3 T4 T5 T6).

Section GeneralizedCompanion7_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone7 gf.

Inductive gcpn7 (r rg : rel) x0 x1 x2 x3 x4 x5 x6 : Prop :=
| gcpn7_intro (IN: ucpn7 gf (r \7/ pcpn7 gf rg) x0 x1 x2 x3 x4 x5 x6)
.

Lemma gcpn7_mon r r' rg rg' x0 x1 x2 x3 x4 x5 x6
      (IN: @gcpn7 r rg x0 x1 x2 x3 x4 x5 x6)
      (LEr: r <7= r')
      (LErg: rg <7= rg'):
  @gcpn7 r' rg' x0 x1 x2 x3 x4 x5 x6.
Proof.
  destruct IN. constructor.
  eapply ucpn7_mon. apply IN. intros.
  destruct PR. left. apply LEr, H. right.
  eapply pcpn7_mon. apply H. apply LErg.
Qed.

Lemma gcpn7_init r: gcpn7 r r <7= ucpn7 gf r.
Proof.
  intros. ucpn. destruct PR.
  eapply ucpn7_mon; [apply IN|].
  intros. destruct PR.
  - ubase. apply H.
  - uunfold H. ustep. apply H.
Qed.

Lemma gcpn7_final r rg: ucpn7 gf r <7= gcpn7 r rg.
Proof.
  constructor. eapply ucpn7_mon. apply PR.
  intros. left. apply PR0.
Qed.

Lemma gcpn7_unfold:
  gcpn7 bot7 bot7 <7= gf (gcpn7 bot7 bot7).
Proof.
  intros. destruct PR. destruct IN.
  - uunfold H. eapply gf_mon. apply H.
    intros. econstructor. apply PR.
  - eapply gf_mon; [| intros; econstructor; right; apply PR].
    eapply (dcompat7_compat (dcpn7_compat gf_mon)).
    eapply dcpn7_mon. apply H.
    intros. destruct PR; try contradiction.
    uunfold H0. eapply gf_mon. apply H0.
    intros. right.
    apply pcpn7_final, ucpn7_init. apply gf_mon. apply PR.
Qed.

Lemma gcpn7_base r rg:
  r <7= gcpn7 r rg.
Proof.
  intros. constructor. ubase. left. apply PR.
Qed.

Lemma gcpn7_step r rg:
  gf (gcpn7 rg rg) <7= gcpn7 r rg.
Proof.
  intros. constructor. ubase. right. ustep.
  eapply gf_mon. apply PR.
  intros. destruct PR0.
  apply ucpn7_ucpn. apply gf_mon.
  eapply ucpn7_mon. apply IN.
  intros. destruct PR0.
  - ubase. apply H.
  - left. apply H.
Qed.

Lemma gcpn7_ucpn r rg:
  ucpn7 gf (gcpn7 r rg) <7= gcpn7 r rg.
Proof.
  intros. constructor. ucpn.
  eapply ucpn7_mon. apply PR.
  intros. destruct PR0. apply IN.
Qed.

Lemma gcpn7_clo r rg
      clo (LE: clo <8= ucpn7 gf):
  clo (gcpn7 r rg) <7= gcpn7 r rg.
Proof.
  intros. apply gcpn7_ucpn, LE, PR.
Qed.

(*
  Fixpoint theorem of gcpn7
 *)

Lemma gcpn7_cofix: forall
    r rg (LE: r <7= rg)
    l (OBG: forall rr (INC: rg <7= rr) (CIH: l <7= rr), l <7= gcpn7 r rr),
  l <7= gcpn7 r rg.
Proof.
Admitted.

End GeneralizedCompanion7_main.

Lemma gcpn7_mon_bot (gf gf': rel -> rel) x0 x1 x2 x3 x4 x5 x6 r rg
      (IN: @gcpn7 gf bot7 bot7 x0 x1 x2 x3 x4 x5 x6)
      (MON: monotone7 gf)
      (MON': monotone7 gf')
      (LE: gf <8= gf'):
  @gcpn7 gf' r rg x0 x1 x2 x3 x4 x5 x6.
Proof.
  destruct IN. constructor.
  eapply ucpn7_mon; [| intros; right; eapply PR].
  ubase.
  eapply pcpn7_mon_bot, LE; [|apply MON].
  ustep.
  eapply MON, ucpn7_ucpn, MON.
  eapply ucpn7_compat; [apply MON|].
  eapply ucpn7_mon. apply IN.
  intros. destruct PR. contradiction. uunfold H. apply H.
Qed.

End GeneralizedCompanion7.

Hint Resolve gcpn7_base : paco.
Hint Resolve gcpn7_step : paco.

