Require Import paco6 pcpn6 pcpntac.
Set Implicit Arguments.

Section GeneralizedCompanion6.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.

Local Notation rel := (rel6 T0 T1 T2 T3 T4 T5).

Section GeneralizedCompanion6_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone6 gf.

Inductive gcpn6 (r rg : rel) x0 x1 x2 x3 x4 x5 : Prop :=
| gcpn6_intro (IN: ucpn6 gf (r \6/ pcpn6 gf rg) x0 x1 x2 x3 x4 x5)
.

Lemma gcpn6_mon r r' rg rg' x0 x1 x2 x3 x4 x5
      (IN: @gcpn6 r rg x0 x1 x2 x3 x4 x5)
      (LEr: r <6= r')
      (LErg: rg <6= rg'):
  @gcpn6 r' rg' x0 x1 x2 x3 x4 x5.
Proof.
  destruct IN. constructor.
  eapply ucpn6_mon. apply IN. intros.
  destruct PR. left. apply LEr, H. right.
  eapply pcpn6_mon. apply H. apply LErg.
Qed.

Lemma gcpn6_init r: gcpn6 r r <6= ucpn6 gf r.
Proof.
  intros. ucpn. destruct PR.
  eapply ucpn6_mon; [apply IN|].
  intros. destruct PR.
  - ubase. apply H.
  - uunfold H. ustep. apply H.
Qed.

Lemma gcpn6_final r rg: ucpn6 gf r <6= gcpn6 r rg.
Proof.
  constructor. eapply ucpn6_mon. apply PR.
  intros. left. apply PR0.
Qed.

Lemma gcpn6_unfold:
  gcpn6 bot6 bot6 <6= gf (gcpn6 bot6 bot6).
Proof.
  intros. destruct PR. destruct IN.
  - uunfold H. eapply gf_mon. apply H.
    intros. econstructor. apply PR.
  - eapply gf_mon; [| intros; econstructor; right; apply PR].
    eapply (dcompat6_compat (dcpn6_compat gf_mon)).
    eapply dcpn6_mon. apply H.
    intros. destruct PR; try contradiction.
    uunfold H0. eapply gf_mon. apply H0.
    intros. right.
    apply pcpn6_final, ucpn6_init. apply gf_mon. apply PR.
Qed.

Lemma gcpn6_base r rg:
  r <6= gcpn6 r rg.
Proof.
  intros. constructor. ubase. left. apply PR.
Qed.

Lemma gcpn6_step r rg:
  gf (gcpn6 rg rg) <6= gcpn6 r rg.
Proof.
  intros. constructor. ubase. right. ustep.
  eapply gf_mon. apply PR.
  intros. destruct PR0.
  apply ucpn6_ucpn. apply gf_mon.
  eapply ucpn6_mon. apply IN.
  intros. destruct PR0.
  - ubase. apply H.
  - left. apply H.
Qed.

Lemma gcpn6_ucpn r rg:
  ucpn6 gf (gcpn6 r rg) <6= gcpn6 r rg.
Proof.
  intros. constructor. ucpn.
  eapply ucpn6_mon. apply PR.
  intros. destruct PR0. apply IN.
Qed.

Lemma gcpn6_clo r rg
      clo (LE: clo <7= ucpn6 gf):
  clo (gcpn6 r rg) <6= gcpn6 r rg.
Proof.
  intros. apply gcpn6_ucpn, LE, PR.
Qed.

(*
  Fixpoint theorem of gcpn6
 *)

Lemma gcpn6_cofix: forall
    r rg (LE: r <6= rg)
    l (OBG: forall rr (INC: rg <6= rr) (CIH: l <6= rr), l <6= gcpn6 r rr),
  l <6= gcpn6 r rg.
Proof.
Admitted.

End GeneralizedCompanion6_main.

Lemma gcpn6_mon_bot (gf gf': rel -> rel) x0 x1 x2 x3 x4 x5 r rg
      (IN: @gcpn6 gf bot6 bot6 x0 x1 x2 x3 x4 x5)
      (MON: monotone6 gf)
      (MON': monotone6 gf')
      (LE: gf <7= gf'):
  @gcpn6 gf' r rg x0 x1 x2 x3 x4 x5.
Proof.
  destruct IN. constructor.
  eapply ucpn6_mon; [| intros; right; eapply PR].
  ubase.
  eapply pcpn6_mon_bot, LE; [|apply MON].
  ustep.
  eapply MON, ucpn6_ucpn, MON.
  eapply ucpn6_compat; [apply MON|].
  eapply ucpn6_mon. apply IN.
  intros. destruct PR. contradiction. uunfold H. apply H.
Qed.

End GeneralizedCompanion6.

Hint Resolve gcpn6_base : paco.
Hint Resolve gcpn6_step : paco.

