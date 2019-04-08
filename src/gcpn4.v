Require Import paco4 pcpn4 pcpntac.
Set Implicit Arguments.

Section GeneralizedCompanion4.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.

Local Notation rel := (rel4 T0 T1 T2 T3).

Section GeneralizedCompanion4_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone4 gf.

Inductive gcpn4 (r rg : rel) x0 x1 x2 x3 : Prop :=
| gcpn4_intro (IN: ucpn4 gf (r \4/ pcpn4 gf rg) x0 x1 x2 x3)
.

Lemma gcpn4_mon r r' rg rg' x0 x1 x2 x3
      (IN: @gcpn4 r rg x0 x1 x2 x3)
      (LEr: r <4= r')
      (LErg: rg <4= rg'):
  @gcpn4 r' rg' x0 x1 x2 x3.
Proof.
  destruct IN. constructor.
  eapply ucpn4_mon. apply IN. intros.
  destruct PR. left. apply LEr, H. right.
  eapply pcpn4_mon. apply H. apply LErg.
Qed.

Lemma gcpn4_init r: gcpn4 r r <4= ucpn4 gf r.
Proof.
  intros. ucpn. destruct PR.
  eapply ucpn4_mon; [apply IN|].
  intros. destruct PR.
  - ubase. apply H.
  - uunfold H. ustep. apply H.
Qed.

Lemma gcpn4_final r rg: ucpn4 gf r <4= gcpn4 r rg.
Proof.
  constructor. eapply ucpn4_mon. apply PR.
  intros. left. apply PR0.
Qed.

Lemma gcpn4_unfold:
  gcpn4 bot4 bot4 <4= gf (gcpn4 bot4 bot4).
Proof.
  intros. destruct PR. destruct IN.
  - uunfold H. eapply gf_mon. apply H.
    intros. econstructor. apply PR.
  - eapply gf_mon; [| intros; econstructor; right; apply PR].
    eapply (dcompat4_compat (dcpn4_compat gf_mon)).
    eapply dcpn4_mon. apply H.
    intros. destruct PR; try contradiction.
    uunfold H0. eapply gf_mon. apply H0.
    intros. right.
    apply pcpn4_final, ucpn4_init. apply gf_mon. apply PR.
Qed.

Lemma gcpn4_base r rg:
  r <4= gcpn4 r rg.
Proof.
  intros. constructor. ubase. left. apply PR.
Qed.

Lemma gcpn4_step r rg:
  gf (gcpn4 rg rg) <4= gcpn4 r rg.
Proof.
  intros. constructor. ubase. right. ustep.
  eapply gf_mon. apply PR.
  intros. destruct PR0.
  apply ucpn4_ucpn. apply gf_mon.
  eapply ucpn4_mon. apply IN.
  intros. destruct PR0.
  - ubase. apply H.
  - left. apply H.
Qed.

Lemma gcpn4_ucpn r rg:
  ucpn4 gf (gcpn4 r rg) <4= gcpn4 r rg.
Proof.
  intros. constructor. ucpn.
  eapply ucpn4_mon. apply PR.
  intros. destruct PR0. apply IN.
Qed.

Lemma gcpn4_clo r rg
      clo (LE: clo <5= ucpn4 gf):
  clo (gcpn4 r rg) <4= gcpn4 r rg.
Proof.
  intros. apply gcpn4_ucpn, LE, PR.
Qed.

(*
  Fixpoint theorem of gcpn4
 *)

Lemma gcpn4_cofix: forall
    r rg (LE: r <4= rg)
    l (OBG: forall rr (INC: rg <4= rr) (CIH: l <4= rr), l <4= gcpn4 r rr),
  l <4= gcpn4 r rg.
Proof.
Admitted.

End GeneralizedCompanion4_main.

Lemma gcpn4_mon_bot (gf gf': rel -> rel) x0 x1 x2 x3 r rg
      (IN: @gcpn4 gf bot4 bot4 x0 x1 x2 x3)
      (MON: monotone4 gf)
      (MON': monotone4 gf')
      (LE: gf <5= gf'):
  @gcpn4 gf' r rg x0 x1 x2 x3.
Proof.
  destruct IN. constructor.
  eapply ucpn4_mon; [| intros; right; eapply PR].
  ubase.
  eapply pcpn4_mon_bot, LE; [|apply MON].
  ustep.
  eapply MON, ucpn4_ucpn, MON.
  eapply ucpn4_compat; [apply MON|].
  eapply ucpn4_mon. apply IN.
  intros. destruct PR. contradiction. uunfold H. apply H.
Qed.

End GeneralizedCompanion4.

Hint Resolve gcpn4_base : paco.
Hint Resolve gcpn4_step : paco.

