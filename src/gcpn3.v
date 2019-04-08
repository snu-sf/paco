Require Import paco3 pcpn3 pcpntac.
Set Implicit Arguments.

Section GeneralizedCompanion3.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.

Local Notation rel := (rel3 T0 T1 T2).

Section GeneralizedCompanion3_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone3 gf.

Inductive gcpn3 (r rg : rel) x0 x1 x2 : Prop :=
| gcpn3_intro (IN: ucpn3 gf (r \3/ pcpn3 gf rg) x0 x1 x2)
.

Lemma gcpn3_mon r r' rg rg' x0 x1 x2
      (IN: @gcpn3 r rg x0 x1 x2)
      (LEr: r <3= r')
      (LErg: rg <3= rg'):
  @gcpn3 r' rg' x0 x1 x2.
Proof.
  destruct IN. constructor.
  eapply ucpn3_mon. apply IN. intros.
  destruct PR. left. apply LEr, H. right.
  eapply pcpn3_mon. apply H. apply LErg.
Qed.

Lemma gcpn3_init r: gcpn3 r r <3= ucpn3 gf r.
Proof.
  intros. ucpn. destruct PR.
  eapply ucpn3_mon; [apply IN|].
  intros. destruct PR.
  - ubase. apply H.
  - uunfold H. ustep. apply H.
Qed.

Lemma gcpn3_final r rg: ucpn3 gf r <3= gcpn3 r rg.
Proof.
  constructor. eapply ucpn3_mon. apply PR.
  intros. left. apply PR0.
Qed.

Lemma gcpn3_unfold:
  gcpn3 bot3 bot3 <3= gf (gcpn3 bot3 bot3).
Proof.
  intros. destruct PR. destruct IN.
  - uunfold H. eapply gf_mon. apply H.
    intros. econstructor. apply PR.
  - eapply gf_mon; [| intros; econstructor; right; apply PR].
    eapply (dcompat3_compat (dcpn3_compat gf_mon)).
    eapply dcpn3_mon. apply H.
    intros. destruct PR; try contradiction.
    uunfold H0. eapply gf_mon. apply H0.
    intros. right.
    apply pcpn3_final, ucpn3_init. apply gf_mon. apply PR.
Qed.

Lemma gcpn3_base r rg:
  r <3= gcpn3 r rg.
Proof.
  intros. constructor. ubase. left. apply PR.
Qed.

Lemma gcpn3_step r rg:
  gf (gcpn3 rg rg) <3= gcpn3 r rg.
Proof.
  intros. constructor. ubase. right. ustep.
  eapply gf_mon. apply PR.
  intros. destruct PR0.
  apply ucpn3_ucpn. apply gf_mon.
  eapply ucpn3_mon. apply IN.
  intros. destruct PR0.
  - ubase. apply H.
  - left. apply H.
Qed.

Lemma gcpn3_ucpn r rg:
  ucpn3 gf (gcpn3 r rg) <3= gcpn3 r rg.
Proof.
  intros. constructor. ucpn.
  eapply ucpn3_mon. apply PR.
  intros. destruct PR0. apply IN.
Qed.

Lemma gcpn3_clo r rg
      clo (LE: clo <4= ucpn3 gf):
  clo (gcpn3 r rg) <3= gcpn3 r rg.
Proof.
  intros. apply gcpn3_ucpn, LE, PR.
Qed.

(*
  Fixpoint theorem of gcpn3
 *)

Lemma gcpn3_cofix: forall
    r rg (LE: r <3= rg)
    l (OBG: forall rr (INC: rg <3= rr) (CIH: l <3= rr), l <3= gcpn3 r rr),
  l <3= gcpn3 r rg.
Proof.
Admitted.

End GeneralizedCompanion3_main.

Lemma gcpn3_mon_bot (gf gf': rel -> rel) x0 x1 x2 r rg
      (IN: @gcpn3 gf bot3 bot3 x0 x1 x2)
      (MON: monotone3 gf)
      (MON': monotone3 gf')
      (LE: gf <4= gf'):
  @gcpn3 gf' r rg x0 x1 x2.
Proof.
  destruct IN. constructor.
  eapply ucpn3_mon; [| intros; right; eapply PR].
  ubase.
  eapply pcpn3_mon_bot, LE; [|apply MON].
  ustep.
  eapply MON, ucpn3_ucpn, MON.
  eapply ucpn3_compat; [apply MON|].
  eapply ucpn3_mon. apply IN.
  intros. destruct PR. contradiction. uunfold H. apply H.
Qed.

End GeneralizedCompanion3.

Hint Resolve gcpn3_base : paco.
Hint Resolve gcpn3_step : paco.

