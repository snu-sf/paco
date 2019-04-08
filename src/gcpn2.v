Require Import paco2 pcpn2 pcpntac.
Set Implicit Arguments.

Section GeneralizedCompanion2.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.

Local Notation rel := (rel2 T0 T1).

Section GeneralizedCompanion2_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone2 gf.

Inductive gcpn2 (r rg : rel) x0 x1 : Prop :=
| gcpn2_intro (IN: ucpn2 gf (r \2/ pcpn2 gf rg) x0 x1)
.

Lemma gcpn2_mon r r' rg rg' x0 x1
      (IN: @gcpn2 r rg x0 x1)
      (LEr: r <2= r')
      (LErg: rg <2= rg'):
  @gcpn2 r' rg' x0 x1.
Proof.
  destruct IN. constructor.
  eapply ucpn2_mon. apply IN. intros.
  destruct PR. left. apply LEr, H. right.
  eapply pcpn2_mon. apply H. apply LErg.
Qed.

Lemma gcpn2_init r: gcpn2 r r <2= ucpn2 gf r.
Proof.
  intros. ucpn. destruct PR.
  eapply ucpn2_mon; [apply IN|].
  intros. destruct PR.
  - ubase. apply H.
  - uunfold H. ustep. apply H.
Qed.

Lemma gcpn2_final r rg: ucpn2 gf r <2= gcpn2 r rg.
Proof.
  constructor. eapply ucpn2_mon. apply PR.
  intros. left. apply PR0.
Qed.

Lemma gcpn2_unfold:
  gcpn2 bot2 bot2 <2= gf (gcpn2 bot2 bot2).
Proof.
  intros. destruct PR. destruct IN.
  - uunfold H. eapply gf_mon. apply H.
    intros. econstructor. apply PR.
  - eapply gf_mon; [| intros; econstructor; right; apply PR].
    eapply (dcompat2_compat (dcpn2_compat gf_mon)).
    eapply dcpn2_mon. apply H.
    intros. destruct PR; try contradiction.
    uunfold H0. eapply gf_mon. apply H0.
    intros. right.
    apply pcpn2_final, ucpn2_init. apply gf_mon. apply PR.
Qed.

Lemma gcpn2_base r rg:
  r <2= gcpn2 r rg.
Proof.
  intros. constructor. ubase. left. apply PR.
Qed.

Lemma gcpn2_step r rg:
  gf (gcpn2 rg rg) <2= gcpn2 r rg.
Proof.
  intros. constructor. ubase. right. ustep.
  eapply gf_mon. apply PR.
  intros. destruct PR0.
  apply ucpn2_ucpn. apply gf_mon.
  eapply ucpn2_mon. apply IN.
  intros. destruct PR0.
  - ubase. apply H.
  - left. apply H.
Qed.

Lemma gcpn2_ucpn r rg:
  ucpn2 gf (gcpn2 r rg) <2= gcpn2 r rg.
Proof.
  intros. constructor. ucpn.
  eapply ucpn2_mon. apply PR.
  intros. destruct PR0. apply IN.
Qed.

Lemma gcpn2_clo r rg
      clo (LE: clo <3= ucpn2 gf):
  clo (gcpn2 r rg) <2= gcpn2 r rg.
Proof.
  intros. apply gcpn2_ucpn, LE, PR.
Qed.

(*
  Fixpoint theorem of gcpn2
 *)

Lemma gcpn2_cofix: forall
    r rg (LE: r <2= rg)
    l (OBG: forall rr (INC: rg <2= rr) (CIH: l <2= rr), l <2= gcpn2 r rr),
  l <2= gcpn2 r rg.
Proof.
Admitted.

End GeneralizedCompanion2_main.

Lemma gcpn2_mon_bot (gf gf': rel -> rel) x0 x1 r rg
      (IN: @gcpn2 gf bot2 bot2 x0 x1)
      (MON: monotone2 gf)
      (MON': monotone2 gf')
      (LE: gf <3= gf'):
  @gcpn2 gf' r rg x0 x1.
Proof.
  destruct IN. constructor.
  eapply ucpn2_mon; [| intros; right; eapply PR].
  ubase.
  eapply pcpn2_mon_bot, LE; [|apply MON].
  ustep.
  eapply MON, ucpn2_ucpn, MON.
  eapply ucpn2_compat; [apply MON|].
  eapply ucpn2_mon. apply IN.
  intros. destruct PR. contradiction. uunfold H. apply H.
Qed.

End GeneralizedCompanion2.

Hint Resolve gcpn2_base : paco.
Hint Resolve gcpn2_step : paco.

