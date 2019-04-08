Require Import paco0 pcpn0 pcpntac.
Set Implicit Arguments.

Section GeneralizedCompanion0.


Local Notation rel := (rel0).

Section GeneralizedCompanion0_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone0 gf.

Inductive gcpn0 (r rg : rel) : Prop :=
| gcpn0_intro (IN: ucpn0 gf (r \0/ pcpn0 gf rg))
.

Lemma gcpn0_mon r r' rg rg'
      (IN: @gcpn0 r rg)
      (LEr: r <0= r')
      (LErg: rg <0= rg'):
  @gcpn0 r' rg'.
Proof.
  destruct IN. constructor.
  eapply ucpn0_mon. apply IN. intros.
  destruct PR. left. apply LEr, H. right.
  eapply pcpn0_mon. apply H. apply LErg.
Qed.

Lemma gcpn0_init r: gcpn0 r r <0= ucpn0 gf r.
Proof.
  intros. ucpn. destruct PR.
  eapply ucpn0_mon; [apply IN|].
  intros. destruct PR.
  - ubase. apply H.
  - uunfold H. ustep. apply H.
Qed.

Lemma gcpn0_final r rg: ucpn0 gf r <0= gcpn0 r rg.
Proof.
  constructor. eapply ucpn0_mon. apply PR.
  intros. left. apply PR0.
Qed.

Lemma gcpn0_unfold:
  gcpn0 bot0 bot0 <0= gf (gcpn0 bot0 bot0).
Proof.
  intros. destruct PR. destruct IN.
  - uunfold H. eapply gf_mon. apply H.
    intros. econstructor. apply PR.
  - eapply gf_mon; [| intros; econstructor; right; apply PR].
    eapply (dcompat0_compat (dcpn0_compat gf_mon)).
    eapply dcpn0_mon. apply H.
    intros. destruct PR; try contradiction.
    uunfold H0. eapply gf_mon. apply H0.
    intros. right.
    apply pcpn0_final, ucpn0_init. apply gf_mon. apply PR.
Qed.

Lemma gcpn0_base r rg:
  r <0= gcpn0 r rg.
Proof.
  intros. constructor. ubase. left. apply PR.
Qed.

Lemma gcpn0_step r rg:
  gf (gcpn0 rg rg) <0= gcpn0 r rg.
Proof.
  intros. constructor. ubase. right. ustep.
  eapply gf_mon. apply PR.
  intros. destruct PR0.
  apply ucpn0_ucpn. apply gf_mon.
  eapply ucpn0_mon. apply IN.
  intros. destruct PR0.
  - ubase. apply H.
  - left. apply H.
Qed.

Lemma gcpn0_ucpn r rg:
  ucpn0 gf (gcpn0 r rg) <0= gcpn0 r rg.
Proof.
  intros. constructor. ucpn.
  eapply ucpn0_mon. apply PR.
  intros. destruct PR0. apply IN.
Qed.

Lemma gcpn0_clo r rg
      clo (LE: clo <1= ucpn0 gf):
  clo (gcpn0 r rg) <0= gcpn0 r rg.
Proof.
  intros. apply gcpn0_ucpn, LE, PR.
Qed.

(*
  Fixpoint theorem of gcpn0
 *)

Lemma gcpn0_cofix: forall
    r rg (LE: r <0= rg)
    l (OBG: forall rr (INC: rg <0= rr) (CIH: l <0= rr), l <0= gcpn0 r rr),
  l <0= gcpn0 r rg.
Proof.
Admitted.

End GeneralizedCompanion0_main.

Lemma gcpn0_mon_bot (gf gf': rel -> rel) r rg
      (IN: @gcpn0 gf bot0 bot0)
      (MON: monotone0 gf)
      (MON': monotone0 gf')
      (LE: gf <1= gf'):
  @gcpn0 gf' r rg.
Proof.
  destruct IN. constructor.
  eapply ucpn0_mon; [| intros; right; eapply PR].
  ubase.
  eapply pcpn0_mon_bot, LE; [|apply MON].
  ustep.
  eapply MON, ucpn0_ucpn, MON.
  eapply ucpn0_compat; [apply MON|].
  eapply ucpn0_mon. apply IN.
  intros. destruct PR. contradiction. uunfold H. apply H.
Qed.

End GeneralizedCompanion0.

Hint Resolve gcpn0_base : paco.
Hint Resolve gcpn0_step : paco.

