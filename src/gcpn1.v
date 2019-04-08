Require Import paco1 pcpn1 pcpntac.
Set Implicit Arguments.

Section GeneralizedCompanion1.

Variable T0 : Type.

Local Notation rel := (rel1 T0).

Section GeneralizedCompanion1_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone1 gf.

Inductive gcpn1 (r rg : rel) x0 : Prop :=
| gcpn1_intro (IN: ucpn1 gf (r \1/ pcpn1 gf rg) x0)
.

Lemma gcpn1_mon r r' rg rg' x0
      (IN: @gcpn1 r rg x0)
      (LEr: r <1= r')
      (LErg: rg <1= rg'):
  @gcpn1 r' rg' x0.
Proof.
  destruct IN. constructor.
  eapply ucpn1_mon. apply IN. intros.
  destruct PR. left. apply LEr, H. right.
  eapply pcpn1_mon. apply H. apply LErg.
Qed.

Lemma gcpn1_init r: gcpn1 r r <1= ucpn1 gf r.
Proof.
  intros. ucpn. destruct PR.
  eapply ucpn1_mon; [apply IN|].
  intros. destruct PR.
  - ubase. apply H.
  - uunfold H. ustep. apply H.
Qed.

Lemma gcpn1_final r rg: ucpn1 gf r <1= gcpn1 r rg.
Proof.
  constructor. eapply ucpn1_mon. apply PR.
  intros. left. apply PR0.
Qed.

Lemma gcpn1_unfold:
  gcpn1 bot1 bot1 <1= gf (gcpn1 bot1 bot1).
Proof.
  intros. destruct PR. destruct IN.
  - uunfold H. eapply gf_mon. apply H.
    intros. econstructor. apply PR.
  - eapply gf_mon; [| intros; econstructor; right; apply PR].
    eapply (dcompat1_compat (dcpn1_compat gf_mon)).
    eapply dcpn1_mon. apply H.
    intros. destruct PR; try contradiction.
    uunfold H0. eapply gf_mon. apply H0.
    intros. right.
    apply pcpn1_final, ucpn1_init. apply gf_mon. apply PR.
Qed.

Lemma gcpn1_base r rg:
  r <1= gcpn1 r rg.
Proof.
  intros. constructor. ubase. left. apply PR.
Qed.

Lemma gcpn1_step r rg:
  gf (gcpn1 rg rg) <1= gcpn1 r rg.
Proof.
  intros. constructor. ubase. right. ustep.
  eapply gf_mon. apply PR.
  intros. destruct PR0.
  apply ucpn1_ucpn. apply gf_mon.
  eapply ucpn1_mon. apply IN.
  intros. destruct PR0.
  - ubase. apply H.
  - left. apply H.
Qed.

Lemma gcpn1_ucpn r rg:
  ucpn1 gf (gcpn1 r rg) <1= gcpn1 r rg.
Proof.
  intros. constructor. ucpn.
  eapply ucpn1_mon. apply PR.
  intros. destruct PR0. apply IN.
Qed.

Lemma gcpn1_clo r rg
      clo (LE: clo <2= ucpn1 gf):
  clo (gcpn1 r rg) <1= gcpn1 r rg.
Proof.
  intros. apply gcpn1_ucpn, LE, PR.
Qed.

(*
  Fixpoint theorem of gcpn1
 *)

Lemma gcpn1_cofix: forall
    r rg (LE: r <1= rg)
    l (OBG: forall rr (INC: rg <1= rr) (CIH: l <1= rr), l <1= gcpn1 r rr),
  l <1= gcpn1 r rg.
Proof.
Admitted.

End GeneralizedCompanion1_main.

Lemma gcpn1_mon_bot (gf gf': rel -> rel) x0 r rg
      (IN: @gcpn1 gf bot1 bot1 x0)
      (MON: monotone1 gf)
      (MON': monotone1 gf')
      (LE: gf <2= gf'):
  @gcpn1 gf' r rg x0.
Proof.
  destruct IN. constructor.
  eapply ucpn1_mon; [| intros; right; eapply PR].
  ubase.
  eapply pcpn1_mon_bot, LE; [|apply MON].
  ustep.
  eapply MON, ucpn1_ucpn, MON.
  eapply ucpn1_compat; [apply MON|].
  eapply ucpn1_mon. apply IN.
  intros. destruct PR. contradiction. uunfold H. apply H.
Qed.

End GeneralizedCompanion1.

Hint Resolve gcpn1_base : paco.
Hint Resolve gcpn1_step : paco.

