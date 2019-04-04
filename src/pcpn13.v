Require Export Program.Basics. Open Scope program_scope.
Require Import paco13 pacotac.
Set Implicit Arguments.

Section PacoCompanion13.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
Variable T7 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5), Type.
Variable T8 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6), Type.
Variable T9 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7), Type.
Variable T10 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8), Type.
Variable T11 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9), Type.
Variable T12 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10), Type.

Local Notation rel := (rel13 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12).

Section PacoCompanion13_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone13 gf.

(** 
  Distributive Compatibility, Distributive Companion, (U)Paco Companion 
*)

Structure dcompatible13 (clo: rel -> rel) : Prop :=
  dcompat13_intro {
      dcompat13_mon: monotone13 clo;
      dcompat13_compat : forall r,
          clo (gf r) <13= gf (clo r);
      dcompat13_distr : forall r1 r2,
          clo (r1 \13/ r2) <13= (clo r1 \13/ clo r2);
    }.

Inductive dcpn13 (r: rel) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : Prop :=
| dcpn13_intro
    clo
    (COM: dcompatible13 clo)
    (CLO: clo r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)
.

Definition pcpn13 r := paco13 gf (dcpn13 r).
Definition ucpn13 r := upaco13 gf (dcpn13 r).

Lemma dcpn13_mon: monotone13 dcpn13.
Proof.
  red; intros.
  destruct IN. exists clo.
  - apply COM.
  - eapply dcompat13_mon.
    + apply COM.
    + apply CLO.
    + apply LE.
Qed.

Lemma pcpn13_mon: monotone13 pcpn13.
Proof.
  red; intros. eapply paco13_mon. apply IN.
  intros. eapply dcpn13_mon. apply PR. apply LE.
Qed.

Lemma ucpn13_mon: monotone13 ucpn13.
Proof.
  red; intros. eapply upaco13_mon. apply IN.
  intros. eapply dcpn13_mon. apply PR. apply LE.
Qed.

Lemma dcpn13_greatest: forall clo (COM: dcompatible13 clo), clo <14= dcpn13.
Proof. intros. econstructor;[apply COM|apply PR]. Qed.

Lemma dcpn13_compat: dcompatible13 dcpn13.
Proof.
  econstructor; [apply dcpn13_mon| |]; intros.
  - destruct PR; eapply gf_mon with (r:=clo r).
    + eapply (dcompat13_compat COM); apply CLO.
    + intros. econstructor; [apply COM|apply PR].
  - destruct PR.
    eapply (dcompat13_distr COM) in CLO.
    destruct CLO.
    + left. eapply dcpn13_greatest. apply COM. apply H.
    + right. eapply dcpn13_greatest. apply COM. apply H.
Qed.

Lemma dcpn13_base: forall r, r <13= dcpn13 r.
Proof.
  exists id; [|apply PR].
  econstructor; repeat intro.
  + apply LE, IN.
  + apply PR0.
  + destruct PR0.
    * left. apply H.
    * right. apply H.
Qed.

Lemma ucpn13_base: forall r, r <13= ucpn13 r.
Proof.
  right. apply dcpn13_base. apply PR.
Qed.

Lemma ucpn13_from_dcpn13_upaco r:
  dcpn13 (upaco13 gf r) <13= ucpn13 r.
Proof.
  intros.
  eapply (dcompat13_distr dcpn13_compat) in PR.
  destruct PR as [IN|IN]; cycle 1.
  - right. apply IN.
  - left. revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 IN.
    pcofix CIH. intros.
    pstep. eapply gf_mon.
    + apply (dcompat13_compat dcpn13_compat).
      eapply dcpn13_mon. apply IN.
      intros. _punfold PR. apply PR. apply gf_mon.
    + intros. apply (dcompat13_distr dcpn13_compat) in PR.
      right. destruct PR.
      * apply CIH. apply H.
      * apply CIH0. apply H.
Qed.

Lemma dcpn13_dcpn: forall r,
    dcpn13 (dcpn13 r) <13= dcpn13 r.
Proof.
  intros. exists (compose dcpn13 dcpn13); [|apply PR].
  econstructor.
  - repeat intro. eapply dcpn13_mon; [apply IN|].
    intros. eapply dcpn13_mon; [apply PR0|apply LE].
  - intros. eapply (dcompat13_compat dcpn13_compat).
    eapply dcpn13_mon; [apply PR0|].
    intros. eapply (dcompat13_compat dcpn13_compat), PR1.
  - intros. eapply (dcompat13_distr dcpn13_compat).
    eapply dcpn13_mon, (dcompat13_distr dcpn13_compat).
    apply PR0.
Qed.

Lemma ucpn13_ucpn: forall r,
    ucpn13 (ucpn13 r) <13= ucpn13 r.
Proof.
  intros. destruct PR.
  - left. eapply paco13_mult_strong.
    eapply paco13_mon. apply H.
    intros. apply ucpn13_from_dcpn13_upaco in PR.
    eapply upaco13_mon. apply PR.
    intros. apply dcpn13_dcpn. apply PR0.
  - red. apply ucpn13_from_dcpn13_upaco in H.
    eapply upaco13_mon. apply H.
    intros. apply dcpn13_dcpn. apply PR.
Qed.

Lemma ucpn13_compat r: ucpn13 (gf r) <13= gf (ucpn13 r).
Proof.
  intros. destruct PR; cycle 1.
  - apply dcpn13_compat in H.
    eapply gf_mon. apply H.
    intros. right. apply PR.
  - _punfold H; [|apply gf_mon]. eapply gf_mon. apply H.
    intros. apply ucpn13_ucpn.
    eapply upaco13_mon. apply PR.
    intros. eapply dcpn13_mon. apply PR0.
    intros. left. pstep. eapply gf_mon. apply PR1.
    intros. apply ucpn13_base. apply PR2.
Qed.

Lemma ucpn13_init:
  ucpn13 bot13 <13= paco13 gf bot13.
Proof.
  pcofix CIH. intros.
  destruct PR; cycle 1.
  - eapply paco13_mon_bot; [| intros; apply PR].
    eapply paco13_algebra, H. apply gf_mon. intros.
    eapply (dcompat13_compat dcpn13_compat).
    eapply dcpn13_mon. apply PR. contradiction.
  - _punfold H; [|apply gf_mon]. pstep.
    eapply gf_mon. apply H. intros.
    right. apply CIH. apply PR.
Qed.

Lemma pcpn13_final r:
  paco13 gf r <13= pcpn13 r.
Proof.
  intros. eapply paco13_mon. apply PR.
  intros. apply dcpn13_base. apply PR0.
Qed.

Lemma ucpn13_final r:
  upaco13 gf r <13= ucpn13 r.
Proof.
  intros. eapply upaco13_mon. apply PR.
  intros. apply dcpn13_base. apply PR0.
Qed.

Lemma ucpn13_clo
      r clo (LE: clo <14= ucpn13):
  clo (ucpn13 r) <13= ucpn13 r.
Proof.
  intros. apply ucpn13_ucpn, LE, PR.
Qed.

Lemma pcpn13_clo
      r clo (LE: clo <14= ucpn13):
  clo (pcpn13 r) <13= pcpn13 r.
Proof.
  intros. pstep. eapply gf_mon, ucpn13_ucpn.
  apply ucpn13_compat. apply LE in PR.
  eapply ucpn13_mon. apply PR.
  intros. _punfold PR0. apply PR0. apply gf_mon.
Qed.

Lemma pcpn13_unfold r:
  pcpn13 r <13= gf (ucpn13 r).
Proof.
  intros. _punfold PR. apply PR. apply gf_mon.
Qed.

Lemma pcpn13_step r:
  gf (ucpn13 r) <13= pcpn13 r.
Proof.
  intros. pstep. apply PR.
Qed.

Lemma ucpn13_step r:
  gf (ucpn13 r) <13= ucpn13 r.
Proof.
  left. apply pcpn13_step. apply PR.
Qed.

Lemma ucpn13_id r : ucpn13 r <13= ucpn13 r.
Proof. intros. apply PR. Qed.

Lemma pcpn13_id r : pcpn13 r <13= pcpn13 r.
Proof. intros. apply PR. Qed.

Lemma gf_dcpn13_mon: monotone13 (compose gf dcpn13).
Proof.
  repeat intro. eapply gf_mon. apply IN.
  intros. eapply dcpn13_mon. apply PR. apply LE.  
Qed.

Lemma pcpn13_from_paco r: paco13 (compose gf dcpn13) r <13= pcpn13 r.
Proof.
  intros. apply dcpn13_base in PR. revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 PR.
  pcofix CIH. intros.
  pstep.
  eapply gf_mon; cycle 1.
  { instantiate (1:= _ \13/ _). right.
    destruct PR0; [apply CIH, H | apply CIH0, H]. }
  eapply gf_mon, (dcompat13_distr dcpn13_compat).
  eapply gf_mon, dcpn13_dcpn.
  eapply (dcompat13_compat dcpn13_compat).
  eapply dcpn13_mon. apply PR.
  intros. _punfold PR0. apply PR0. apply gf_dcpn13_mon.
Qed.

Lemma pcpn13_to_paco r: pcpn13 r <13= paco13 (compose gf dcpn13) r.
Proof.
  pcofix CIH. intros.
  pstep. _punfold PR; [|apply gf_mon].
  eapply gf_mon. apply PR. intros.
  destruct PR0; cycle 1.
  - eapply dcpn13_mon. apply H. intros.
    right. apply CIH0, PR0. 
  - apply dcpn13_base. right. apply CIH, H.
Qed.

Lemma pcpn13_cofix
    r l (OBG: forall rr (INC: r <13= rr) (CIH: l <13= rr), l <13= pcpn13 rr):
  l <13= pcpn13 r.
Proof.
  under_forall ltac:(apply pcpn13_from_paco).
  pcofix CIH. intros. apply pcpn13_to_paco.
  apply OBG. apply CIH0. apply CIH. apply PR.
Qed.

End PacoCompanion13_main.

Lemma pcpn13_mon_bot (gf gf': rel -> rel) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 r
      (IN: @pcpn13 gf bot13 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)
      (MON: monotone13 gf)
      (LE: gf <14= gf'):
  @pcpn13 gf' r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12.
Proof.
  eapply paco13_mon_bot, LE.
  apply ucpn13_init. apply MON. left. apply IN.
Qed.

Lemma ucpn13_mon_bot (gf gf': rel -> rel) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 r
      (IN: @ucpn13 gf bot13 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)
      (MON: monotone13 gf)
      (LE: gf <14= gf'):
  @ucpn13 gf' r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12.
Proof.
  eapply upaco13_mon_bot, LE.
  left. apply ucpn13_init. apply MON. apply IN.
Qed.

End PacoCompanion13.

Hint Resolve ucpn13_base : paco.
Hint Resolve pcpn13_step : paco.
Hint Resolve ucpn13_step : paco.

