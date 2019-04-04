Require Export Program.Basics. Open Scope program_scope.
Require Import paco14 pacotac.
Set Implicit Arguments.

Section PacoCompanion14.

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
Variable T13 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) (x11: @T11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) (x12: @T12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11), Type.

Local Notation rel := (rel14 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13).

Section PacoCompanion14_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone14 gf.

(** 
  Distributive Compatibility, Distributive Companion, (U)Paco Companion 
*)

Structure dcompatible14 (clo: rel -> rel) : Prop :=
  dcompat14_intro {
      dcompat14_mon: monotone14 clo;
      dcompat14_compat : forall r,
          clo (gf r) <14= gf (clo r);
      dcompat14_distr : forall r1 r2,
          clo (r1 \14/ r2) <14= (clo r1 \14/ clo r2);
    }.

Inductive dcpn14 (r: rel) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : Prop :=
| dcpn14_intro
    clo
    (COM: dcompatible14 clo)
    (CLO: clo r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13)
.

Definition pcpn14 r := paco14 gf (dcpn14 r).
Definition ucpn14 r := upaco14 gf (dcpn14 r).

Lemma dcpn14_mon: monotone14 dcpn14.
Proof.
  red; intros.
  destruct IN. exists clo.
  - apply COM.
  - eapply dcompat14_mon.
    + apply COM.
    + apply CLO.
    + apply LE.
Qed.

Lemma pcpn14_mon: monotone14 pcpn14.
Proof.
  red; intros. eapply paco14_mon. apply IN.
  intros. eapply dcpn14_mon. apply PR. apply LE.
Qed.

Lemma ucpn14_mon: monotone14 ucpn14.
Proof.
  red; intros. eapply upaco14_mon. apply IN.
  intros. eapply dcpn14_mon. apply PR. apply LE.
Qed.

Lemma dcpn14_greatest: forall clo (COM: dcompatible14 clo), clo <15= dcpn14.
Proof. intros. econstructor;[apply COM|apply PR]. Qed.

Lemma dcpn14_compat: dcompatible14 dcpn14.
Proof.
  econstructor; [apply dcpn14_mon| |]; intros.
  - destruct PR; eapply gf_mon with (r:=clo r).
    + eapply (dcompat14_compat COM); apply CLO.
    + intros. econstructor; [apply COM|apply PR].
  - destruct PR.
    eapply (dcompat14_distr COM) in CLO.
    destruct CLO.
    + left. eapply dcpn14_greatest. apply COM. apply H.
    + right. eapply dcpn14_greatest. apply COM. apply H.
Qed.

Lemma dcpn14_base: forall r, r <14= dcpn14 r.
Proof.
  exists id; [|apply PR].
  econstructor; repeat intro.
  + apply LE, IN.
  + apply PR0.
  + destruct PR0.
    * left. apply H.
    * right. apply H.
Qed.

Lemma ucpn14_base: forall r, r <14= ucpn14 r.
Proof.
  right. apply dcpn14_base. apply PR.
Qed.

Lemma ucpn14_from_dcpn14_upaco r:
  dcpn14 (upaco14 gf r) <14= ucpn14 r.
Proof.
  intros.
  eapply (dcompat14_distr dcpn14_compat) in PR.
  destruct PR as [IN|IN]; cycle 1.
  - right. apply IN.
  - left. revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 IN.
    pcofix CIH. intros.
    pstep. eapply gf_mon.
    + apply (dcompat14_compat dcpn14_compat).
      eapply dcpn14_mon. apply IN.
      intros. _punfold PR. apply PR. apply gf_mon.
    + intros. apply (dcompat14_distr dcpn14_compat) in PR.
      right. destruct PR.
      * apply CIH. apply H.
      * apply CIH0. apply H.
Qed.

Lemma dcpn14_dcpn: forall r,
    dcpn14 (dcpn14 r) <14= dcpn14 r.
Proof.
  intros. exists (compose dcpn14 dcpn14); [|apply PR].
  econstructor.
  - repeat intro. eapply dcpn14_mon; [apply IN|].
    intros. eapply dcpn14_mon; [apply PR0|apply LE].
  - intros. eapply (dcompat14_compat dcpn14_compat).
    eapply dcpn14_mon; [apply PR0|].
    intros. eapply (dcompat14_compat dcpn14_compat), PR1.
  - intros. eapply (dcompat14_distr dcpn14_compat).
    eapply dcpn14_mon, (dcompat14_distr dcpn14_compat).
    apply PR0.
Qed.

Lemma ucpn14_ucpn: forall r,
    ucpn14 (ucpn14 r) <14= ucpn14 r.
Proof.
  intros. destruct PR.
  - left. eapply paco14_mult_strong.
    eapply paco14_mon. apply H.
    intros. apply ucpn14_from_dcpn14_upaco in PR.
    eapply upaco14_mon. apply PR.
    intros. apply dcpn14_dcpn. apply PR0.
  - red. apply ucpn14_from_dcpn14_upaco in H.
    eapply upaco14_mon. apply H.
    intros. apply dcpn14_dcpn. apply PR.
Qed.

Lemma ucpn14_compat r: ucpn14 (gf r) <14= gf (ucpn14 r).
Proof.
  intros. destruct PR; cycle 1.
  - apply dcpn14_compat in H.
    eapply gf_mon. apply H.
    intros. right. apply PR.
  - _punfold H; [|apply gf_mon]. eapply gf_mon. apply H.
    intros. apply ucpn14_ucpn.
    eapply upaco14_mon. apply PR.
    intros. eapply dcpn14_mon. apply PR0.
    intros. left. pstep. eapply gf_mon. apply PR1.
    intros. apply ucpn14_base. apply PR2.
Qed.

Lemma ucpn14_init:
  ucpn14 bot14 <14= paco14 gf bot14.
Proof.
  pcofix CIH. intros.
  destruct PR; cycle 1.
  - eapply paco14_mon_bot; [| intros; apply PR].
    eapply paco14_algebra, H. apply gf_mon. intros.
    eapply (dcompat14_compat dcpn14_compat).
    eapply dcpn14_mon. apply PR. contradiction.
  - _punfold H; [|apply gf_mon]. pstep.
    eapply gf_mon. apply H. intros.
    right. apply CIH. apply PR.
Qed.

Lemma pcpn14_final r:
  paco14 gf r <14= pcpn14 r.
Proof.
  intros. eapply paco14_mon. apply PR.
  intros. apply dcpn14_base. apply PR0.
Qed.

Lemma ucpn14_final r:
  upaco14 gf r <14= ucpn14 r.
Proof.
  intros. eapply upaco14_mon. apply PR.
  intros. apply dcpn14_base. apply PR0.
Qed.

Lemma ucpn14_clo
      r clo (LE: clo <15= ucpn14):
  clo (ucpn14 r) <14= ucpn14 r.
Proof.
  intros. apply ucpn14_ucpn, LE, PR.
Qed.

Lemma pcpn14_clo
      r clo (LE: clo <15= ucpn14):
  clo (pcpn14 r) <14= pcpn14 r.
Proof.
  intros. pstep. eapply gf_mon, ucpn14_ucpn.
  apply ucpn14_compat. apply LE in PR.
  eapply ucpn14_mon. apply PR.
  intros. _punfold PR0. apply PR0. apply gf_mon.
Qed.

Lemma pcpn14_unfold r:
  pcpn14 r <14= gf (ucpn14 r).
Proof.
  intros. _punfold PR. apply PR. apply gf_mon.
Qed.

Lemma pcpn14_step r:
  gf (ucpn14 r) <14= pcpn14 r.
Proof.
  intros. pstep. apply PR.
Qed.

Lemma ucpn14_step r:
  gf (ucpn14 r) <14= ucpn14 r.
Proof.
  left. apply pcpn14_step. apply PR.
Qed.

Lemma ucpn14_id r : ucpn14 r <14= ucpn14 r.
Proof. intros. apply PR. Qed.

Lemma pcpn14_id r : pcpn14 r <14= pcpn14 r.
Proof. intros. apply PR. Qed.

Lemma gf_dcpn14_mon: monotone14 (compose gf dcpn14).
Proof.
  repeat intro. eapply gf_mon. apply IN.
  intros. eapply dcpn14_mon. apply PR. apply LE.  
Qed.

Lemma pcpn14_from_paco r: paco14 (compose gf dcpn14) r <14= pcpn14 r.
Proof.
  intros. apply dcpn14_base in PR. revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 PR.
  pcofix CIH. intros.
  pstep.
  eapply gf_mon; cycle 1.
  { instantiate (1:= _ \14/ _). right.
    destruct PR0; [apply CIH, H | apply CIH0, H]. }
  eapply gf_mon, (dcompat14_distr dcpn14_compat).
  eapply gf_mon, dcpn14_dcpn.
  eapply (dcompat14_compat dcpn14_compat).
  eapply dcpn14_mon. apply PR.
  intros. _punfold PR0. apply PR0. apply gf_dcpn14_mon.
Qed.

Lemma pcpn14_to_paco r: pcpn14 r <14= paco14 (compose gf dcpn14) r.
Proof.
  pcofix CIH. intros.
  pstep. _punfold PR; [|apply gf_mon].
  eapply gf_mon. apply PR. intros.
  destruct PR0; cycle 1.
  - eapply dcpn14_mon. apply H. intros.
    right. apply CIH0, PR0. 
  - apply dcpn14_base. right. apply CIH, H.
Qed.

Lemma pcpn14_cofix
    r l (OBG: forall rr (INC: r <14= rr) (CIH: l <14= rr), l <14= pcpn14 rr):
  l <14= pcpn14 r.
Proof.
  under_forall ltac:(apply pcpn14_from_paco).
  pcofix CIH. intros. apply pcpn14_to_paco.
  apply OBG. apply CIH0. apply CIH. apply PR.
Qed.

End PacoCompanion14_main.

Lemma pcpn14_mon_bot (gf gf': rel -> rel) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 r
      (IN: @pcpn14 gf bot14 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13)
      (MON: monotone14 gf)
      (LE: gf <15= gf'):
  @pcpn14 gf' r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13.
Proof.
  eapply paco14_mon_bot, LE.
  apply ucpn14_init. apply MON. left. apply IN.
Qed.

Lemma ucpn14_mon_bot (gf gf': rel -> rel) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 r
      (IN: @ucpn14 gf bot14 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13)
      (MON: monotone14 gf)
      (LE: gf <15= gf'):
  @ucpn14 gf' r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13.
Proof.
  eapply upaco14_mon_bot, LE.
  left. apply ucpn14_init. apply MON. apply IN.
Qed.

End PacoCompanion14.

Hint Resolve ucpn14_base : paco.
Hint Resolve pcpn14_step : paco.
Hint Resolve ucpn14_step : paco.

