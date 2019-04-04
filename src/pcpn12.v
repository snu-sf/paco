Require Export Program.Basics. Open Scope program_scope.
Require Import paco12 pacotac.
Set Implicit Arguments.

Section PacoCompanion12.

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

Local Notation rel := (rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11).

Section PacoCompanion12_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone12 gf.

(** 
  Distributive Compatibility, Distributive Companion, (U)Paco Companion 
*)

Structure dcompatible12 (clo: rel -> rel) : Prop :=
  dcompat12_intro {
      dcompat12_mon: monotone12 clo;
      dcompat12_compat : forall r,
          clo (gf r) <12= gf (clo r);
      dcompat12_distr : forall r1 r2,
          clo (r1 \12/ r2) <12= (clo r1 \12/ clo r2);
    }.

Inductive dcpn12 (r: rel) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Prop :=
| dcpn12_intro
    clo
    (COM: dcompatible12 clo)
    (CLO: clo r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)
.

Definition pcpn12 r := paco12 gf (dcpn12 r).
Definition ucpn12 r := upaco12 gf (dcpn12 r).

Lemma dcpn12_mon: monotone12 dcpn12.
Proof.
  red; intros.
  destruct IN. exists clo.
  - apply COM.
  - eapply dcompat12_mon.
    + apply COM.
    + apply CLO.
    + apply LE.
Qed.

Lemma pcpn12_mon: monotone12 pcpn12.
Proof.
  red; intros. eapply paco12_mon. apply IN.
  intros. eapply dcpn12_mon. apply PR. apply LE.
Qed.

Lemma ucpn12_mon: monotone12 ucpn12.
Proof.
  red; intros. eapply upaco12_mon. apply IN.
  intros. eapply dcpn12_mon. apply PR. apply LE.
Qed.

Lemma dcpn12_greatest: forall clo (COM: dcompatible12 clo), clo <13= dcpn12.
Proof. intros. econstructor;[apply COM|apply PR]. Qed.

Lemma dcpn12_compat: dcompatible12 dcpn12.
Proof.
  econstructor; [apply dcpn12_mon| |]; intros.
  - destruct PR; eapply gf_mon with (r:=clo r).
    + eapply (dcompat12_compat COM); apply CLO.
    + intros. econstructor; [apply COM|apply PR].
  - destruct PR.
    eapply (dcompat12_distr COM) in CLO.
    destruct CLO.
    + left. eapply dcpn12_greatest. apply COM. apply H.
    + right. eapply dcpn12_greatest. apply COM. apply H.
Qed.

Lemma dcpn12_base: forall r, r <12= dcpn12 r.
Proof.
  exists id; [|apply PR].
  econstructor; repeat intro.
  + apply LE, IN.
  + apply PR0.
  + destruct PR0.
    * left. apply H.
    * right. apply H.
Qed.

Lemma ucpn12_base: forall r, r <12= ucpn12 r.
Proof.
  right. apply dcpn12_base. apply PR.
Qed.

Lemma ucpn12_from_dcpn12_upaco r:
  dcpn12 (upaco12 gf r) <12= ucpn12 r.
Proof.
  intros.
  eapply (dcompat12_distr dcpn12_compat) in PR.
  destruct PR as [IN|IN]; cycle 1.
  - right. apply IN.
  - left. revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 IN.
    pcofix CIH. intros.
    pstep. eapply gf_mon.
    + apply (dcompat12_compat dcpn12_compat).
      eapply dcpn12_mon. apply IN.
      intros. _punfold PR. apply PR. apply gf_mon.
    + intros. apply (dcompat12_distr dcpn12_compat) in PR.
      right. destruct PR.
      * apply CIH. apply H.
      * apply CIH0. apply H.
Qed.

Lemma dcpn12_dcpn: forall r,
    dcpn12 (dcpn12 r) <12= dcpn12 r.
Proof.
  intros. exists (compose dcpn12 dcpn12); [|apply PR].
  econstructor.
  - repeat intro. eapply dcpn12_mon; [apply IN|].
    intros. eapply dcpn12_mon; [apply PR0|apply LE].
  - intros. eapply (dcompat12_compat dcpn12_compat).
    eapply dcpn12_mon; [apply PR0|].
    intros. eapply (dcompat12_compat dcpn12_compat), PR1.
  - intros. eapply (dcompat12_distr dcpn12_compat).
    eapply dcpn12_mon, (dcompat12_distr dcpn12_compat).
    apply PR0.
Qed.

Lemma ucpn12_ucpn: forall r,
    ucpn12 (ucpn12 r) <12= ucpn12 r.
Proof.
  intros. destruct PR.
  - left. eapply paco12_mult_strong.
    eapply paco12_mon. apply H.
    intros. apply ucpn12_from_dcpn12_upaco in PR.
    eapply upaco12_mon. apply PR.
    intros. apply dcpn12_dcpn. apply PR0.
  - red. apply ucpn12_from_dcpn12_upaco in H.
    eapply upaco12_mon. apply H.
    intros. apply dcpn12_dcpn. apply PR.
Qed.

Lemma ucpn12_compat r: ucpn12 (gf r) <12= gf (ucpn12 r).
Proof.
  intros. destruct PR; cycle 1.
  - apply dcpn12_compat in H.
    eapply gf_mon. apply H.
    intros. right. apply PR.
  - _punfold H; [|apply gf_mon]. eapply gf_mon. apply H.
    intros. apply ucpn12_ucpn.
    eapply upaco12_mon. apply PR.
    intros. eapply dcpn12_mon. apply PR0.
    intros. left. pstep. eapply gf_mon. apply PR1.
    intros. apply ucpn12_base. apply PR2.
Qed.

Lemma ucpn12_init:
  ucpn12 bot12 <12= paco12 gf bot12.
Proof.
  pcofix CIH. intros.
  destruct PR; cycle 1.
  - eapply paco12_mon_bot; [| intros; apply PR].
    eapply paco12_algebra, H. apply gf_mon. intros.
    eapply (dcompat12_compat dcpn12_compat).
    eapply dcpn12_mon. apply PR. contradiction.
  - _punfold H; [|apply gf_mon]. pstep.
    eapply gf_mon. apply H. intros.
    right. apply CIH. apply PR.
Qed.

Lemma pcpn12_final r:
  paco12 gf r <12= pcpn12 r.
Proof.
  intros. eapply paco12_mon. apply PR.
  intros. apply dcpn12_base. apply PR0.
Qed.

Lemma ucpn12_final r:
  upaco12 gf r <12= ucpn12 r.
Proof.
  intros. eapply upaco12_mon. apply PR.
  intros. apply dcpn12_base. apply PR0.
Qed.

Lemma ucpn12_clo
      r clo (LE: clo <13= ucpn12):
  clo (ucpn12 r) <12= ucpn12 r.
Proof.
  intros. apply ucpn12_ucpn, LE, PR.
Qed.

Lemma pcpn12_clo
      r clo (LE: clo <13= ucpn12):
  clo (pcpn12 r) <12= pcpn12 r.
Proof.
  intros. pstep. eapply gf_mon, ucpn12_ucpn.
  apply ucpn12_compat. apply LE in PR.
  eapply ucpn12_mon. apply PR.
  intros. _punfold PR0. apply PR0. apply gf_mon.
Qed.

Lemma pcpn12_unfold r:
  pcpn12 r <12= gf (ucpn12 r).
Proof.
  intros. _punfold PR. apply PR. apply gf_mon.
Qed.

Lemma pcpn12_step r:
  gf (ucpn12 r) <12= pcpn12 r.
Proof.
  intros. pstep. apply PR.
Qed.

Lemma ucpn12_step r:
  gf (ucpn12 r) <12= ucpn12 r.
Proof.
  left. apply pcpn12_step. apply PR.
Qed.

Lemma ucpn12_id r : ucpn12 r <12= ucpn12 r.
Proof. intros. apply PR. Qed.

Lemma pcpn12_id r : pcpn12 r <12= pcpn12 r.
Proof. intros. apply PR. Qed.

Lemma gf_dcpn12_mon: monotone12 (compose gf dcpn12).
Proof.
  repeat intro. eapply gf_mon. apply IN.
  intros. eapply dcpn12_mon. apply PR. apply LE.  
Qed.

Lemma pcpn12_from_paco r: paco12 (compose gf dcpn12) r <12= pcpn12 r.
Proof.
  intros. apply dcpn12_base in PR. revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 PR.
  pcofix CIH. intros.
  pstep.
  eapply gf_mon; cycle 1.
  { instantiate (1:= _ \12/ _). right.
    destruct PR0; [apply CIH, H | apply CIH0, H]. }
  eapply gf_mon, (dcompat12_distr dcpn12_compat).
  eapply gf_mon, dcpn12_dcpn.
  eapply (dcompat12_compat dcpn12_compat).
  eapply dcpn12_mon. apply PR.
  intros. _punfold PR0. apply PR0. apply gf_dcpn12_mon.
Qed.

Lemma pcpn12_to_paco r: pcpn12 r <12= paco12 (compose gf dcpn12) r.
Proof.
  pcofix CIH. intros.
  pstep. _punfold PR; [|apply gf_mon].
  eapply gf_mon. apply PR. intros.
  destruct PR0; cycle 1.
  - eapply dcpn12_mon. apply H. intros.
    right. apply CIH0, PR0. 
  - apply dcpn12_base. right. apply CIH, H.
Qed.

Lemma pcpn12_cofix
    r l (OBG: forall rr (INC: r <12= rr) (CIH: l <12= rr), l <12= pcpn12 rr):
  l <12= pcpn12 r.
Proof.
  under_forall ltac:(apply pcpn12_from_paco).
  pcofix CIH. intros. apply pcpn12_to_paco.
  apply OBG. apply CIH0. apply CIH. apply PR.
Qed.

End PacoCompanion12_main.

Lemma pcpn12_mon_bot (gf gf': rel -> rel) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 r
      (IN: @pcpn12 gf bot12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)
      (MON: monotone12 gf)
      (LE: gf <13= gf'):
  @pcpn12 gf' r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11.
Proof.
  eapply paco12_mon_bot, LE.
  apply ucpn12_init. apply MON. left. apply IN.
Qed.

Lemma ucpn12_mon_bot (gf gf': rel -> rel) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 r
      (IN: @ucpn12 gf bot12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)
      (MON: monotone12 gf)
      (LE: gf <13= gf'):
  @ucpn12 gf' r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11.
Proof.
  eapply upaco12_mon_bot, LE.
  left. apply ucpn12_init. apply MON. apply IN.
Qed.

End PacoCompanion12.

Hint Resolve ucpn12_base : paco.
Hint Resolve pcpn12_step : paco.
Hint Resolve ucpn12_step : paco.

