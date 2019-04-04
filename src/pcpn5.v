Require Export Program.Basics. Open Scope program_scope.
Require Import paco5 pacotac.
Set Implicit Arguments.

Section PacoCompanion5.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.

Local Notation rel := (rel5 T0 T1 T2 T3 T4).

Section PacoCompanion5_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone5 gf.

(** 
  Distributive Compatibility, Distributive Companion, (U)Paco Companion 
*)

Structure dcompatible5 (clo: rel -> rel) : Prop :=
  dcompat5_intro {
      dcompat5_mon: monotone5 clo;
      dcompat5_compat : forall r,
          clo (gf r) <5= gf (clo r);
      dcompat5_distr : forall r1 r2,
          clo (r1 \5/ r2) <5= (clo r1 \5/ clo r2);
    }.

Inductive dcpn5 (r: rel) x0 x1 x2 x3 x4 : Prop :=
| dcpn5_intro
    clo
    (COM: dcompatible5 clo)
    (CLO: clo r x0 x1 x2 x3 x4)
.

Definition pcpn5 r := paco5 gf (dcpn5 r).
Definition ucpn5 r := upaco5 gf (dcpn5 r).

Lemma dcpn5_mon: monotone5 dcpn5.
Proof.
  red; intros.
  destruct IN. exists clo.
  - apply COM.
  - eapply dcompat5_mon.
    + apply COM.
    + apply CLO.
    + apply LE.
Qed.

Lemma pcpn5_mon: monotone5 pcpn5.
Proof.
  red; intros. eapply paco5_mon. apply IN.
  intros. eapply dcpn5_mon. apply PR. apply LE.
Qed.

Lemma ucpn5_mon: monotone5 ucpn5.
Proof.
  red; intros. eapply upaco5_mon. apply IN.
  intros. eapply dcpn5_mon. apply PR. apply LE.
Qed.

Lemma dcpn5_greatest: forall clo (COM: dcompatible5 clo), clo <6= dcpn5.
Proof. intros. econstructor;[apply COM|apply PR]. Qed.

Lemma dcpn5_compat: dcompatible5 dcpn5.
Proof.
  econstructor; [apply dcpn5_mon| |]; intros.
  - destruct PR; eapply gf_mon with (r:=clo r).
    + eapply (dcompat5_compat COM); apply CLO.
    + intros. econstructor; [apply COM|apply PR].
  - destruct PR.
    eapply (dcompat5_distr COM) in CLO.
    destruct CLO.
    + left. eapply dcpn5_greatest. apply COM. apply H.
    + right. eapply dcpn5_greatest. apply COM. apply H.
Qed.

Lemma dcpn5_base: forall r, r <5= dcpn5 r.
Proof.
  exists id; [|apply PR].
  econstructor; repeat intro.
  + apply LE, IN.
  + apply PR0.
  + destruct PR0.
    * left. apply H.
    * right. apply H.
Qed.

Lemma ucpn5_base: forall r, r <5= ucpn5 r.
Proof.
  right. apply dcpn5_base. apply PR.
Qed.

Lemma ucpn5_from_dcpn5_upaco r:
  dcpn5 (upaco5 gf r) <5= ucpn5 r.
Proof.
  intros.
  eapply (dcompat5_distr dcpn5_compat) in PR.
  destruct PR as [IN|IN]; cycle 1.
  - right. apply IN.
  - left. revert x0 x1 x2 x3 x4 IN.
    pcofix CIH. intros.
    pstep. eapply gf_mon.
    + apply (dcompat5_compat dcpn5_compat).
      eapply dcpn5_mon. apply IN.
      intros. _punfold PR. apply PR. apply gf_mon.
    + intros. apply (dcompat5_distr dcpn5_compat) in PR.
      right. destruct PR.
      * apply CIH. apply H.
      * apply CIH0. apply H.
Qed.

Lemma dcpn5_dcpn: forall r,
    dcpn5 (dcpn5 r) <5= dcpn5 r.
Proof.
  intros. exists (compose dcpn5 dcpn5); [|apply PR].
  econstructor.
  - repeat intro. eapply dcpn5_mon; [apply IN|].
    intros. eapply dcpn5_mon; [apply PR0|apply LE].
  - intros. eapply (dcompat5_compat dcpn5_compat).
    eapply dcpn5_mon; [apply PR0|].
    intros. eapply (dcompat5_compat dcpn5_compat), PR1.
  - intros. eapply (dcompat5_distr dcpn5_compat).
    eapply dcpn5_mon, (dcompat5_distr dcpn5_compat).
    apply PR0.
Qed.

Lemma ucpn5_ucpn: forall r,
    ucpn5 (ucpn5 r) <5= ucpn5 r.
Proof.
  intros. destruct PR.
  - left. eapply paco5_mult_strong.
    eapply paco5_mon. apply H.
    intros. apply ucpn5_from_dcpn5_upaco in PR.
    eapply upaco5_mon. apply PR.
    intros. apply dcpn5_dcpn. apply PR0.
  - red. apply ucpn5_from_dcpn5_upaco in H.
    eapply upaco5_mon. apply H.
    intros. apply dcpn5_dcpn. apply PR.
Qed.

Lemma ucpn5_compat r: ucpn5 (gf r) <5= gf (ucpn5 r).
Proof.
  intros. destruct PR; cycle 1.
  - apply dcpn5_compat in H.
    eapply gf_mon. apply H.
    intros. right. apply PR.
  - _punfold H; [|apply gf_mon]. eapply gf_mon. apply H.
    intros. apply ucpn5_ucpn.
    eapply upaco5_mon. apply PR.
    intros. eapply dcpn5_mon. apply PR0.
    intros. left. pstep. eapply gf_mon. apply PR1.
    intros. apply ucpn5_base. apply PR2.
Qed.

Lemma ucpn5_init:
  ucpn5 bot5 <5= paco5 gf bot5.
Proof.
  pcofix CIH. intros.
  destruct PR; cycle 1.
  - eapply paco5_mon_bot; [| intros; apply PR].
    eapply paco5_algebra, H. apply gf_mon. intros.
    eapply (dcompat5_compat dcpn5_compat).
    eapply dcpn5_mon. apply PR. contradiction.
  - _punfold H; [|apply gf_mon]. pstep.
    eapply gf_mon. apply H. intros.
    right. apply CIH. apply PR.
Qed.

Lemma pcpn5_final r:
  paco5 gf r <5= pcpn5 r.
Proof.
  intros. eapply paco5_mon. apply PR.
  intros. apply dcpn5_base. apply PR0.
Qed.

Lemma ucpn5_final r:
  upaco5 gf r <5= ucpn5 r.
Proof.
  intros. eapply upaco5_mon. apply PR.
  intros. apply dcpn5_base. apply PR0.
Qed.

Lemma ucpn5_clo
      r clo (LE: clo <6= ucpn5):
  clo (ucpn5 r) <5= ucpn5 r.
Proof.
  intros. apply ucpn5_ucpn, LE, PR.
Qed.

Lemma pcpn5_clo
      r clo (LE: clo <6= ucpn5):
  clo (pcpn5 r) <5= pcpn5 r.
Proof.
  intros. pstep. eapply gf_mon, ucpn5_ucpn.
  apply ucpn5_compat. apply LE in PR.
  eapply ucpn5_mon. apply PR.
  intros. _punfold PR0. apply PR0. apply gf_mon.
Qed.

Lemma pcpn5_unfold r:
  pcpn5 r <5= gf (ucpn5 r).
Proof.
  intros. _punfold PR. apply PR. apply gf_mon.
Qed.

Lemma pcpn5_step r:
  gf (ucpn5 r) <5= pcpn5 r.
Proof.
  intros. pstep. apply PR.
Qed.

Lemma ucpn5_step r:
  gf (ucpn5 r) <5= ucpn5 r.
Proof.
  left. apply pcpn5_step. apply PR.
Qed.

Lemma ucpn5_id r : ucpn5 r <5= ucpn5 r.
Proof. intros. apply PR. Qed.

Lemma pcpn5_id r : pcpn5 r <5= pcpn5 r.
Proof. intros. apply PR. Qed.

Lemma gf_dcpn5_mon: monotone5 (compose gf dcpn5).
Proof.
  repeat intro. eapply gf_mon. apply IN.
  intros. eapply dcpn5_mon. apply PR. apply LE.  
Qed.

Lemma pcpn5_from_paco r: paco5 (compose gf dcpn5) r <5= pcpn5 r.
Proof.
  intros. apply dcpn5_base in PR. revert x0 x1 x2 x3 x4 PR.
  pcofix CIH. intros.
  pstep.
  eapply gf_mon; cycle 1.
  { instantiate (1:= _ \5/ _). right.
    destruct PR0; [apply CIH, H | apply CIH0, H]. }
  eapply gf_mon, (dcompat5_distr dcpn5_compat).
  eapply gf_mon, dcpn5_dcpn.
  eapply (dcompat5_compat dcpn5_compat).
  eapply dcpn5_mon. apply PR.
  intros. _punfold PR0. apply PR0. apply gf_dcpn5_mon.
Qed.

Lemma pcpn5_to_paco r: pcpn5 r <5= paco5 (compose gf dcpn5) r.
Proof.
  pcofix CIH. intros.
  pstep. _punfold PR; [|apply gf_mon].
  eapply gf_mon. apply PR. intros.
  destruct PR0; cycle 1.
  - eapply dcpn5_mon. apply H. intros.
    right. apply CIH0, PR0. 
  - apply dcpn5_base. right. apply CIH, H.
Qed.

Lemma pcpn5_cofix
    r l (OBG: forall rr (INC: r <5= rr) (CIH: l <5= rr), l <5= pcpn5 rr):
  l <5= pcpn5 r.
Proof.
  under_forall ltac:(apply pcpn5_from_paco).
  pcofix CIH. intros. apply pcpn5_to_paco.
  apply OBG. apply CIH0. apply CIH. apply PR.
Qed.

End PacoCompanion5_main.

Lemma pcpn5_mon_bot (gf gf': rel -> rel) x0 x1 x2 x3 x4 r
      (IN: @pcpn5 gf bot5 x0 x1 x2 x3 x4)
      (MON: monotone5 gf)
      (LE: gf <6= gf'):
  @pcpn5 gf' r x0 x1 x2 x3 x4.
Proof.
  eapply paco5_mon_bot, LE.
  apply ucpn5_init. apply MON. left. apply IN.
Qed.

Lemma ucpn5_mon_bot (gf gf': rel -> rel) x0 x1 x2 x3 x4 r
      (IN: @ucpn5 gf bot5 x0 x1 x2 x3 x4)
      (MON: monotone5 gf)
      (LE: gf <6= gf'):
  @ucpn5 gf' r x0 x1 x2 x3 x4.
Proof.
  eapply upaco5_mon_bot, LE.
  left. apply ucpn5_init. apply MON. apply IN.
Qed.

End PacoCompanion5.

Hint Resolve ucpn5_base : paco.
Hint Resolve pcpn5_step : paco.
Hint Resolve ucpn5_step : paco.

