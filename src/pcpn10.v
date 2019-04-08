Require Export Program.Basics. Open Scope program_scope.
Require Import paco10 pacotac.
Set Implicit Arguments.

Section PacoCompanion10.

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

Local Notation rel := (rel10 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9).

Section PacoCompanion10_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone10 gf.

(** 
  Distributive Compatibility, Distributive Companion, (U)Paco Companion 
*)

Structure dcompatible10 (clo: rel -> rel) : Prop :=
  dcompat10_intro {
      dcompat10_mon: monotone10 clo;
      dcompat10_compat : forall r,
          clo (gf r) <10= gf (clo r);
      dcompat10_distr : forall r1 r2,
          clo (r1 \10/ r2) <10= (clo r1 \10/ clo r2);
    }.

Inductive dcpn10 (r: rel) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Prop :=
| dcpn10_intro
    clo
    (COM: dcompatible10 clo)
    (CLO: clo r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)
.

Definition pcpn10 r := paco10 gf (dcpn10 r).
Definition ucpn10 r := upaco10 gf (dcpn10 r).

Lemma dcpn10_mon: monotone10 dcpn10.
Proof.
  red; intros.
  destruct IN. exists clo.
  - apply COM.
  - eapply dcompat10_mon.
    + apply COM.
    + apply CLO.
    + apply LE.
Qed.

Lemma pcpn10_mon: monotone10 pcpn10.
Proof.
  red; intros. eapply paco10_mon. apply IN.
  intros. eapply dcpn10_mon. apply PR. apply LE.
Qed.

Lemma ucpn10_mon: monotone10 ucpn10.
Proof.
  red; intros. eapply upaco10_mon. apply IN.
  intros. eapply dcpn10_mon. apply PR. apply LE.
Qed.

Lemma dcpn10_greatest: forall clo (COM: dcompatible10 clo), clo <11= dcpn10.
Proof. intros. econstructor;[apply COM|apply PR]. Qed.

Lemma dcpn10_compat: dcompatible10 dcpn10.
Proof.
  econstructor; [apply dcpn10_mon| |]; intros.
  - destruct PR; eapply gf_mon with (r:=clo r).
    + eapply (dcompat10_compat COM); apply CLO.
    + intros. econstructor; [apply COM|apply PR].
  - destruct PR.
    eapply (dcompat10_distr COM) in CLO.
    destruct CLO.
    + left. eapply dcpn10_greatest. apply COM. apply H.
    + right. eapply dcpn10_greatest. apply COM. apply H.
Qed.

Lemma dcpn10_base: forall r, r <10= dcpn10 r.
Proof.
  exists id; [|apply PR].
  econstructor; repeat intro.
  + apply LE, IN.
  + apply PR0.
  + destruct PR0.
    * left. apply H.
    * right. apply H.
Qed.

Lemma ucpn10_base: forall r, r <10= ucpn10 r.
Proof.
  right. apply dcpn10_base. apply PR.
Qed.

Lemma ucpn10_from_dcpn10_upaco r:
  dcpn10 (upaco10 gf r) <10= ucpn10 r.
Proof.
  intros.
  eapply (dcompat10_distr dcpn10_compat) in PR.
  destruct PR as [IN|IN]; cycle 1.
  - right. apply IN.
  - left. revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 IN.
    pcofix CIH. intros.
    pstep. eapply gf_mon.
    + apply (dcompat10_compat dcpn10_compat).
      eapply dcpn10_mon. apply IN.
      intros. _punfold PR. apply PR. apply gf_mon.
    + intros. apply (dcompat10_distr dcpn10_compat) in PR.
      right. destruct PR.
      * apply CIH. apply H.
      * apply CIH0. apply H.
Qed.

Lemma dcpn10_dcpn: forall r,
    dcpn10 (dcpn10 r) <10= dcpn10 r.
Proof.
  intros. exists (compose dcpn10 dcpn10); [|apply PR].
  econstructor.
  - repeat intro. eapply dcpn10_mon; [apply IN|].
    intros. eapply dcpn10_mon; [apply PR0|apply LE].
  - intros. eapply (dcompat10_compat dcpn10_compat).
    eapply dcpn10_mon; [apply PR0|].
    intros. eapply (dcompat10_compat dcpn10_compat), PR1.
  - intros. eapply (dcompat10_distr dcpn10_compat).
    eapply dcpn10_mon, (dcompat10_distr dcpn10_compat).
    apply PR0.
Qed.

Lemma ucpn10_ucpn: forall r,
    ucpn10 (ucpn10 r) <10= ucpn10 r.
Proof.
  intros. destruct PR.
  - left. eapply paco10_mult_strong.
    eapply paco10_mon. apply H.
    intros. apply ucpn10_from_dcpn10_upaco in PR.
    eapply upaco10_mon. apply PR.
    intros. apply dcpn10_dcpn. apply PR0.
  - red. apply ucpn10_from_dcpn10_upaco in H.
    eapply upaco10_mon. apply H.
    intros. apply dcpn10_dcpn. apply PR.
Qed.

Lemma ucpn10_compat r: ucpn10 (gf r) <10= gf (ucpn10 r).
Proof.
  intros. destruct PR; cycle 1.
  - apply dcpn10_compat in H.
    eapply gf_mon. apply H.
    intros. right. apply PR.
  - _punfold H; [|apply gf_mon]. eapply gf_mon. apply H.
    intros. apply ucpn10_ucpn.
    eapply upaco10_mon. apply PR.
    intros. eapply dcpn10_mon. apply PR0.
    intros. left. pstep. eapply gf_mon. apply PR1.
    intros. apply ucpn10_base. apply PR2.
Qed.

Lemma ucpn10_init:
  ucpn10 bot10 <10= paco10 gf bot10.
Proof.
  pcofix CIH. intros.
  destruct PR; cycle 1.
  - eapply paco10_mon_bot; [| intros; apply PR].
    eapply paco10_algebra, H. apply gf_mon. intros.
    eapply (dcompat10_compat dcpn10_compat).
    eapply dcpn10_mon. apply PR. contradiction.
  - _punfold H; [|apply gf_mon]. pstep.
    eapply gf_mon. apply H. intros.
    right. apply CIH. apply PR.
Qed.

Lemma pcpn10_final r:
  paco10 gf r <10= pcpn10 r.
Proof.
  intros. eapply paco10_mon. apply PR.
  intros. apply dcpn10_base. apply PR0.
Qed.

Lemma ucpn10_final r:
  upaco10 gf r <10= ucpn10 r.
Proof.
  intros. eapply upaco10_mon. apply PR.
  intros. apply dcpn10_base. apply PR0.
Qed.

Lemma ucpn10_clo
      r clo (LE: clo <11= ucpn10):
  clo (ucpn10 r) <10= ucpn10 r.
Proof.
  intros. apply ucpn10_ucpn, LE, PR.
Qed.

Lemma pcpn10_clo
      r clo (LE: clo <11= ucpn10):
  clo (pcpn10 r) <10= pcpn10 r.
Proof.
  intros. pstep. eapply gf_mon, ucpn10_ucpn.
  apply ucpn10_compat. apply LE in PR.
  eapply ucpn10_mon. apply PR.
  intros. _punfold PR0. apply PR0. apply gf_mon.
Qed.

Lemma pcpn10_unfold r:
  pcpn10 r <10= gf (ucpn10 r).
Proof.
  intros. _punfold PR. apply PR. apply gf_mon.
Qed.

Lemma ucpn10_unfold:
  ucpn10 bot10 <10= gf(ucpn10 bot10).
Proof.
  intros. apply pcpn10_unfold, pcpn10_final, ucpn10_init, PR.
Qed.

Lemma pcpn10_step r:
  gf (ucpn10 r) <10= pcpn10 r.
Proof.
  intros. pstep. apply PR.
Qed.

Lemma ucpn10_step r:
  gf (ucpn10 r) <10= ucpn10 r.
Proof.
  left. apply pcpn10_step. apply PR.
Qed.

Lemma ucpn10_id r : ucpn10 r <10= ucpn10 r.
Proof. intros. apply PR. Qed.

Lemma pcpn10_id r : pcpn10 r <10= pcpn10 r.
Proof. intros. apply PR. Qed.

Lemma gf_dcpn10_mon: monotone10 (compose gf dcpn10).
Proof.
  repeat intro. eapply gf_mon. apply IN.
  intros. eapply dcpn10_mon. apply PR. apply LE.  
Qed.

Lemma pcpn10_from_paco r: paco10 (compose gf dcpn10) r <10= pcpn10 r.
Proof.
  intros. apply dcpn10_base in PR. revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 PR.
  pcofix CIH. intros.
  pstep.
  eapply gf_mon; cycle 1.
  { instantiate (1:= _ \10/ _). right.
    destruct PR0; [apply CIH, H | apply CIH0, H]. }
  eapply gf_mon, (dcompat10_distr dcpn10_compat).
  eapply gf_mon, dcpn10_dcpn.
  eapply (dcompat10_compat dcpn10_compat).
  eapply dcpn10_mon. apply PR.
  intros. _punfold PR0. apply PR0. apply gf_dcpn10_mon.
Qed.

Lemma pcpn10_to_paco r: pcpn10 r <10= paco10 (compose gf dcpn10) r.
Proof.
  pcofix CIH. intros.
  pstep. _punfold PR; [|apply gf_mon].
  eapply gf_mon. apply PR. intros.
  destruct PR0; cycle 1.
  - eapply dcpn10_mon. apply H. intros.
    right. apply CIH0, PR0. 
  - apply dcpn10_base. right. apply CIH, H.
Qed.

Lemma pcpn10_cofix
    r l (OBG: forall rr (INC: r <10= rr) (CIH: l <10= rr), l <10= pcpn10 rr):
  l <10= pcpn10 r.
Proof.
  under_forall ltac:(apply pcpn10_from_paco).
  pcofix CIH. intros. apply pcpn10_to_paco.
  apply OBG. apply CIH0. apply CIH. apply PR.
Qed.

(**
  Recursive Closure & Weak Compatibility
*)

Inductive rclo10 (clo: rel->rel) (r: rel): rel :=
| rclo10_base
    x0 x1 x2 x3 x4 x5 x6 x7 x8 x9
    (R: r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9):
    @rclo10 clo r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9
| rclo10_clo'
    r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9
    (R': r' <10= rclo10 clo r)
    (CLOR': clo r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9):
    @rclo10 clo r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9
| rclo10_dcpn'
    r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9
    (R': r' <10= rclo10 clo r)
    (CLOR': @dcpn10 r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9):
    @rclo10 clo r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9
.

Structure wdcompatible10 (clo: rel -> rel) : Prop :=
  wdcompat10_intro {
      wdcompat10_mon: monotone10 clo;
      wdcompat10_wcompat: forall r,
          clo (gf r) <10= gf (rclo10 clo r);
      wdcompat10_distr : forall r1 r2,
          clo (r1 \10/ r2) <10= (clo r1 \10/ clo r2);
    }.

Lemma rclo10_mon_gen clo clo' r r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9
      (IN: @rclo10 clo r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)
      (LEclo: clo <11= clo')
      (LEr: r <10= r') :
  @rclo10 clo' r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9.
Proof.
  induction IN; intros.
  - econstructor 1. apply LEr, R.
  - econstructor 2; [intros; eapply H, PR|apply LEclo, CLOR'].
  - econstructor 3; [intros; eapply H, PR|].
    eapply dcpn10_mon; [apply CLOR'|].
    intros. apply PR.
Qed.

Lemma rclo10_mon clo:
  monotone10 (rclo10 clo).
Proof.
  repeat intro. eapply rclo10_mon_gen; [apply IN|intros; apply PR|apply LE].
Qed.

Lemma rclo10_clo clo r:
  clo (rclo10 clo r) <10= rclo10 clo r.
Proof.
  intros. econstructor 2; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo10_dcpn clo r:
  dcpn10 (rclo10 clo r) <10= rclo10 clo r.
Proof.
  intros. econstructor 3; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo10_mult clo r:
  rclo10 clo (rclo10 clo r) <10= rclo10 clo r.
Proof.
  intros. induction PR.
  - apply R.
  - econstructor 2; [eapply H | eapply CLOR'].
  - econstructor 3; [eapply H | eapply CLOR'].
Qed.

Lemma rclo10_compose clo r:
  rclo10 (rclo10 clo) r <10= rclo10 clo r.
Proof.
  intros. induction PR.
  - apply rclo10_base, R.
  - apply rclo10_mult.
    eapply rclo10_mon; [apply CLOR'|apply H].
  - apply rclo10_dcpn.
    eapply dcpn10_mon; [apply CLOR'|apply H].
Qed.

Lemma wdcompat10_dcompat
      clo (WCOM: wdcompatible10 clo):
  dcompatible10 (rclo10 clo).
Proof.
  econstructor; [eapply rclo10_mon| |]; intros.
  - induction PR; intros.
    + eapply gf_mon; [apply R|]. intros.
      apply rclo10_base. apply PR.
    + eapply gf_mon.
      * eapply (wdcompat10_wcompat WCOM).
        eapply (wdcompat10_mon WCOM); [apply CLOR'|apply H].
      * intros. apply rclo10_mult, PR.
    + eapply gf_mon; [|intros; apply rclo10_dcpn, PR].
      eapply (dcompat10_compat dcpn10_compat).
      eapply dcpn10_mon; [apply CLOR'|apply H].
  - induction PR; intros.
    + destruct R as [R|R]; [left | right]; econstructor; apply R.
    + assert (CLOR:= wdcompat10_mon WCOM _ _ _ CLOR' H).
      eapply (wdcompat10_distr WCOM) in CLOR.
      destruct CLOR as [CLOR|CLOR]; [left|right]; apply rclo10_clo, CLOR.
    + assert (CLOR:= dcpn10_mon _ CLOR' H).
      eapply (dcompat10_distr dcpn10_compat) in CLOR.
      destruct CLOR as [CLOR|CLOR]; [left|right]; apply rclo10_dcpn, CLOR.
Qed.

Lemma wcompat10_sound clo (WCOM: wdcompatible10 clo):
  clo <11= dcpn10.
Proof.
  intros. exists (rclo10 clo).
  - apply wdcompat10_dcompat, WCOM.
  - apply rclo10_clo.
    eapply (wdcompat10_mon WCOM); [apply PR|].
    intros. apply rclo10_base, PR0.
Qed.

End PacoCompanion10_main.

Lemma pcpn10_mon_bot (gf gf': rel -> rel) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 r
      (IN: @pcpn10 gf bot10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)
      (MON: monotone10 gf)
      (LE: gf <11= gf'):
  @pcpn10 gf' r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9.
Proof.
  eapply paco10_mon_bot, LE.
  apply ucpn10_init. apply MON. left. apply IN.
Qed.

Lemma ucpn10_mon_bot (gf gf': rel -> rel) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 r
      (IN: @ucpn10 gf bot10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)
      (MON: monotone10 gf)
      (LE: gf <11= gf'):
  @ucpn10 gf' r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9.
Proof.
  eapply upaco10_mon_bot, LE.
  left. apply ucpn10_init. apply MON. apply IN.
Qed.

End PacoCompanion10.

Hint Resolve ucpn10_base : paco.
Hint Resolve pcpn10_step : paco.
Hint Resolve ucpn10_step : paco.

Hint Constructors rclo10 : rclo.
Hint Resolve rclo10_clo rclo10_dcpn : rclo.
