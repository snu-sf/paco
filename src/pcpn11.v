Require Export Program.Basics. Open Scope program_scope.
Require Import paco11 pacotac.
Set Implicit Arguments.

Section PacoCompanion11.

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

Local Notation rel := (rel11 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10).

Section PacoCompanion11_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone11 gf.

(** 
  Distributive Compatibility, Distributive Companion, (U)Paco Companion 
*)

Structure dcompatible11 (clo: rel -> rel) : Prop :=
  dcompat11_intro {
      dcompat11_mon: monotone11 clo;
      dcompat11_compat : forall r,
          clo (gf r) <11= gf (clo r);
      dcompat11_distr : forall r1 r2,
          clo (r1 \11/ r2) <11= (clo r1 \11/ clo r2);
    }.

Inductive dcpn11 (r: rel) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : Prop :=
| dcpn11_intro
    clo
    (COM: dcompatible11 clo)
    (CLO: clo r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
.

Definition pcpn11 r := paco11 gf (dcpn11 r).
Definition ucpn11 r := upaco11 gf (dcpn11 r).

Lemma dcpn11_mon: monotone11 dcpn11.
Proof.
  red; intros.
  destruct IN. exists clo.
  - apply COM.
  - eapply dcompat11_mon.
    + apply COM.
    + apply CLO.
    + apply LE.
Qed.

Lemma pcpn11_mon: monotone11 pcpn11.
Proof.
  red; intros. eapply paco11_mon. apply IN.
  intros. eapply dcpn11_mon. apply PR. apply LE.
Qed.

Lemma ucpn11_mon: monotone11 ucpn11.
Proof.
  red; intros. eapply upaco11_mon. apply IN.
  intros. eapply dcpn11_mon. apply PR. apply LE.
Qed.

Lemma dcpn11_greatest: forall clo (COM: dcompatible11 clo), clo <12= dcpn11.
Proof. intros. econstructor;[apply COM|apply PR]. Qed.

Lemma dcpn11_compat: dcompatible11 dcpn11.
Proof.
  econstructor; [apply dcpn11_mon| |]; intros.
  - destruct PR; eapply gf_mon with (r:=clo r).
    + eapply (dcompat11_compat COM); apply CLO.
    + intros. econstructor; [apply COM|apply PR].
  - destruct PR.
    eapply (dcompat11_distr COM) in CLO.
    destruct CLO.
    + left. eapply dcpn11_greatest. apply COM. apply H.
    + right. eapply dcpn11_greatest. apply COM. apply H.
Qed.

Lemma dcpn11_base: forall r, r <11= dcpn11 r.
Proof.
  exists id; [|apply PR].
  econstructor; repeat intro.
  + apply LE, IN.
  + apply PR0.
  + destruct PR0.
    * left. apply H.
    * right. apply H.
Qed.

Lemma ucpn11_base: forall r, r <11= ucpn11 r.
Proof.
  right. apply dcpn11_base. apply PR.
Qed.

Lemma ucpn11_from_dcpn11_upaco r:
  dcpn11 (upaco11 gf r) <11= ucpn11 r.
Proof.
  intros.
  eapply (dcompat11_distr dcpn11_compat) in PR.
  destruct PR as [IN|IN]; cycle 1.
  - right. apply IN.
  - left. revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 IN.
    pcofix CIH. intros.
    pstep. eapply gf_mon.
    + apply (dcompat11_compat dcpn11_compat).
      eapply dcpn11_mon. apply IN.
      intros. _punfold PR. apply PR. apply gf_mon.
    + intros. apply (dcompat11_distr dcpn11_compat) in PR.
      right. destruct PR.
      * apply CIH. apply H.
      * apply CIH0. apply H.
Qed.

Lemma dcpn11_dcpn: forall r,
    dcpn11 (dcpn11 r) <11= dcpn11 r.
Proof.
  intros. exists (compose dcpn11 dcpn11); [|apply PR].
  econstructor.
  - repeat intro. eapply dcpn11_mon; [apply IN|].
    intros. eapply dcpn11_mon; [apply PR0|apply LE].
  - intros. eapply (dcompat11_compat dcpn11_compat).
    eapply dcpn11_mon; [apply PR0|].
    intros. eapply (dcompat11_compat dcpn11_compat), PR1.
  - intros. eapply (dcompat11_distr dcpn11_compat).
    eapply dcpn11_mon, (dcompat11_distr dcpn11_compat).
    apply PR0.
Qed.

Lemma ucpn11_ucpn: forall r,
    ucpn11 (ucpn11 r) <11= ucpn11 r.
Proof.
  intros. destruct PR.
  - left. eapply paco11_mult_strong.
    eapply paco11_mon. apply H.
    intros. apply ucpn11_from_dcpn11_upaco in PR.
    eapply upaco11_mon. apply PR.
    intros. apply dcpn11_dcpn. apply PR0.
  - red. apply ucpn11_from_dcpn11_upaco in H.
    eapply upaco11_mon. apply H.
    intros. apply dcpn11_dcpn. apply PR.
Qed.

Lemma ucpn11_compat r: ucpn11 (gf r) <11= gf (ucpn11 r).
Proof.
  intros. destruct PR; cycle 1.
  - apply dcpn11_compat in H.
    eapply gf_mon. apply H.
    intros. right. apply PR.
  - _punfold H; [|apply gf_mon]. eapply gf_mon. apply H.
    intros. apply ucpn11_ucpn.
    eapply upaco11_mon. apply PR.
    intros. eapply dcpn11_mon. apply PR0.
    intros. left. pstep. eapply gf_mon. apply PR1.
    intros. apply ucpn11_base. apply PR2.
Qed.

Lemma ucpn11_init:
  ucpn11 bot11 <11= paco11 gf bot11.
Proof.
  pcofix CIH. intros.
  destruct PR; cycle 1.
  - eapply paco11_mon_bot; [| intros; apply PR].
    eapply paco11_algebra, H. apply gf_mon. intros.
    eapply (dcompat11_compat dcpn11_compat).
    eapply dcpn11_mon. apply PR. contradiction.
  - _punfold H; [|apply gf_mon]. pstep.
    eapply gf_mon. apply H. intros.
    right. apply CIH. apply PR.
Qed.

Lemma pcpn11_final r:
  paco11 gf r <11= pcpn11 r.
Proof.
  intros. eapply paco11_mon. apply PR.
  intros. apply dcpn11_base. apply PR0.
Qed.

Lemma ucpn11_final r:
  upaco11 gf r <11= ucpn11 r.
Proof.
  intros. eapply upaco11_mon. apply PR.
  intros. apply dcpn11_base. apply PR0.
Qed.

Lemma ucpn11_clo
      r clo (LE: clo <12= ucpn11):
  clo (ucpn11 r) <11= ucpn11 r.
Proof.
  intros. apply ucpn11_ucpn, LE, PR.
Qed.

Lemma pcpn11_clo
      r clo (LE: clo <12= ucpn11):
  clo (pcpn11 r) <11= pcpn11 r.
Proof.
  intros. pstep. eapply gf_mon, ucpn11_ucpn.
  apply ucpn11_compat. apply LE in PR.
  eapply ucpn11_mon. apply PR.
  intros. _punfold PR0. apply PR0. apply gf_mon.
Qed.

Lemma pcpn11_unfold r:
  pcpn11 r <11= gf (ucpn11 r).
Proof.
  intros. _punfold PR. apply PR. apply gf_mon.
Qed.

Lemma ucpn11_unfold:
  ucpn11 bot11 <11= gf(ucpn11 bot11).
Proof.
  intros. apply pcpn11_unfold, pcpn11_final, ucpn11_init, PR.
Qed.

Lemma pcpn11_step r:
  gf (ucpn11 r) <11= pcpn11 r.
Proof.
  intros. pstep. apply PR.
Qed.

Lemma ucpn11_step r:
  gf (ucpn11 r) <11= ucpn11 r.
Proof.
  left. apply pcpn11_step. apply PR.
Qed.

Lemma ucpn11_id r : ucpn11 r <11= ucpn11 r.
Proof. intros. apply PR. Qed.

Lemma pcpn11_id r : pcpn11 r <11= pcpn11 r.
Proof. intros. apply PR. Qed.

Lemma gf_dcpn11_mon: monotone11 (compose gf dcpn11).
Proof.
  repeat intro. eapply gf_mon. apply IN.
  intros. eapply dcpn11_mon. apply PR. apply LE.  
Qed.

Lemma pcpn11_from_paco r: paco11 (compose gf dcpn11) r <11= pcpn11 r.
Proof.
  intros. apply dcpn11_base in PR. revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 PR.
  pcofix CIH. intros.
  pstep.
  eapply gf_mon; cycle 1.
  { instantiate (1:= _ \11/ _). right.
    destruct PR0; [apply CIH, H | apply CIH0, H]. }
  eapply gf_mon, (dcompat11_distr dcpn11_compat).
  eapply gf_mon, dcpn11_dcpn.
  eapply (dcompat11_compat dcpn11_compat).
  eapply dcpn11_mon. apply PR.
  intros. _punfold PR0. apply PR0. apply gf_dcpn11_mon.
Qed.

Lemma pcpn11_to_paco r: pcpn11 r <11= paco11 (compose gf dcpn11) r.
Proof.
  pcofix CIH. intros.
  pstep. _punfold PR; [|apply gf_mon].
  eapply gf_mon. apply PR. intros.
  destruct PR0; cycle 1.
  - eapply dcpn11_mon. apply H. intros.
    right. apply CIH0, PR0. 
  - apply dcpn11_base. right. apply CIH, H.
Qed.

Lemma pcpn11_cofix
    r l (OBG: forall rr (INC: r <11= rr) (CIH: l <11= rr), l <11= pcpn11 rr):
  l <11= pcpn11 r.
Proof.
  under_forall ltac:(apply pcpn11_from_paco).
  pcofix CIH. intros. apply pcpn11_to_paco.
  apply OBG. apply CIH0. apply CIH. apply PR.
Qed.

(**
  Recursive Closure & Weak Compatibility
*)

Inductive rclo11 (clo: rel->rel) (r: rel): rel :=
| rclo11_base
    x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
    (R: r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10):
    @rclo11 clo r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
| rclo11_clo'
    r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
    (R': r' <11= rclo11 clo r)
    (CLOR': clo r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10):
    @rclo11 clo r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
| rclo11_dcpn'
    r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
    (R': r' <11= rclo11 clo r)
    (CLOR': @dcpn11 r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10):
    @rclo11 clo r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
.

Structure wdcompatible11 (clo: rel -> rel) : Prop :=
  wdcompat11_intro {
      wdcompat11_mon: monotone11 clo;
      wdcompat11_wcompat: forall r,
          clo (gf r) <11= gf (rclo11 clo r);
      wdcompat11_distr : forall r1 r2,
          clo (r1 \11/ r2) <11= (clo r1 \11/ clo r2);
    }.

Lemma rclo11_mon_gen clo clo' r r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
      (IN: @rclo11 clo r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
      (LEclo: clo <12= clo')
      (LEr: r <11= r') :
  @rclo11 clo' r' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10.
Proof.
  induction IN; intros.
  - econstructor 1. apply LEr, R.
  - econstructor 2; [intros; eapply H, PR|apply LEclo, CLOR'].
  - econstructor 3; [intros; eapply H, PR|].
    eapply dcpn11_mon; [apply CLOR'|].
    intros. apply PR.
Qed.

Lemma rclo11_mon clo:
  monotone11 (rclo11 clo).
Proof.
  repeat intro. eapply rclo11_mon_gen; [apply IN|intros; apply PR|apply LE].
Qed.

Lemma rclo11_clo clo r:
  clo (rclo11 clo r) <11= rclo11 clo r.
Proof.
  intros. econstructor 2; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo11_dcpn clo r:
  dcpn11 (rclo11 clo r) <11= rclo11 clo r.
Proof.
  intros. econstructor 3; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo11_mult clo r:
  rclo11 clo (rclo11 clo r) <11= rclo11 clo r.
Proof.
  intros. induction PR.
  - apply R.
  - econstructor 2; [eapply H | eapply CLOR'].
  - econstructor 3; [eapply H | eapply CLOR'].
Qed.

Lemma rclo11_compose clo r:
  rclo11 (rclo11 clo) r <11= rclo11 clo r.
Proof.
  intros. induction PR.
  - apply rclo11_base, R.
  - apply rclo11_mult.
    eapply rclo11_mon; [apply CLOR'|apply H].
  - apply rclo11_dcpn.
    eapply dcpn11_mon; [apply CLOR'|apply H].
Qed.

Lemma wdcompat11_dcompat
      clo (WCOM: wdcompatible11 clo):
  dcompatible11 (rclo11 clo).
Proof.
  econstructor; [eapply rclo11_mon| |]; intros.
  - induction PR; intros.
    + eapply gf_mon; [apply R|]. intros.
      apply rclo11_base. apply PR.
    + eapply gf_mon.
      * eapply (wdcompat11_wcompat WCOM).
        eapply (wdcompat11_mon WCOM); [apply CLOR'|apply H].
      * intros. apply rclo11_mult, PR.
    + eapply gf_mon; [|intros; apply rclo11_dcpn, PR].
      eapply (dcompat11_compat dcpn11_compat).
      eapply dcpn11_mon; [apply CLOR'|apply H].
  - induction PR; intros.
    + destruct R as [R|R]; [left | right]; econstructor; apply R.
    + assert (CLOR:= wdcompat11_mon WCOM _ _ _ CLOR' H).
      eapply (wdcompat11_distr WCOM) in CLOR.
      destruct CLOR as [CLOR|CLOR]; [left|right]; apply rclo11_clo, CLOR.
    + assert (CLOR:= dcpn11_mon _ CLOR' H).
      eapply (dcompat11_distr dcpn11_compat) in CLOR.
      destruct CLOR as [CLOR|CLOR]; [left|right]; apply rclo11_dcpn, CLOR.
Qed.

Lemma wcompat11_sound clo (WCOM: wdcompatible11 clo):
  clo <12= dcpn11.
Proof.
  intros. exists (rclo11 clo).
  - apply wdcompat11_dcompat, WCOM.
  - apply rclo11_clo.
    eapply (wdcompat11_mon WCOM); [apply PR|].
    intros. apply rclo11_base, PR0.
Qed.

End PacoCompanion11_main.

Lemma pcpn11_mon_bot (gf gf': rel -> rel) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 r
      (IN: @pcpn11 gf bot11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
      (MON: monotone11 gf)
      (LE: gf <12= gf'):
  @pcpn11 gf' r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10.
Proof.
  eapply paco11_mon_bot, LE.
  apply ucpn11_init. apply MON. left. apply IN.
Qed.

Lemma ucpn11_mon_bot (gf gf': rel -> rel) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 r
      (IN: @ucpn11 gf bot11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
      (MON: monotone11 gf)
      (LE: gf <12= gf'):
  @ucpn11 gf' r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10.
Proof.
  eapply upaco11_mon_bot, LE.
  left. apply ucpn11_init. apply MON. apply IN.
Qed.

End PacoCompanion11.

Hint Resolve ucpn11_base : paco.
Hint Resolve pcpn11_step : paco.
Hint Resolve ucpn11_step : paco.

Hint Constructors rclo11 : rclo.
Hint Resolve rclo11_clo rclo11_dcpn : rclo.
