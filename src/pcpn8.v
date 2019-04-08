Require Export Program.Basics. Open Scope program_scope.
Require Import paco8 pacotac.
Set Implicit Arguments.

Section PacoCompanion8.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
Variable T7 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5), Type.

Local Notation rel := (rel8 T0 T1 T2 T3 T4 T5 T6 T7).

Section PacoCompanion8_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone8 gf.

(** 
  Distributive Compatibility, Distributive Companion, (U)Paco Companion 
*)

Structure dcompatible8 (clo: rel -> rel) : Prop :=
  dcompat8_intro {
      dcompat8_mon: monotone8 clo;
      dcompat8_compat : forall r,
          clo (gf r) <8= gf (clo r);
      dcompat8_distr : forall r1 r2,
          clo (r1 \8/ r2) <8= (clo r1 \8/ clo r2);
    }.

Inductive dcpn8 (r: rel) x0 x1 x2 x3 x4 x5 x6 x7 : Prop :=
| dcpn8_intro
    clo
    (COM: dcompatible8 clo)
    (CLO: clo r x0 x1 x2 x3 x4 x5 x6 x7)
.

Definition pcpn8 r := paco8 gf (dcpn8 r).
Definition ucpn8 r := upaco8 gf (dcpn8 r).

Lemma dcpn8_mon: monotone8 dcpn8.
Proof.
  red; intros.
  destruct IN. exists clo.
  - apply COM.
  - eapply dcompat8_mon.
    + apply COM.
    + apply CLO.
    + apply LE.
Qed.

Lemma pcpn8_mon: monotone8 pcpn8.
Proof.
  red; intros. eapply paco8_mon. apply IN.
  intros. eapply dcpn8_mon. apply PR. apply LE.
Qed.

Lemma ucpn8_mon: monotone8 ucpn8.
Proof.
  red; intros. eapply upaco8_mon. apply IN.
  intros. eapply dcpn8_mon. apply PR. apply LE.
Qed.

Lemma dcpn8_greatest: forall clo (COM: dcompatible8 clo), clo <9= dcpn8.
Proof. intros. econstructor;[apply COM|apply PR]. Qed.

Lemma dcpn8_compat: dcompatible8 dcpn8.
Proof.
  econstructor; [apply dcpn8_mon| |]; intros.
  - destruct PR; eapply gf_mon with (r:=clo r).
    + eapply (dcompat8_compat COM); apply CLO.
    + intros. econstructor; [apply COM|apply PR].
  - destruct PR.
    eapply (dcompat8_distr COM) in CLO.
    destruct CLO.
    + left. eapply dcpn8_greatest. apply COM. apply H.
    + right. eapply dcpn8_greatest. apply COM. apply H.
Qed.

Lemma dcpn8_base: forall r, r <8= dcpn8 r.
Proof.
  exists id; [|apply PR].
  econstructor; repeat intro.
  + apply LE, IN.
  + apply PR0.
  + destruct PR0.
    * left. apply H.
    * right. apply H.
Qed.

Lemma ucpn8_base: forall r, r <8= ucpn8 r.
Proof.
  right. apply dcpn8_base. apply PR.
Qed.

Lemma ucpn8_from_dcpn8_upaco r:
  dcpn8 (upaco8 gf r) <8= ucpn8 r.
Proof.
  intros.
  eapply (dcompat8_distr dcpn8_compat) in PR.
  destruct PR as [IN|IN]; cycle 1.
  - right. apply IN.
  - left. revert x0 x1 x2 x3 x4 x5 x6 x7 IN.
    pcofix CIH. intros.
    pstep. eapply gf_mon.
    + apply (dcompat8_compat dcpn8_compat).
      eapply dcpn8_mon. apply IN.
      intros. _punfold PR. apply PR. apply gf_mon.
    + intros. apply (dcompat8_distr dcpn8_compat) in PR.
      right. destruct PR.
      * apply CIH. apply H.
      * apply CIH0. apply H.
Qed.

Lemma dcpn8_dcpn: forall r,
    dcpn8 (dcpn8 r) <8= dcpn8 r.
Proof.
  intros. exists (compose dcpn8 dcpn8); [|apply PR].
  econstructor.
  - repeat intro. eapply dcpn8_mon; [apply IN|].
    intros. eapply dcpn8_mon; [apply PR0|apply LE].
  - intros. eapply (dcompat8_compat dcpn8_compat).
    eapply dcpn8_mon; [apply PR0|].
    intros. eapply (dcompat8_compat dcpn8_compat), PR1.
  - intros. eapply (dcompat8_distr dcpn8_compat).
    eapply dcpn8_mon, (dcompat8_distr dcpn8_compat).
    apply PR0.
Qed.

Lemma ucpn8_ucpn: forall r,
    ucpn8 (ucpn8 r) <8= ucpn8 r.
Proof.
  intros. destruct PR.
  - left. eapply paco8_mult_strong.
    eapply paco8_mon. apply H.
    intros. apply ucpn8_from_dcpn8_upaco in PR.
    eapply upaco8_mon. apply PR.
    intros. apply dcpn8_dcpn. apply PR0.
  - red. apply ucpn8_from_dcpn8_upaco in H.
    eapply upaco8_mon. apply H.
    intros. apply dcpn8_dcpn. apply PR.
Qed.

Lemma ucpn8_compat r: ucpn8 (gf r) <8= gf (ucpn8 r).
Proof.
  intros. destruct PR; cycle 1.
  - apply dcpn8_compat in H.
    eapply gf_mon. apply H.
    intros. right. apply PR.
  - _punfold H; [|apply gf_mon]. eapply gf_mon. apply H.
    intros. apply ucpn8_ucpn.
    eapply upaco8_mon. apply PR.
    intros. eapply dcpn8_mon. apply PR0.
    intros. left. pstep. eapply gf_mon. apply PR1.
    intros. apply ucpn8_base. apply PR2.
Qed.

Lemma ucpn8_init:
  ucpn8 bot8 <8= paco8 gf bot8.
Proof.
  pcofix CIH. intros.
  destruct PR; cycle 1.
  - eapply paco8_mon_bot; [| intros; apply PR].
    eapply paco8_algebra, H. apply gf_mon. intros.
    eapply (dcompat8_compat dcpn8_compat).
    eapply dcpn8_mon. apply PR. contradiction.
  - _punfold H; [|apply gf_mon]. pstep.
    eapply gf_mon. apply H. intros.
    right. apply CIH. apply PR.
Qed.

Lemma pcpn8_final r:
  paco8 gf r <8= pcpn8 r.
Proof.
  intros. eapply paco8_mon. apply PR.
  intros. apply dcpn8_base. apply PR0.
Qed.

Lemma ucpn8_final r:
  upaco8 gf r <8= ucpn8 r.
Proof.
  intros. eapply upaco8_mon. apply PR.
  intros. apply dcpn8_base. apply PR0.
Qed.

Lemma ucpn8_clo
      r clo (LE: clo <9= ucpn8):
  clo (ucpn8 r) <8= ucpn8 r.
Proof.
  intros. apply ucpn8_ucpn, LE, PR.
Qed.

Lemma pcpn8_clo
      r clo (LE: clo <9= ucpn8):
  clo (pcpn8 r) <8= pcpn8 r.
Proof.
  intros. pstep. eapply gf_mon, ucpn8_ucpn.
  apply ucpn8_compat. apply LE in PR.
  eapply ucpn8_mon. apply PR.
  intros. _punfold PR0. apply PR0. apply gf_mon.
Qed.

Lemma pcpn8_unfold r:
  pcpn8 r <8= gf (ucpn8 r).
Proof.
  intros. _punfold PR. apply PR. apply gf_mon.
Qed.

Lemma ucpn8_unfold:
  ucpn8 bot8 <8= gf(ucpn8 bot8).
Proof.
  intros. apply pcpn8_unfold, pcpn8_final, ucpn8_init, PR.
Qed.

Lemma pcpn8_step r:
  gf (ucpn8 r) <8= pcpn8 r.
Proof.
  intros. pstep. apply PR.
Qed.

Lemma ucpn8_step r:
  gf (ucpn8 r) <8= ucpn8 r.
Proof.
  left. apply pcpn8_step. apply PR.
Qed.

Lemma ucpn8_id r : ucpn8 r <8= ucpn8 r.
Proof. intros. apply PR. Qed.

Lemma pcpn8_id r : pcpn8 r <8= pcpn8 r.
Proof. intros. apply PR. Qed.

Lemma gf_dcpn8_mon: monotone8 (compose gf dcpn8).
Proof.
  repeat intro. eapply gf_mon. apply IN.
  intros. eapply dcpn8_mon. apply PR. apply LE.  
Qed.

Lemma pcpn8_from_paco r: paco8 (compose gf dcpn8) r <8= pcpn8 r.
Proof.
  intros. apply dcpn8_base in PR. revert x0 x1 x2 x3 x4 x5 x6 x7 PR.
  pcofix CIH. intros.
  pstep.
  eapply gf_mon; cycle 1.
  { instantiate (1:= _ \8/ _). right.
    destruct PR0; [apply CIH, H | apply CIH0, H]. }
  eapply gf_mon, (dcompat8_distr dcpn8_compat).
  eapply gf_mon, dcpn8_dcpn.
  eapply (dcompat8_compat dcpn8_compat).
  eapply dcpn8_mon. apply PR.
  intros. _punfold PR0. apply PR0. apply gf_dcpn8_mon.
Qed.

Lemma pcpn8_to_paco r: pcpn8 r <8= paco8 (compose gf dcpn8) r.
Proof.
  pcofix CIH. intros.
  pstep. _punfold PR; [|apply gf_mon].
  eapply gf_mon. apply PR. intros.
  destruct PR0; cycle 1.
  - eapply dcpn8_mon. apply H. intros.
    right. apply CIH0, PR0. 
  - apply dcpn8_base. right. apply CIH, H.
Qed.

Lemma pcpn8_cofix
    r l (OBG: forall rr (INC: r <8= rr) (CIH: l <8= rr), l <8= pcpn8 rr):
  l <8= pcpn8 r.
Proof.
  under_forall ltac:(apply pcpn8_from_paco).
  pcofix CIH. intros. apply pcpn8_to_paco.
  apply OBG. apply CIH0. apply CIH. apply PR.
Qed.

(**
  Recursive Closure & Weak Compatibility
*)

Inductive rclo8 (clo: rel->rel) (r: rel): rel :=
| rclo8_base
    x0 x1 x2 x3 x4 x5 x6 x7
    (R: r x0 x1 x2 x3 x4 x5 x6 x7):
    @rclo8 clo r x0 x1 x2 x3 x4 x5 x6 x7
| rclo8_clo'
    r' x0 x1 x2 x3 x4 x5 x6 x7
    (R': r' <8= rclo8 clo r)
    (CLOR': clo r' x0 x1 x2 x3 x4 x5 x6 x7):
    @rclo8 clo r x0 x1 x2 x3 x4 x5 x6 x7
| rclo8_dcpn'
    r' x0 x1 x2 x3 x4 x5 x6 x7
    (R': r' <8= rclo8 clo r)
    (CLOR': @dcpn8 r' x0 x1 x2 x3 x4 x5 x6 x7):
    @rclo8 clo r x0 x1 x2 x3 x4 x5 x6 x7
.

Structure wdcompatible8 (clo: rel -> rel) : Prop :=
  wdcompat8_intro {
      wdcompat8_mon: monotone8 clo;
      wdcompat8_wcompat: forall r,
          clo (gf r) <8= gf (rclo8 clo r);
      wdcompat8_distr : forall r1 r2,
          clo (r1 \8/ r2) <8= (clo r1 \8/ clo r2);
    }.

Lemma rclo8_mon_gen clo clo' r r' x0 x1 x2 x3 x4 x5 x6 x7
      (IN: @rclo8 clo r x0 x1 x2 x3 x4 x5 x6 x7)
      (LEclo: clo <9= clo')
      (LEr: r <8= r') :
  @rclo8 clo' r' x0 x1 x2 x3 x4 x5 x6 x7.
Proof.
  induction IN; intros.
  - econstructor 1. apply LEr, R.
  - econstructor 2; [intros; eapply H, PR|apply LEclo, CLOR'].
  - econstructor 3; [intros; eapply H, PR|].
    eapply dcpn8_mon; [apply CLOR'|].
    intros. apply PR.
Qed.

Lemma rclo8_mon clo:
  monotone8 (rclo8 clo).
Proof.
  repeat intro. eapply rclo8_mon_gen; [apply IN|intros; apply PR|apply LE].
Qed.

Lemma rclo8_clo clo r:
  clo (rclo8 clo r) <8= rclo8 clo r.
Proof.
  intros. econstructor 2; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo8_dcpn clo r:
  dcpn8 (rclo8 clo r) <8= rclo8 clo r.
Proof.
  intros. econstructor 3; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo8_mult clo r:
  rclo8 clo (rclo8 clo r) <8= rclo8 clo r.
Proof.
  intros. induction PR.
  - apply R.
  - econstructor 2; [eapply H | eapply CLOR'].
  - econstructor 3; [eapply H | eapply CLOR'].
Qed.

Lemma rclo8_compose clo r:
  rclo8 (rclo8 clo) r <8= rclo8 clo r.
Proof.
  intros. induction PR.
  - apply rclo8_base, R.
  - apply rclo8_mult.
    eapply rclo8_mon; [apply CLOR'|apply H].
  - apply rclo8_dcpn.
    eapply dcpn8_mon; [apply CLOR'|apply H].
Qed.

Lemma wdcompat8_dcompat
      clo (WCOM: wdcompatible8 clo):
  dcompatible8 (rclo8 clo).
Proof.
  econstructor; [eapply rclo8_mon| |]; intros.
  - induction PR; intros.
    + eapply gf_mon; [apply R|]. intros.
      apply rclo8_base. apply PR.
    + eapply gf_mon.
      * eapply (wdcompat8_wcompat WCOM).
        eapply (wdcompat8_mon WCOM); [apply CLOR'|apply H].
      * intros. apply rclo8_mult, PR.
    + eapply gf_mon; [|intros; apply rclo8_dcpn, PR].
      eapply (dcompat8_compat dcpn8_compat).
      eapply dcpn8_mon; [apply CLOR'|apply H].
  - induction PR; intros.
    + destruct R as [R|R]; [left | right]; econstructor; apply R.
    + assert (CLOR:= wdcompat8_mon WCOM _ _ _ CLOR' H).
      eapply (wdcompat8_distr WCOM) in CLOR.
      destruct CLOR as [CLOR|CLOR]; [left|right]; apply rclo8_clo, CLOR.
    + assert (CLOR:= dcpn8_mon _ CLOR' H).
      eapply (dcompat8_distr dcpn8_compat) in CLOR.
      destruct CLOR as [CLOR|CLOR]; [left|right]; apply rclo8_dcpn, CLOR.
Qed.

Lemma wcompat8_sound clo (WCOM: wdcompatible8 clo):
  clo <9= dcpn8.
Proof.
  intros. exists (rclo8 clo).
  - apply wdcompat8_dcompat, WCOM.
  - apply rclo8_clo.
    eapply (wdcompat8_mon WCOM); [apply PR|].
    intros. apply rclo8_base, PR0.
Qed.

End PacoCompanion8_main.

Lemma pcpn8_mon_bot (gf gf': rel -> rel) x0 x1 x2 x3 x4 x5 x6 x7 r
      (IN: @pcpn8 gf bot8 x0 x1 x2 x3 x4 x5 x6 x7)
      (MON: monotone8 gf)
      (LE: gf <9= gf'):
  @pcpn8 gf' r x0 x1 x2 x3 x4 x5 x6 x7.
Proof.
  eapply paco8_mon_bot, LE.
  apply ucpn8_init. apply MON. left. apply IN.
Qed.

Lemma ucpn8_mon_bot (gf gf': rel -> rel) x0 x1 x2 x3 x4 x5 x6 x7 r
      (IN: @ucpn8 gf bot8 x0 x1 x2 x3 x4 x5 x6 x7)
      (MON: monotone8 gf)
      (LE: gf <9= gf'):
  @ucpn8 gf' r x0 x1 x2 x3 x4 x5 x6 x7.
Proof.
  eapply upaco8_mon_bot, LE.
  left. apply ucpn8_init. apply MON. apply IN.
Qed.

End PacoCompanion8.

Hint Resolve ucpn8_base : paco.
Hint Resolve pcpn8_step : paco.
Hint Resolve ucpn8_step : paco.

Hint Constructors rclo8 : rclo.
Hint Resolve rclo8_clo rclo8_dcpn : rclo.
