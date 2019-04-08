Require Export Program.Basics. Open Scope program_scope.
Require Import paco4 pacotac.
Set Implicit Arguments.

Section PacoCompanion4.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.

Local Notation rel := (rel4 T0 T1 T2 T3).

Section PacoCompanion4_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone4 gf.

(** 
  Distributive Compatibility, Distributive Companion, (U)Paco Companion 
*)

Structure dcompatible4 (clo: rel -> rel) : Prop :=
  dcompat4_intro {
      dcompat4_mon: monotone4 clo;
      dcompat4_compat : forall r,
          clo (gf r) <4= gf (clo r);
      dcompat4_distr : forall r1 r2,
          clo (r1 \4/ r2) <4= (clo r1 \4/ clo r2);
    }.

Inductive dcpn4 (r: rel) x0 x1 x2 x3 : Prop :=
| dcpn4_intro
    clo
    (COM: dcompatible4 clo)
    (CLO: clo r x0 x1 x2 x3)
.

Definition pcpn4 r := paco4 gf (dcpn4 r).
Definition ucpn4 r := upaco4 gf (dcpn4 r).

Lemma dcpn4_mon: monotone4 dcpn4.
Proof.
  red; intros.
  destruct IN. exists clo.
  - apply COM.
  - eapply dcompat4_mon.
    + apply COM.
    + apply CLO.
    + apply LE.
Qed.

Lemma pcpn4_mon: monotone4 pcpn4.
Proof.
  red; intros. eapply paco4_mon. apply IN.
  intros. eapply dcpn4_mon. apply PR. apply LE.
Qed.

Lemma ucpn4_mon: monotone4 ucpn4.
Proof.
  red; intros. eapply upaco4_mon. apply IN.
  intros. eapply dcpn4_mon. apply PR. apply LE.
Qed.

Lemma dcpn4_greatest: forall clo (COM: dcompatible4 clo), clo <5= dcpn4.
Proof. intros. econstructor;[apply COM|apply PR]. Qed.

Lemma dcpn4_compat: dcompatible4 dcpn4.
Proof.
  econstructor; [apply dcpn4_mon| |]; intros.
  - destruct PR; eapply gf_mon with (r:=clo r).
    + eapply (dcompat4_compat COM); apply CLO.
    + intros. econstructor; [apply COM|apply PR].
  - destruct PR.
    eapply (dcompat4_distr COM) in CLO.
    destruct CLO.
    + left. eapply dcpn4_greatest. apply COM. apply H.
    + right. eapply dcpn4_greatest. apply COM. apply H.
Qed.

Lemma dcpn4_base: forall r, r <4= dcpn4 r.
Proof.
  exists id; [|apply PR].
  econstructor; repeat intro.
  + apply LE, IN.
  + apply PR0.
  + destruct PR0.
    * left. apply H.
    * right. apply H.
Qed.

Lemma ucpn4_base: forall r, r <4= ucpn4 r.
Proof.
  right. apply dcpn4_base. apply PR.
Qed.

Lemma ucpn4_from_dcpn4_upaco r:
  dcpn4 (upaco4 gf r) <4= ucpn4 r.
Proof.
  intros.
  eapply (dcompat4_distr dcpn4_compat) in PR.
  destruct PR as [IN|IN]; cycle 1.
  - right. apply IN.
  - left. revert x0 x1 x2 x3 IN.
    pcofix CIH. intros.
    pstep. eapply gf_mon.
    + apply (dcompat4_compat dcpn4_compat).
      eapply dcpn4_mon. apply IN.
      intros. _punfold PR. apply PR. apply gf_mon.
    + intros. apply (dcompat4_distr dcpn4_compat) in PR.
      right. destruct PR.
      * apply CIH. apply H.
      * apply CIH0. apply H.
Qed.

Lemma dcpn4_dcpn: forall r,
    dcpn4 (dcpn4 r) <4= dcpn4 r.
Proof.
  intros. exists (compose dcpn4 dcpn4); [|apply PR].
  econstructor.
  - repeat intro. eapply dcpn4_mon; [apply IN|].
    intros. eapply dcpn4_mon; [apply PR0|apply LE].
  - intros. eapply (dcompat4_compat dcpn4_compat).
    eapply dcpn4_mon; [apply PR0|].
    intros. eapply (dcompat4_compat dcpn4_compat), PR1.
  - intros. eapply (dcompat4_distr dcpn4_compat).
    eapply dcpn4_mon, (dcompat4_distr dcpn4_compat).
    apply PR0.
Qed.

Lemma ucpn4_ucpn: forall r,
    ucpn4 (ucpn4 r) <4= ucpn4 r.
Proof.
  intros. destruct PR.
  - left. eapply paco4_mult_strong.
    eapply paco4_mon. apply H.
    intros. apply ucpn4_from_dcpn4_upaco in PR.
    eapply upaco4_mon. apply PR.
    intros. apply dcpn4_dcpn. apply PR0.
  - red. apply ucpn4_from_dcpn4_upaco in H.
    eapply upaco4_mon. apply H.
    intros. apply dcpn4_dcpn. apply PR.
Qed.

Lemma ucpn4_compat r: ucpn4 (gf r) <4= gf (ucpn4 r).
Proof.
  intros. destruct PR; cycle 1.
  - apply dcpn4_compat in H.
    eapply gf_mon. apply H.
    intros. right. apply PR.
  - _punfold H; [|apply gf_mon]. eapply gf_mon. apply H.
    intros. apply ucpn4_ucpn.
    eapply upaco4_mon. apply PR.
    intros. eapply dcpn4_mon. apply PR0.
    intros. left. pstep. eapply gf_mon. apply PR1.
    intros. apply ucpn4_base. apply PR2.
Qed.

Lemma ucpn4_init:
  ucpn4 bot4 <4= paco4 gf bot4.
Proof.
  pcofix CIH. intros.
  destruct PR; cycle 1.
  - eapply paco4_mon_bot; [| intros; apply PR].
    eapply paco4_algebra, H. apply gf_mon. intros.
    eapply (dcompat4_compat dcpn4_compat).
    eapply dcpn4_mon. apply PR. contradiction.
  - _punfold H; [|apply gf_mon]. pstep.
    eapply gf_mon. apply H. intros.
    right. apply CIH. apply PR.
Qed.

Lemma pcpn4_final r:
  paco4 gf r <4= pcpn4 r.
Proof.
  intros. eapply paco4_mon. apply PR.
  intros. apply dcpn4_base. apply PR0.
Qed.

Lemma ucpn4_final r:
  upaco4 gf r <4= ucpn4 r.
Proof.
  intros. eapply upaco4_mon. apply PR.
  intros. apply dcpn4_base. apply PR0.
Qed.

Lemma ucpn4_clo
      r clo (LE: clo <5= ucpn4):
  clo (ucpn4 r) <4= ucpn4 r.
Proof.
  intros. apply ucpn4_ucpn, LE, PR.
Qed.

Lemma pcpn4_clo
      r clo (LE: clo <5= ucpn4):
  clo (pcpn4 r) <4= pcpn4 r.
Proof.
  intros. pstep. eapply gf_mon, ucpn4_ucpn.
  apply ucpn4_compat. apply LE in PR.
  eapply ucpn4_mon. apply PR.
  intros. _punfold PR0. apply PR0. apply gf_mon.
Qed.

Lemma pcpn4_unfold r:
  pcpn4 r <4= gf (ucpn4 r).
Proof.
  intros. _punfold PR. apply PR. apply gf_mon.
Qed.

Lemma ucpn4_unfold:
  ucpn4 bot4 <4= gf(ucpn4 bot4).
Proof.
  intros. apply pcpn4_unfold, pcpn4_final, ucpn4_init, PR.
Qed.

Lemma pcpn4_step r:
  gf (ucpn4 r) <4= pcpn4 r.
Proof.
  intros. pstep. apply PR.
Qed.

Lemma ucpn4_step r:
  gf (ucpn4 r) <4= ucpn4 r.
Proof.
  left. apply pcpn4_step. apply PR.
Qed.

Lemma ucpn4_id r : ucpn4 r <4= ucpn4 r.
Proof. intros. apply PR. Qed.

Lemma pcpn4_id r : pcpn4 r <4= pcpn4 r.
Proof. intros. apply PR. Qed.

Lemma gf_dcpn4_mon: monotone4 (compose gf dcpn4).
Proof.
  repeat intro. eapply gf_mon. apply IN.
  intros. eapply dcpn4_mon. apply PR. apply LE.  
Qed.

Lemma pcpn4_from_paco r: paco4 (compose gf dcpn4) r <4= pcpn4 r.
Proof.
  intros. apply dcpn4_base in PR. revert x0 x1 x2 x3 PR.
  pcofix CIH. intros.
  pstep.
  eapply gf_mon; cycle 1.
  { instantiate (1:= _ \4/ _). right.
    destruct PR0; [apply CIH, H | apply CIH0, H]. }
  eapply gf_mon, (dcompat4_distr dcpn4_compat).
  eapply gf_mon, dcpn4_dcpn.
  eapply (dcompat4_compat dcpn4_compat).
  eapply dcpn4_mon. apply PR.
  intros. _punfold PR0. apply PR0. apply gf_dcpn4_mon.
Qed.

Lemma pcpn4_to_paco r: pcpn4 r <4= paco4 (compose gf dcpn4) r.
Proof.
  pcofix CIH. intros.
  pstep. _punfold PR; [|apply gf_mon].
  eapply gf_mon. apply PR. intros.
  destruct PR0; cycle 1.
  - eapply dcpn4_mon. apply H. intros.
    right. apply CIH0, PR0. 
  - apply dcpn4_base. right. apply CIH, H.
Qed.

Lemma pcpn4_cofix
    r l (OBG: forall rr (INC: r <4= rr) (CIH: l <4= rr), l <4= pcpn4 rr):
  l <4= pcpn4 r.
Proof.
  under_forall ltac:(apply pcpn4_from_paco).
  pcofix CIH. intros. apply pcpn4_to_paco.
  apply OBG. apply CIH0. apply CIH. apply PR.
Qed.

(**
  Recursive Closure & Weak Compatibility
*)

Inductive rclo4 (clo: rel->rel) (r: rel): rel :=
| rclo4_base
    x0 x1 x2 x3
    (R: r x0 x1 x2 x3):
    @rclo4 clo r x0 x1 x2 x3
| rclo4_clo'
    r' x0 x1 x2 x3
    (R': r' <4= rclo4 clo r)
    (CLOR': clo r' x0 x1 x2 x3):
    @rclo4 clo r x0 x1 x2 x3
| rclo4_dcpn'
    r' x0 x1 x2 x3
    (R': r' <4= rclo4 clo r)
    (CLOR': @dcpn4 r' x0 x1 x2 x3):
    @rclo4 clo r x0 x1 x2 x3
.

Structure wdcompatible4 (clo: rel -> rel) : Prop :=
  wdcompat4_intro {
      wdcompat4_mon: monotone4 clo;
      wdcompat4_wcompat: forall r,
          clo (gf r) <4= gf (rclo4 clo r);
      wdcompat4_distr : forall r1 r2,
          clo (r1 \4/ r2) <4= (clo r1 \4/ clo r2);
    }.

Lemma rclo4_mon_gen clo clo' r r' x0 x1 x2 x3
      (IN: @rclo4 clo r x0 x1 x2 x3)
      (LEclo: clo <5= clo')
      (LEr: r <4= r') :
  @rclo4 clo' r' x0 x1 x2 x3.
Proof.
  induction IN; intros.
  - econstructor 1. apply LEr, R.
  - econstructor 2; [intros; eapply H, PR|apply LEclo, CLOR'].
  - econstructor 3; [intros; eapply H, PR|].
    eapply dcpn4_mon; [apply CLOR'|].
    intros. apply PR.
Qed.

Lemma rclo4_mon clo:
  monotone4 (rclo4 clo).
Proof.
  repeat intro. eapply rclo4_mon_gen; [apply IN|intros; apply PR|apply LE].
Qed.

Lemma rclo4_clo clo r:
  clo (rclo4 clo r) <4= rclo4 clo r.
Proof.
  intros. econstructor 2; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo4_dcpn clo r:
  dcpn4 (rclo4 clo r) <4= rclo4 clo r.
Proof.
  intros. econstructor 3; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo4_mult clo r:
  rclo4 clo (rclo4 clo r) <4= rclo4 clo r.
Proof.
  intros. induction PR.
  - apply R.
  - econstructor 2; [eapply H | eapply CLOR'].
  - econstructor 3; [eapply H | eapply CLOR'].
Qed.

Lemma rclo4_compose clo r:
  rclo4 (rclo4 clo) r <4= rclo4 clo r.
Proof.
  intros. induction PR.
  - apply rclo4_base, R.
  - apply rclo4_mult.
    eapply rclo4_mon; [apply CLOR'|apply H].
  - apply rclo4_dcpn.
    eapply dcpn4_mon; [apply CLOR'|apply H].
Qed.

Lemma wdcompat4_dcompat
      clo (WCOM: wdcompatible4 clo):
  dcompatible4 (rclo4 clo).
Proof.
  econstructor; [eapply rclo4_mon| |]; intros.
  - induction PR; intros.
    + eapply gf_mon; [apply R|]. intros.
      apply rclo4_base. apply PR.
    + eapply gf_mon.
      * eapply (wdcompat4_wcompat WCOM).
        eapply (wdcompat4_mon WCOM); [apply CLOR'|apply H].
      * intros. apply rclo4_mult, PR.
    + eapply gf_mon; [|intros; apply rclo4_dcpn, PR].
      eapply (dcompat4_compat dcpn4_compat).
      eapply dcpn4_mon; [apply CLOR'|apply H].
  - induction PR; intros.
    + destruct R as [R|R]; [left | right]; econstructor; apply R.
    + assert (CLOR:= wdcompat4_mon WCOM _ _ _ CLOR' H).
      eapply (wdcompat4_distr WCOM) in CLOR.
      destruct CLOR as [CLOR|CLOR]; [left|right]; apply rclo4_clo, CLOR.
    + assert (CLOR:= dcpn4_mon _ CLOR' H).
      eapply (dcompat4_distr dcpn4_compat) in CLOR.
      destruct CLOR as [CLOR|CLOR]; [left|right]; apply rclo4_dcpn, CLOR.
Qed.

Lemma wcompat4_sound clo (WCOM: wdcompatible4 clo):
  clo <5= dcpn4.
Proof.
  intros. exists (rclo4 clo).
  - apply wdcompat4_dcompat, WCOM.
  - apply rclo4_clo.
    eapply (wdcompat4_mon WCOM); [apply PR|].
    intros. apply rclo4_base, PR0.
Qed.

End PacoCompanion4_main.

Lemma pcpn4_mon_bot (gf gf': rel -> rel) x0 x1 x2 x3 r
      (IN: @pcpn4 gf bot4 x0 x1 x2 x3)
      (MON: monotone4 gf)
      (LE: gf <5= gf'):
  @pcpn4 gf' r x0 x1 x2 x3.
Proof.
  eapply paco4_mon_bot, LE.
  apply ucpn4_init. apply MON. left. apply IN.
Qed.

Lemma ucpn4_mon_bot (gf gf': rel -> rel) x0 x1 x2 x3 r
      (IN: @ucpn4 gf bot4 x0 x1 x2 x3)
      (MON: monotone4 gf)
      (LE: gf <5= gf'):
  @ucpn4 gf' r x0 x1 x2 x3.
Proof.
  eapply upaco4_mon_bot, LE.
  left. apply ucpn4_init. apply MON. apply IN.
Qed.

End PacoCompanion4.

Hint Resolve ucpn4_base : paco.
Hint Resolve pcpn4_step : paco.
Hint Resolve ucpn4_step : paco.

Hint Constructors rclo4 : rclo.
Hint Resolve rclo4_clo rclo4_dcpn : rclo.
