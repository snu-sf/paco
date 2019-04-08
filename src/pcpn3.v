Require Export Program.Basics. Open Scope program_scope.
Require Import paco3 pacotac.
Set Implicit Arguments.

Section PacoCompanion3.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.

Local Notation rel := (rel3 T0 T1 T2).

Section PacoCompanion3_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone3 gf.

(** 
  Distributive Compatibility, Distributive Companion, (U)Paco Companion 
*)

Structure dcompatible3 (clo: rel -> rel) : Prop :=
  dcompat3_intro {
      dcompat3_mon: monotone3 clo;
      dcompat3_compat : forall r,
          clo (gf r) <3= gf (clo r);
      dcompat3_distr : forall r1 r2,
          clo (r1 \3/ r2) <3= (clo r1 \3/ clo r2);
    }.

Inductive dcpn3 (r: rel) x0 x1 x2 : Prop :=
| dcpn3_intro
    clo
    (COM: dcompatible3 clo)
    (CLO: clo r x0 x1 x2)
.

Definition pcpn3 r := paco3 gf (dcpn3 r).
Definition ucpn3 r := upaco3 gf (dcpn3 r).

Lemma dcpn3_mon: monotone3 dcpn3.
Proof.
  red; intros.
  destruct IN. exists clo.
  - apply COM.
  - eapply dcompat3_mon.
    + apply COM.
    + apply CLO.
    + apply LE.
Qed.

Lemma pcpn3_mon: monotone3 pcpn3.
Proof.
  red; intros. eapply paco3_mon. apply IN.
  intros. eapply dcpn3_mon. apply PR. apply LE.
Qed.

Lemma ucpn3_mon: monotone3 ucpn3.
Proof.
  red; intros. eapply upaco3_mon. apply IN.
  intros. eapply dcpn3_mon. apply PR. apply LE.
Qed.

Lemma dcpn3_greatest: forall clo (COM: dcompatible3 clo), clo <4= dcpn3.
Proof. intros. econstructor;[apply COM|apply PR]. Qed.

Lemma dcpn3_compat: dcompatible3 dcpn3.
Proof.
  econstructor; [apply dcpn3_mon| |]; intros.
  - destruct PR; eapply gf_mon with (r:=clo r).
    + eapply (dcompat3_compat COM); apply CLO.
    + intros. econstructor; [apply COM|apply PR].
  - destruct PR.
    eapply (dcompat3_distr COM) in CLO.
    destruct CLO.
    + left. eapply dcpn3_greatest. apply COM. apply H.
    + right. eapply dcpn3_greatest. apply COM. apply H.
Qed.

Lemma dcpn3_base: forall r, r <3= dcpn3 r.
Proof.
  exists id; [|apply PR].
  econstructor; repeat intro.
  + apply LE, IN.
  + apply PR0.
  + destruct PR0.
    * left. apply H.
    * right. apply H.
Qed.

Lemma ucpn3_base: forall r, r <3= ucpn3 r.
Proof.
  right. apply dcpn3_base. apply PR.
Qed.

Lemma ucpn3_from_dcpn3_upaco r:
  dcpn3 (upaco3 gf r) <3= ucpn3 r.
Proof.
  intros.
  eapply (dcompat3_distr dcpn3_compat) in PR.
  destruct PR as [IN|IN]; cycle 1.
  - right. apply IN.
  - left. revert x0 x1 x2 IN.
    pcofix CIH. intros.
    pstep. eapply gf_mon.
    + apply (dcompat3_compat dcpn3_compat).
      eapply dcpn3_mon. apply IN.
      intros. _punfold PR. apply PR. apply gf_mon.
    + intros. apply (dcompat3_distr dcpn3_compat) in PR.
      right. destruct PR.
      * apply CIH. apply H.
      * apply CIH0. apply H.
Qed.

Lemma dcpn3_dcpn: forall r,
    dcpn3 (dcpn3 r) <3= dcpn3 r.
Proof.
  intros. exists (compose dcpn3 dcpn3); [|apply PR].
  econstructor.
  - repeat intro. eapply dcpn3_mon; [apply IN|].
    intros. eapply dcpn3_mon; [apply PR0|apply LE].
  - intros. eapply (dcompat3_compat dcpn3_compat).
    eapply dcpn3_mon; [apply PR0|].
    intros. eapply (dcompat3_compat dcpn3_compat), PR1.
  - intros. eapply (dcompat3_distr dcpn3_compat).
    eapply dcpn3_mon, (dcompat3_distr dcpn3_compat).
    apply PR0.
Qed.

Lemma ucpn3_ucpn: forall r,
    ucpn3 (ucpn3 r) <3= ucpn3 r.
Proof.
  intros. destruct PR.
  - left. eapply paco3_mult_strong.
    eapply paco3_mon. apply H.
    intros. apply ucpn3_from_dcpn3_upaco in PR.
    eapply upaco3_mon. apply PR.
    intros. apply dcpn3_dcpn. apply PR0.
  - red. apply ucpn3_from_dcpn3_upaco in H.
    eapply upaco3_mon. apply H.
    intros. apply dcpn3_dcpn. apply PR.
Qed.

Lemma ucpn3_compat r: ucpn3 (gf r) <3= gf (ucpn3 r).
Proof.
  intros. destruct PR; cycle 1.
  - apply dcpn3_compat in H.
    eapply gf_mon. apply H.
    intros. right. apply PR.
  - _punfold H; [|apply gf_mon]. eapply gf_mon. apply H.
    intros. apply ucpn3_ucpn.
    eapply upaco3_mon. apply PR.
    intros. eapply dcpn3_mon. apply PR0.
    intros. left. pstep. eapply gf_mon. apply PR1.
    intros. apply ucpn3_base. apply PR2.
Qed.

Lemma ucpn3_init:
  ucpn3 bot3 <3= paco3 gf bot3.
Proof.
  pcofix CIH. intros.
  destruct PR; cycle 1.
  - eapply paco3_mon_bot; [| intros; apply PR].
    eapply paco3_algebra, H. apply gf_mon. intros.
    eapply (dcompat3_compat dcpn3_compat).
    eapply dcpn3_mon. apply PR. contradiction.
  - _punfold H; [|apply gf_mon]. pstep.
    eapply gf_mon. apply H. intros.
    right. apply CIH. apply PR.
Qed.

Lemma pcpn3_final r:
  paco3 gf r <3= pcpn3 r.
Proof.
  intros. eapply paco3_mon. apply PR.
  intros. apply dcpn3_base. apply PR0.
Qed.

Lemma ucpn3_final r:
  upaco3 gf r <3= ucpn3 r.
Proof.
  intros. eapply upaco3_mon. apply PR.
  intros. apply dcpn3_base. apply PR0.
Qed.

Lemma ucpn3_clo
      r clo (LE: clo <4= ucpn3):
  clo (ucpn3 r) <3= ucpn3 r.
Proof.
  intros. apply ucpn3_ucpn, LE, PR.
Qed.

Lemma pcpn3_clo
      r clo (LE: clo <4= ucpn3):
  clo (pcpn3 r) <3= pcpn3 r.
Proof.
  intros. pstep. eapply gf_mon, ucpn3_ucpn.
  apply ucpn3_compat. apply LE in PR.
  eapply ucpn3_mon. apply PR.
  intros. _punfold PR0. apply PR0. apply gf_mon.
Qed.

Lemma pcpn3_unfold r:
  pcpn3 r <3= gf (ucpn3 r).
Proof.
  intros. _punfold PR. apply PR. apply gf_mon.
Qed.

Lemma ucpn3_unfold:
  ucpn3 bot3 <3= gf(ucpn3 bot3).
Proof.
  intros. apply pcpn3_unfold, pcpn3_final, ucpn3_init, PR.
Qed.

Lemma pcpn3_step r:
  gf (ucpn3 r) <3= pcpn3 r.
Proof.
  intros. pstep. apply PR.
Qed.

Lemma ucpn3_step r:
  gf (ucpn3 r) <3= ucpn3 r.
Proof.
  left. apply pcpn3_step. apply PR.
Qed.

Lemma ucpn3_id r : ucpn3 r <3= ucpn3 r.
Proof. intros. apply PR. Qed.

Lemma pcpn3_id r : pcpn3 r <3= pcpn3 r.
Proof. intros. apply PR. Qed.

Lemma gf_dcpn3_mon: monotone3 (compose gf dcpn3).
Proof.
  repeat intro. eapply gf_mon. apply IN.
  intros. eapply dcpn3_mon. apply PR. apply LE.  
Qed.

Lemma pcpn3_from_paco r: paco3 (compose gf dcpn3) r <3= pcpn3 r.
Proof.
  intros. apply dcpn3_base in PR. revert x0 x1 x2 PR.
  pcofix CIH. intros.
  pstep.
  eapply gf_mon; cycle 1.
  { instantiate (1:= _ \3/ _). right.
    destruct PR0; [apply CIH, H | apply CIH0, H]. }
  eapply gf_mon, (dcompat3_distr dcpn3_compat).
  eapply gf_mon, dcpn3_dcpn.
  eapply (dcompat3_compat dcpn3_compat).
  eapply dcpn3_mon. apply PR.
  intros. _punfold PR0. apply PR0. apply gf_dcpn3_mon.
Qed.

Lemma pcpn3_to_paco r: pcpn3 r <3= paco3 (compose gf dcpn3) r.
Proof.
  pcofix CIH. intros.
  pstep. _punfold PR; [|apply gf_mon].
  eapply gf_mon. apply PR. intros.
  destruct PR0; cycle 1.
  - eapply dcpn3_mon. apply H. intros.
    right. apply CIH0, PR0. 
  - apply dcpn3_base. right. apply CIH, H.
Qed.

Lemma pcpn3_cofix
    r l (OBG: forall rr (INC: r <3= rr) (CIH: l <3= rr), l <3= pcpn3 rr):
  l <3= pcpn3 r.
Proof.
  under_forall ltac:(apply pcpn3_from_paco).
  pcofix CIH. intros. apply pcpn3_to_paco.
  apply OBG. apply CIH0. apply CIH. apply PR.
Qed.

(**
  Recursive Closure & Weak Compatibility
*)

Inductive rclo3 (clo: rel->rel) (r: rel): rel :=
| rclo3_base
    x0 x1 x2
    (R: r x0 x1 x2):
    @rclo3 clo r x0 x1 x2
| rclo3_clo'
    r' x0 x1 x2
    (R': r' <3= rclo3 clo r)
    (CLOR': clo r' x0 x1 x2):
    @rclo3 clo r x0 x1 x2
| rclo3_dcpn'
    r' x0 x1 x2
    (R': r' <3= rclo3 clo r)
    (CLOR': @dcpn3 r' x0 x1 x2):
    @rclo3 clo r x0 x1 x2
.

Structure wdcompatible3 (clo: rel -> rel) : Prop :=
  wdcompat3_intro {
      wdcompat3_mon: monotone3 clo;
      wdcompat3_wcompat: forall r,
          clo (gf r) <3= gf (rclo3 clo r);
      wdcompat3_distr : forall r1 r2,
          clo (r1 \3/ r2) <3= (clo r1 \3/ clo r2);
    }.

Lemma rclo3_mon_gen clo clo' r r' x0 x1 x2
      (IN: @rclo3 clo r x0 x1 x2)
      (LEclo: clo <4= clo')
      (LEr: r <3= r') :
  @rclo3 clo' r' x0 x1 x2.
Proof.
  induction IN; intros.
  - econstructor 1. apply LEr, R.
  - econstructor 2; [intros; eapply H, PR|apply LEclo, CLOR'].
  - econstructor 3; [intros; eapply H, PR|].
    eapply dcpn3_mon; [apply CLOR'|].
    intros. apply PR.
Qed.

Lemma rclo3_mon clo:
  monotone3 (rclo3 clo).
Proof.
  repeat intro. eapply rclo3_mon_gen; [apply IN|intros; apply PR|apply LE].
Qed.

Lemma rclo3_clo clo r:
  clo (rclo3 clo r) <3= rclo3 clo r.
Proof.
  intros. econstructor 2; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo3_dcpn clo r:
  dcpn3 (rclo3 clo r) <3= rclo3 clo r.
Proof.
  intros. econstructor 3; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo3_mult clo r:
  rclo3 clo (rclo3 clo r) <3= rclo3 clo r.
Proof.
  intros. induction PR.
  - apply R.
  - econstructor 2; [eapply H | eapply CLOR'].
  - econstructor 3; [eapply H | eapply CLOR'].
Qed.

Lemma rclo3_compose clo r:
  rclo3 (rclo3 clo) r <3= rclo3 clo r.
Proof.
  intros. induction PR.
  - apply rclo3_base, R.
  - apply rclo3_mult.
    eapply rclo3_mon; [apply CLOR'|apply H].
  - apply rclo3_dcpn.
    eapply dcpn3_mon; [apply CLOR'|apply H].
Qed.

Lemma wdcompat3_dcompat
      clo (WCOM: wdcompatible3 clo):
  dcompatible3 (rclo3 clo).
Proof.
  econstructor; [eapply rclo3_mon| |]; intros.
  - induction PR; intros.
    + eapply gf_mon; [apply R|]. intros.
      apply rclo3_base. apply PR.
    + eapply gf_mon.
      * eapply (wdcompat3_wcompat WCOM).
        eapply (wdcompat3_mon WCOM); [apply CLOR'|apply H].
      * intros. apply rclo3_mult, PR.
    + eapply gf_mon; [|intros; apply rclo3_dcpn, PR].
      eapply (dcompat3_compat dcpn3_compat).
      eapply dcpn3_mon; [apply CLOR'|apply H].
  - induction PR; intros.
    + destruct R as [R|R]; [left | right]; econstructor; apply R.
    + assert (CLOR:= wdcompat3_mon WCOM _ _ _ CLOR' H).
      eapply (wdcompat3_distr WCOM) in CLOR.
      destruct CLOR as [CLOR|CLOR]; [left|right]; apply rclo3_clo, CLOR.
    + assert (CLOR:= dcpn3_mon _ CLOR' H).
      eapply (dcompat3_distr dcpn3_compat) in CLOR.
      destruct CLOR as [CLOR|CLOR]; [left|right]; apply rclo3_dcpn, CLOR.
Qed.

Lemma wcompat3_sound clo (WCOM: wdcompatible3 clo):
  clo <4= dcpn3.
Proof.
  intros. exists (rclo3 clo).
  - apply wdcompat3_dcompat, WCOM.
  - apply rclo3_clo.
    eapply (wdcompat3_mon WCOM); [apply PR|].
    intros. apply rclo3_base, PR0.
Qed.

End PacoCompanion3_main.

Lemma pcpn3_mon_bot (gf gf': rel -> rel) x0 x1 x2 r
      (IN: @pcpn3 gf bot3 x0 x1 x2)
      (MON: monotone3 gf)
      (LE: gf <4= gf'):
  @pcpn3 gf' r x0 x1 x2.
Proof.
  eapply paco3_mon_bot, LE.
  apply ucpn3_init. apply MON. left. apply IN.
Qed.

Lemma ucpn3_mon_bot (gf gf': rel -> rel) x0 x1 x2 r
      (IN: @ucpn3 gf bot3 x0 x1 x2)
      (MON: monotone3 gf)
      (LE: gf <4= gf'):
  @ucpn3 gf' r x0 x1 x2.
Proof.
  eapply upaco3_mon_bot, LE.
  left. apply ucpn3_init. apply MON. apply IN.
Qed.

End PacoCompanion3.

Hint Resolve ucpn3_base : paco.
Hint Resolve pcpn3_step : paco.
Hint Resolve ucpn3_step : paco.

Hint Constructors rclo3 : rclo.
Hint Resolve rclo3_clo rclo3_dcpn : rclo.
