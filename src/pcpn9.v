Require Export Program.Basics. Open Scope program_scope.
Require Import paco9 pacotac.
Set Implicit Arguments.

Section PacoCompanion9.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
Variable T7 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5), Type.
Variable T8 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6), Type.

Local Notation rel := (rel9 T0 T1 T2 T3 T4 T5 T6 T7 T8).

Section PacoCompanion9_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone9 gf.

(** 
  Distributive Compatibility, Distributive Companion, (U)Paco Companion 
*)

Structure dcompatible9 (clo: rel -> rel) : Prop :=
  dcompat9_intro {
      dcompat9_mon: monotone9 clo;
      dcompat9_compat : forall r,
          clo (gf r) <9= gf (clo r);
      dcompat9_distr : forall r1 r2,
          clo (r1 \9/ r2) <9= (clo r1 \9/ clo r2);
    }.

Inductive dcpn9 (r: rel) x0 x1 x2 x3 x4 x5 x6 x7 x8 : Prop :=
| dcpn9_intro
    clo
    (COM: dcompatible9 clo)
    (CLO: clo r x0 x1 x2 x3 x4 x5 x6 x7 x8)
.

Definition pcpn9 r := paco9 gf (dcpn9 r).
Definition ucpn9 r := upaco9 gf (dcpn9 r).

Lemma dcpn9_mon: monotone9 dcpn9.
Proof.
  red; intros.
  destruct IN. exists clo.
  - apply COM.
  - eapply dcompat9_mon.
    + apply COM.
    + apply CLO.
    + apply LE.
Qed.

Lemma pcpn9_mon: monotone9 pcpn9.
Proof.
  red; intros. eapply paco9_mon. apply IN.
  intros. eapply dcpn9_mon. apply PR. apply LE.
Qed.

Lemma ucpn9_mon: monotone9 ucpn9.
Proof.
  red; intros. eapply upaco9_mon. apply IN.
  intros. eapply dcpn9_mon. apply PR. apply LE.
Qed.

Lemma dcpn9_greatest: forall clo (COM: dcompatible9 clo), clo <10= dcpn9.
Proof. intros. econstructor;[apply COM|apply PR]. Qed.

Lemma dcpn9_compat: dcompatible9 dcpn9.
Proof.
  econstructor; [apply dcpn9_mon| |]; intros.
  - destruct PR; eapply gf_mon with (r:=clo r).
    + eapply (dcompat9_compat COM); apply CLO.
    + intros. econstructor; [apply COM|apply PR].
  - destruct PR.
    eapply (dcompat9_distr COM) in CLO.
    destruct CLO.
    + left. eapply dcpn9_greatest. apply COM. apply H.
    + right. eapply dcpn9_greatest. apply COM. apply H.
Qed.

Lemma dcpn9_base: forall r, r <9= dcpn9 r.
Proof.
  exists id; [|apply PR].
  econstructor; repeat intro.
  + apply LE, IN.
  + apply PR0.
  + destruct PR0.
    * left. apply H.
    * right. apply H.
Qed.

Lemma ucpn9_base: forall r, r <9= ucpn9 r.
Proof.
  right. apply dcpn9_base. apply PR.
Qed.

Lemma ucpn9_from_dcpn9_upaco r:
  dcpn9 (upaco9 gf r) <9= ucpn9 r.
Proof.
  intros.
  eapply (dcompat9_distr dcpn9_compat) in PR.
  destruct PR as [IN|IN]; cycle 1.
  - right. apply IN.
  - left. revert x0 x1 x2 x3 x4 x5 x6 x7 x8 IN.
    pcofix CIH. intros.
    pstep. eapply gf_mon.
    + apply (dcompat9_compat dcpn9_compat).
      eapply dcpn9_mon. apply IN.
      intros. _punfold PR. apply PR. apply gf_mon.
    + intros. apply (dcompat9_distr dcpn9_compat) in PR.
      right. destruct PR.
      * apply CIH. apply H.
      * apply CIH0. apply H.
Qed.

Lemma dcpn9_dcpn: forall r,
    dcpn9 (dcpn9 r) <9= dcpn9 r.
Proof.
  intros. exists (compose dcpn9 dcpn9); [|apply PR].
  econstructor.
  - repeat intro. eapply dcpn9_mon; [apply IN|].
    intros. eapply dcpn9_mon; [apply PR0|apply LE].
  - intros. eapply (dcompat9_compat dcpn9_compat).
    eapply dcpn9_mon; [apply PR0|].
    intros. eapply (dcompat9_compat dcpn9_compat), PR1.
  - intros. eapply (dcompat9_distr dcpn9_compat).
    eapply dcpn9_mon, (dcompat9_distr dcpn9_compat).
    apply PR0.
Qed.

Lemma ucpn9_ucpn: forall r,
    ucpn9 (ucpn9 r) <9= ucpn9 r.
Proof.
  intros. destruct PR.
  - left. eapply paco9_mult_strong.
    eapply paco9_mon. apply H.
    intros. apply ucpn9_from_dcpn9_upaco in PR.
    eapply upaco9_mon. apply PR.
    intros. apply dcpn9_dcpn. apply PR0.
  - red. apply ucpn9_from_dcpn9_upaco in H.
    eapply upaco9_mon. apply H.
    intros. apply dcpn9_dcpn. apply PR.
Qed.

Lemma ucpn9_compat r: ucpn9 (gf r) <9= gf (ucpn9 r).
Proof.
  intros. destruct PR; cycle 1.
  - apply dcpn9_compat in H.
    eapply gf_mon. apply H.
    intros. right. apply PR.
  - _punfold H; [|apply gf_mon]. eapply gf_mon. apply H.
    intros. apply ucpn9_ucpn.
    eapply upaco9_mon. apply PR.
    intros. eapply dcpn9_mon. apply PR0.
    intros. left. pstep. eapply gf_mon. apply PR1.
    intros. apply ucpn9_base. apply PR2.
Qed.

Lemma ucpn9_init:
  ucpn9 bot9 <9= paco9 gf bot9.
Proof.
  pcofix CIH. intros.
  destruct PR; cycle 1.
  - eapply paco9_mon_bot; [| intros; apply PR].
    eapply paco9_algebra, H. apply gf_mon. intros.
    eapply (dcompat9_compat dcpn9_compat).
    eapply dcpn9_mon. apply PR. contradiction.
  - _punfold H; [|apply gf_mon]. pstep.
    eapply gf_mon. apply H. intros.
    right. apply CIH. apply PR.
Qed.

Lemma pcpn9_final r:
  paco9 gf r <9= pcpn9 r.
Proof.
  intros. eapply paco9_mon. apply PR.
  intros. apply dcpn9_base. apply PR0.
Qed.

Lemma ucpn9_final r:
  upaco9 gf r <9= ucpn9 r.
Proof.
  intros. eapply upaco9_mon. apply PR.
  intros. apply dcpn9_base. apply PR0.
Qed.

Lemma ucpn9_clo
      r clo (LE: clo <10= ucpn9):
  clo (ucpn9 r) <9= ucpn9 r.
Proof.
  intros. apply ucpn9_ucpn, LE, PR.
Qed.

Lemma pcpn9_clo
      r clo (LE: clo <10= ucpn9):
  clo (pcpn9 r) <9= pcpn9 r.
Proof.
  intros. pstep. eapply gf_mon, ucpn9_ucpn.
  apply ucpn9_compat. apply LE in PR.
  eapply ucpn9_mon. apply PR.
  intros. _punfold PR0. apply PR0. apply gf_mon.
Qed.

Lemma pcpn9_unfold r:
  pcpn9 r <9= gf (ucpn9 r).
Proof.
  intros. _punfold PR. apply PR. apply gf_mon.
Qed.

Lemma ucpn9_unfold:
  ucpn9 bot9 <9= gf(ucpn9 bot9).
Proof.
  intros. apply pcpn9_unfold, pcpn9_final, ucpn9_init, PR.
Qed.

Lemma pcpn9_step r:
  gf (ucpn9 r) <9= pcpn9 r.
Proof.
  intros. pstep. apply PR.
Qed.

Lemma ucpn9_step r:
  gf (ucpn9 r) <9= ucpn9 r.
Proof.
  left. apply pcpn9_step. apply PR.
Qed.

Lemma ucpn9_id r : ucpn9 r <9= ucpn9 r.
Proof. intros. apply PR. Qed.

Lemma pcpn9_id r : pcpn9 r <9= pcpn9 r.
Proof. intros. apply PR. Qed.

Lemma gf_dcpn9_mon: monotone9 (compose gf dcpn9).
Proof.
  repeat intro. eapply gf_mon. apply IN.
  intros. eapply dcpn9_mon. apply PR. apply LE.  
Qed.

Lemma pcpn9_from_paco r: paco9 (compose gf dcpn9) r <9= pcpn9 r.
Proof.
  intros. apply dcpn9_base in PR. revert x0 x1 x2 x3 x4 x5 x6 x7 x8 PR.
  pcofix CIH. intros.
  pstep.
  eapply gf_mon; cycle 1.
  { instantiate (1:= _ \9/ _). right.
    destruct PR0; [apply CIH, H | apply CIH0, H]. }
  eapply gf_mon, (dcompat9_distr dcpn9_compat).
  eapply gf_mon, dcpn9_dcpn.
  eapply (dcompat9_compat dcpn9_compat).
  eapply dcpn9_mon. apply PR.
  intros. _punfold PR0. apply PR0. apply gf_dcpn9_mon.
Qed.

Lemma pcpn9_to_paco r: pcpn9 r <9= paco9 (compose gf dcpn9) r.
Proof.
  pcofix CIH. intros.
  pstep. _punfold PR; [|apply gf_mon].
  eapply gf_mon. apply PR. intros.
  destruct PR0; cycle 1.
  - eapply dcpn9_mon. apply H. intros.
    right. apply CIH0, PR0. 
  - apply dcpn9_base. right. apply CIH, H.
Qed.

Lemma pcpn9_cofix
    r l (OBG: forall rr (INC: r <9= rr) (CIH: l <9= rr), l <9= pcpn9 rr):
  l <9= pcpn9 r.
Proof.
  under_forall ltac:(apply pcpn9_from_paco).
  pcofix CIH. intros. apply pcpn9_to_paco.
  apply OBG. apply CIH0. apply CIH. apply PR.
Qed.

(**
  Recursive Closure & Weak Compatibility
*)

Inductive rclo9 (clo: rel->rel) (r: rel): rel :=
| rclo9_base
    x0 x1 x2 x3 x4 x5 x6 x7 x8
    (R: r x0 x1 x2 x3 x4 x5 x6 x7 x8):
    @rclo9 clo r x0 x1 x2 x3 x4 x5 x6 x7 x8
| rclo9_clo'
    r' x0 x1 x2 x3 x4 x5 x6 x7 x8
    (R': r' <9= rclo9 clo r)
    (CLOR': clo r' x0 x1 x2 x3 x4 x5 x6 x7 x8):
    @rclo9 clo r x0 x1 x2 x3 x4 x5 x6 x7 x8
| rclo9_dcpn'
    r' x0 x1 x2 x3 x4 x5 x6 x7 x8
    (R': r' <9= rclo9 clo r)
    (CLOR': @dcpn9 r' x0 x1 x2 x3 x4 x5 x6 x7 x8):
    @rclo9 clo r x0 x1 x2 x3 x4 x5 x6 x7 x8
.

Structure wdcompatible9 (clo: rel -> rel) : Prop :=
  wdcompat9_intro {
      wdcompat9_mon: monotone9 clo;
      wdcompat9_wcompat: forall r,
          clo (gf r) <9= gf (rclo9 clo r);
      wdcompat9_distr : forall r1 r2,
          clo (r1 \9/ r2) <9= (clo r1 \9/ clo r2);
    }.

Lemma rclo9_mon_gen clo clo' r r' x0 x1 x2 x3 x4 x5 x6 x7 x8
      (IN: @rclo9 clo r x0 x1 x2 x3 x4 x5 x6 x7 x8)
      (LEclo: clo <10= clo')
      (LEr: r <9= r') :
  @rclo9 clo' r' x0 x1 x2 x3 x4 x5 x6 x7 x8.
Proof.
  induction IN; intros.
  - econstructor 1. apply LEr, R.
  - econstructor 2; [intros; eapply H, PR|apply LEclo, CLOR'].
  - econstructor 3; [intros; eapply H, PR|].
    eapply dcpn9_mon; [apply CLOR'|].
    intros. apply PR.
Qed.

Lemma rclo9_mon clo:
  monotone9 (rclo9 clo).
Proof.
  repeat intro. eapply rclo9_mon_gen; [apply IN|intros; apply PR|apply LE].
Qed.

Lemma rclo9_clo clo r:
  clo (rclo9 clo r) <9= rclo9 clo r.
Proof.
  intros. econstructor 2; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo9_dcpn clo r:
  dcpn9 (rclo9 clo r) <9= rclo9 clo r.
Proof.
  intros. econstructor 3; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo9_mult clo r:
  rclo9 clo (rclo9 clo r) <9= rclo9 clo r.
Proof.
  intros. induction PR.
  - apply R.
  - econstructor 2; [eapply H | eapply CLOR'].
  - econstructor 3; [eapply H | eapply CLOR'].
Qed.

Lemma rclo9_compose clo r:
  rclo9 (rclo9 clo) r <9= rclo9 clo r.
Proof.
  intros. induction PR.
  - apply rclo9_base, R.
  - apply rclo9_mult.
    eapply rclo9_mon; [apply CLOR'|apply H].
  - apply rclo9_dcpn.
    eapply dcpn9_mon; [apply CLOR'|apply H].
Qed.

Lemma wdcompat9_dcompat
      clo (WCOM: wdcompatible9 clo):
  dcompatible9 (rclo9 clo).
Proof.
  econstructor; [eapply rclo9_mon| |]; intros.
  - induction PR; intros.
    + eapply gf_mon; [apply R|]. intros.
      apply rclo9_base. apply PR.
    + eapply gf_mon.
      * eapply (wdcompat9_wcompat WCOM).
        eapply (wdcompat9_mon WCOM); [apply CLOR'|apply H].
      * intros. apply rclo9_mult, PR.
    + eapply gf_mon; [|intros; apply rclo9_dcpn, PR].
      eapply (dcompat9_compat dcpn9_compat).
      eapply dcpn9_mon; [apply CLOR'|apply H].
  - induction PR; intros.
    + destruct R as [R|R]; [left | right]; econstructor; apply R.
    + assert (CLOR:= wdcompat9_mon WCOM _ _ _ CLOR' H).
      eapply (wdcompat9_distr WCOM) in CLOR.
      destruct CLOR as [CLOR|CLOR]; [left|right]; apply rclo9_clo, CLOR.
    + assert (CLOR:= dcpn9_mon _ CLOR' H).
      eapply (dcompat9_distr dcpn9_compat) in CLOR.
      destruct CLOR as [CLOR|CLOR]; [left|right]; apply rclo9_dcpn, CLOR.
Qed.

Lemma wcompat9_sound clo (WCOM: wdcompatible9 clo):
  clo <10= dcpn9.
Proof.
  intros. exists (rclo9 clo).
  - apply wdcompat9_dcompat, WCOM.
  - apply rclo9_clo.
    eapply (wdcompat9_mon WCOM); [apply PR|].
    intros. apply rclo9_base, PR0.
Qed.

End PacoCompanion9_main.

Lemma pcpn9_mon_bot (gf gf': rel -> rel) x0 x1 x2 x3 x4 x5 x6 x7 x8 r
      (IN: @pcpn9 gf bot9 x0 x1 x2 x3 x4 x5 x6 x7 x8)
      (MON: monotone9 gf)
      (LE: gf <10= gf'):
  @pcpn9 gf' r x0 x1 x2 x3 x4 x5 x6 x7 x8.
Proof.
  eapply paco9_mon_bot, LE.
  apply ucpn9_init. apply MON. left. apply IN.
Qed.

Lemma ucpn9_mon_bot (gf gf': rel -> rel) x0 x1 x2 x3 x4 x5 x6 x7 x8 r
      (IN: @ucpn9 gf bot9 x0 x1 x2 x3 x4 x5 x6 x7 x8)
      (MON: monotone9 gf)
      (LE: gf <10= gf'):
  @ucpn9 gf' r x0 x1 x2 x3 x4 x5 x6 x7 x8.
Proof.
  eapply upaco9_mon_bot, LE.
  left. apply ucpn9_init. apply MON. apply IN.
Qed.

End PacoCompanion9.

Hint Resolve ucpn9_base : paco.
Hint Resolve pcpn9_step : paco.
Hint Resolve ucpn9_step : paco.

Hint Constructors rclo9 : rclo.
Hint Resolve rclo9_clo rclo9_dcpn : rclo.
