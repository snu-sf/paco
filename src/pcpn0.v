Require Export Program.Basics. Open Scope program_scope.
Require Import paco0 pacotac.
Set Implicit Arguments.

Section PacoCompanion0.


Local Notation rel := (rel0).

Section PacoCompanion0_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone0 gf.

(** 
  Distributive Compatibility, Distributive Companion, (U)Paco Companion 
*)

Structure dcompatible0 (clo: rel -> rel) : Prop :=
  dcompat0_intro {
      dcompat0_mon: monotone0 clo;
      dcompat0_compat : forall r,
          clo (gf r) <0= gf (clo r);
      dcompat0_distr : forall r1 r2,
          clo (r1 \0/ r2) <0= (clo r1 \0/ clo r2);
    }.

Inductive dcpn0 (r: rel) : Prop :=
| dcpn0_intro
    clo
    (COM: dcompatible0 clo)
    (CLO: clo r)
.

Definition pcpn0 r := paco0 gf (dcpn0 r).
Definition ucpn0 r := upaco0 gf (dcpn0 r).

Lemma dcpn0_mon: monotone0 dcpn0.
Proof.
  red; intros.
  destruct IN. exists clo.
  - apply COM.
  - eapply dcompat0_mon.
    + apply COM.
    + apply CLO.
    + apply LE.
Qed.

Lemma pcpn0_mon: monotone0 pcpn0.
Proof.
  red; intros. eapply paco0_mon. apply IN.
  intros. eapply dcpn0_mon. apply PR. apply LE.
Qed.

Lemma ucpn0_mon: monotone0 ucpn0.
Proof.
  red; intros. eapply upaco0_mon. apply IN.
  intros. eapply dcpn0_mon. apply PR. apply LE.
Qed.

Lemma dcpn0_greatest: forall clo (COM: dcompatible0 clo), clo <1= dcpn0.
Proof. intros. econstructor;[apply COM|apply PR]. Qed.

Lemma dcpn0_compat: dcompatible0 dcpn0.
Proof.
  econstructor; [apply dcpn0_mon| |]; intros.
  - destruct PR; eapply gf_mon with (r:=clo r).
    + eapply (dcompat0_compat COM); apply CLO.
    + intros. econstructor; [apply COM|apply PR].
  - destruct PR.
    eapply (dcompat0_distr COM) in CLO.
    destruct CLO.
    + left. eapply dcpn0_greatest. apply COM. apply H.
    + right. eapply dcpn0_greatest. apply COM. apply H.
Qed.

Lemma dcpn0_base: forall r, r <0= dcpn0 r.
Proof.
  exists id; [|apply PR].
  econstructor; repeat intro.
  + apply LE, IN.
  + apply PR0.
  + destruct PR0.
    * left. apply H.
    * right. apply H.
Qed.

Lemma ucpn0_base: forall r, r <0= ucpn0 r.
Proof.
  right. apply dcpn0_base. apply PR.
Qed.

Lemma ucpn0_from_dcpn0_upaco r:
  dcpn0 (upaco0 gf r) <0= ucpn0 r.
Proof.
  intros.
  eapply (dcompat0_distr dcpn0_compat) in PR.
  destruct PR as [IN|IN]; cycle 1.
  - right. apply IN.
  - left. revert IN.
    pcofix CIH. intros.
    pstep. eapply gf_mon.
    + apply (dcompat0_compat dcpn0_compat).
      eapply dcpn0_mon. apply IN.
      intros. _punfold PR. apply PR. apply gf_mon.
    + intros. apply (dcompat0_distr dcpn0_compat) in PR.
      right. destruct PR.
      * apply CIH. apply H.
      * apply CIH0. apply H.
Qed.

Lemma dcpn0_dcpn: forall r,
    dcpn0 (dcpn0 r) <0= dcpn0 r.
Proof.
  intros. exists (compose dcpn0 dcpn0); [|apply PR].
  econstructor.
  - repeat intro. eapply dcpn0_mon; [apply IN|].
    intros. eapply dcpn0_mon; [apply PR0|apply LE].
  - intros. eapply (dcompat0_compat dcpn0_compat).
    eapply dcpn0_mon; [apply PR0|].
    intros. eapply (dcompat0_compat dcpn0_compat), PR1.
  - intros. eapply (dcompat0_distr dcpn0_compat).
    eapply dcpn0_mon, (dcompat0_distr dcpn0_compat).
    apply PR0.
Qed.

Lemma ucpn0_ucpn: forall r,
    ucpn0 (ucpn0 r) <0= ucpn0 r.
Proof.
  intros. destruct PR.
  - left. eapply paco0_mult_strong.
    eapply paco0_mon. apply H.
    intros. apply ucpn0_from_dcpn0_upaco in PR.
    eapply upaco0_mon. apply PR.
    intros. apply dcpn0_dcpn. apply PR0.
  - red. apply ucpn0_from_dcpn0_upaco in H.
    eapply upaco0_mon. apply H.
    intros. apply dcpn0_dcpn. apply PR.
Qed.

Lemma ucpn0_compat r: ucpn0 (gf r) <0= gf (ucpn0 r).
Proof.
  intros. destruct PR; cycle 1.
  - apply dcpn0_compat in H.
    eapply gf_mon. apply H.
    intros. right. apply PR.
  - _punfold H; [|apply gf_mon]. eapply gf_mon. apply H.
    intros. apply ucpn0_ucpn.
    eapply upaco0_mon. apply PR.
    intros. eapply dcpn0_mon. apply PR0.
    intros. left. pstep. eapply gf_mon. apply PR1.
    intros. apply ucpn0_base. apply PR2.
Qed.

Lemma ucpn0_init:
  ucpn0 bot0 <0= paco0 gf bot0.
Proof.
  pcofix CIH. intros.
  destruct PR; cycle 1.
  - eapply paco0_mon_bot; [| intros; apply PR].
    eapply paco0_algebra, H. apply gf_mon. intros.
    eapply (dcompat0_compat dcpn0_compat).
    eapply dcpn0_mon. apply PR. contradiction.
  - _punfold H; [|apply gf_mon]. pstep.
    eapply gf_mon. apply H. intros.
    right. apply CIH. apply PR.
Qed.

Lemma pcpn0_final r:
  paco0 gf r <0= pcpn0 r.
Proof.
  intros. eapply paco0_mon. apply PR.
  intros. apply dcpn0_base. apply PR0.
Qed.

Lemma ucpn0_final r:
  upaco0 gf r <0= ucpn0 r.
Proof.
  intros. eapply upaco0_mon. apply PR.
  intros. apply dcpn0_base. apply PR0.
Qed.

Lemma ucpn0_clo
      r clo (LE: clo <1= ucpn0):
  clo (ucpn0 r) <0= ucpn0 r.
Proof.
  intros. apply ucpn0_ucpn, LE, PR.
Qed.

Lemma pcpn0_clo
      r clo (LE: clo <1= ucpn0):
  clo (pcpn0 r) <0= pcpn0 r.
Proof.
  intros. pstep. eapply gf_mon, ucpn0_ucpn.
  apply ucpn0_compat. apply LE in PR.
  eapply ucpn0_mon. apply PR.
  intros. _punfold PR0. apply PR0. apply gf_mon.
Qed.

Lemma pcpn0_unfold r:
  pcpn0 r <0= gf (ucpn0 r).
Proof.
  intros. _punfold PR. apply PR. apply gf_mon.
Qed.

Lemma ucpn0_unfold:
  ucpn0 bot0 <0= gf(ucpn0 bot0).
Proof.
  intros. apply pcpn0_unfold, pcpn0_final, ucpn0_init, PR.
Qed.

Lemma pcpn0_step r:
  gf (ucpn0 r) <0= pcpn0 r.
Proof.
  intros. pstep. apply PR.
Qed.

Lemma ucpn0_step r:
  gf (ucpn0 r) <0= ucpn0 r.
Proof.
  left. apply pcpn0_step. apply PR.
Qed.

Lemma ucpn0_id r : ucpn0 r <0= ucpn0 r.
Proof. intros. apply PR. Qed.

Lemma pcpn0_id r : pcpn0 r <0= pcpn0 r.
Proof. intros. apply PR. Qed.

Lemma gf_dcpn0_mon: monotone0 (compose gf dcpn0).
Proof.
  repeat intro. eapply gf_mon. apply IN.
  intros. eapply dcpn0_mon. apply PR. apply LE.  
Qed.

Lemma pcpn0_from_paco r: paco0 (compose gf dcpn0) r <0= pcpn0 r.
Proof.
  intros. apply dcpn0_base in PR. revert PR.
  pcofix CIH. intros.
  pstep.
  eapply gf_mon; cycle 1.
  { instantiate (1:= _ \0/ _). right.
    destruct PR0; [apply CIH, H | apply CIH0, H]. }
  eapply gf_mon, (dcompat0_distr dcpn0_compat).
  eapply gf_mon, dcpn0_dcpn.
  eapply (dcompat0_compat dcpn0_compat).
  eapply dcpn0_mon. apply PR.
  intros. _punfold PR0. apply PR0. apply gf_dcpn0_mon.
Qed.

Lemma pcpn0_to_paco r: pcpn0 r <0= paco0 (compose gf dcpn0) r.
Proof.
  pcofix CIH. intros.
  pstep. _punfold PR; [|apply gf_mon].
  eapply gf_mon. apply PR. intros.
  destruct PR0; cycle 1.
  - eapply dcpn0_mon. apply H. intros.
    right. apply CIH0, PR0. 
  - apply dcpn0_base. right. apply CIH, H.
Qed.

Lemma pcpn0_cofix
    r l (OBG: forall rr (INC: r <0= rr) (CIH: l <0= rr), l <0= pcpn0 rr):
  l <0= pcpn0 r.
Proof.
  under_forall ltac:(apply pcpn0_from_paco).
  pcofix CIH. intros. apply pcpn0_to_paco.
  apply OBG. apply CIH0. apply CIH. apply PR.
Qed.

(**
  Recursive Closure & Weak Compatibility
*)

Inductive rclo0 (clo: rel->rel) (r: rel): rel :=
| rclo0_base
   
    (R: r):
    @rclo0 clo r
| rclo0_clo'
    r'
    (R': r' <0= rclo0 clo r)
    (CLOR': clo r'):
    @rclo0 clo r
| rclo0_dcpn'
    r'
    (R': r' <0= rclo0 clo r)
    (CLOR': @dcpn0 r'):
    @rclo0 clo r
.

Structure wdcompatible0 (clo: rel -> rel) : Prop :=
  wdcompat0_intro {
      wdcompat0_mon: monotone0 clo;
      wdcompat0_wcompat: forall r,
          clo (gf r) <0= gf (rclo0 clo r);
      wdcompat0_distr : forall r1 r2,
          clo (r1 \0/ r2) <0= (clo r1 \0/ clo r2);
    }.

Lemma rclo0_mon_gen clo clo' r r'
      (IN: @rclo0 clo r)
      (LEclo: clo <1= clo')
      (LEr: r <0= r') :
  @rclo0 clo' r'.
Proof.
  induction IN; intros.
  - econstructor 1. apply LEr, R.
  - econstructor 2; [intros; eapply H, PR|apply LEclo, CLOR'].
  - econstructor 3; [intros; eapply H, PR|].
    eapply dcpn0_mon; [apply CLOR'|].
    intros. apply PR.
Qed.

Lemma rclo0_mon clo:
  monotone0 (rclo0 clo).
Proof.
  repeat intro. eapply rclo0_mon_gen; [apply IN|intros; apply PR|apply LE].
Qed.

Lemma rclo0_clo clo r:
  clo (rclo0 clo r) <0= rclo0 clo r.
Proof.
  intros. econstructor 2; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo0_dcpn clo r:
  dcpn0 (rclo0 clo r) <0= rclo0 clo r.
Proof.
  intros. econstructor 3; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo0_mult clo r:
  rclo0 clo (rclo0 clo r) <0= rclo0 clo r.
Proof.
  intros. induction PR.
  - apply R.
  - econstructor 2; [eapply H | eapply CLOR'].
  - econstructor 3; [eapply H | eapply CLOR'].
Qed.

Lemma rclo0_compose clo r:
  rclo0 (rclo0 clo) r <0= rclo0 clo r.
Proof.
  intros. induction PR.
  - apply rclo0_base, R.
  - apply rclo0_mult.
    eapply rclo0_mon; [apply CLOR'|apply H].
  - apply rclo0_dcpn.
    eapply dcpn0_mon; [apply CLOR'|apply H].
Qed.

Lemma wdcompat0_dcompat
      clo (WCOM: wdcompatible0 clo):
  dcompatible0 (rclo0 clo).
Proof.
  econstructor; [eapply rclo0_mon| |]; intros.
  - induction PR; intros.
    + eapply gf_mon; [apply R|]. intros.
      apply rclo0_base. apply PR.
    + eapply gf_mon.
      * eapply (wdcompat0_wcompat WCOM).
        eapply (wdcompat0_mon WCOM); [apply CLOR'|apply H].
      * intros. apply rclo0_mult, PR.
    + eapply gf_mon; [|intros; apply rclo0_dcpn, PR].
      eapply (dcompat0_compat dcpn0_compat).
      eapply dcpn0_mon; [apply CLOR'|apply H].
  - induction PR; intros.
    + destruct R as [R|R]; [left | right]; econstructor; apply R.
    + assert (CLOR:= wdcompat0_mon WCOM CLOR' H).
      eapply (wdcompat0_distr WCOM) in CLOR.
      destruct CLOR as [CLOR|CLOR]; [left|right]; apply rclo0_clo, CLOR.
    + assert (CLOR:= dcpn0_mon CLOR' H).
      eapply (dcompat0_distr dcpn0_compat) in CLOR.
      destruct CLOR as [CLOR|CLOR]; [left|right]; apply rclo0_dcpn, CLOR.
Qed.

Lemma wcompat0_sound clo (WCOM: wdcompatible0 clo):
  clo <1= dcpn0.
Proof.
  intros. exists (rclo0 clo).
  - apply wdcompat0_dcompat, WCOM.
  - apply rclo0_clo.
    eapply (wdcompat0_mon WCOM); [apply PR|].
    intros. apply rclo0_base, PR0.
Qed.

End PacoCompanion0_main.

Lemma pcpn0_mon_bot (gf gf': rel -> rel) r
      (IN: @pcpn0 gf bot0)
      (MON: monotone0 gf)
      (LE: gf <1= gf'):
  @pcpn0 gf' r.
Proof.
  eapply paco0_mon_bot, LE.
  apply ucpn0_init. apply MON. left. apply IN.
Qed.

Lemma ucpn0_mon_bot (gf gf': rel -> rel) r
      (IN: @ucpn0 gf bot0)
      (MON: monotone0 gf)
      (LE: gf <1= gf'):
  @ucpn0 gf' r.
Proof.
  eapply upaco0_mon_bot, LE.
  left. apply ucpn0_init. apply MON. apply IN.
Qed.

End PacoCompanion0.

Hint Resolve ucpn0_base : paco.
Hint Resolve pcpn0_step : paco.
Hint Resolve ucpn0_step : paco.

Hint Constructors rclo0 : rclo.
Hint Resolve rclo0_clo rclo0_dcpn : rclo.