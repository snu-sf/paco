Require Export Program.Basics. Open Scope program_scope.
Require Import paco2 pacotac.
Set Implicit Arguments.

Section PacoCompanion2.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.

Local Notation rel := (rel2 T0 T1).

Section PacoCompanion2_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone2 gf.

(** 
  Distributive Compatibility, Distributive Companion, (U)Paco Companion 
*)

Structure dcompatible2 (clo: rel -> rel) : Prop :=
  dcompat2_intro {
      dcompat2_mon: monotone2 clo;
      dcompat2_compat : forall r,
          clo (gf r) <2= gf (clo r);
      dcompat2_distr : forall r1 r2,
          clo (r1 \2/ r2) <2= (clo r1 \2/ clo r2);
    }.

Inductive dcpn2 (r: rel) x0 x1 : Prop :=
| dcpn2_intro
    clo
    (COM: dcompatible2 clo)
    (CLO: clo r x0 x1)
.

Definition pcpn2 r := paco2 gf (dcpn2 r).
Definition ucpn2 r := upaco2 gf (dcpn2 r).

Lemma dcpn2_mon: monotone2 dcpn2.
Proof.
  red; intros.
  destruct IN. exists clo.
  - apply COM.
  - eapply dcompat2_mon.
    + apply COM.
    + apply CLO.
    + apply LE.
Qed.

Lemma pcpn2_mon: monotone2 pcpn2.
Proof.
  red; intros. eapply paco2_mon. apply IN.
  intros. eapply dcpn2_mon. apply PR. apply LE.
Qed.

Lemma ucpn2_mon: monotone2 ucpn2.
Proof.
  red; intros. eapply upaco2_mon. apply IN.
  intros. eapply dcpn2_mon. apply PR. apply LE.
Qed.

Lemma dcpn2_greatest: forall clo (COM: dcompatible2 clo), clo <3= dcpn2.
Proof. intros. econstructor;[apply COM|apply PR]. Qed.

Lemma dcpn2_compat: dcompatible2 dcpn2.
Proof.
  econstructor; [apply dcpn2_mon| |]; intros.
  - destruct PR; eapply gf_mon with (r:=clo r).
    + eapply (dcompat2_compat COM); apply CLO.
    + intros. econstructor; [apply COM|apply PR].
  - destruct PR.
    eapply (dcompat2_distr COM) in CLO.
    destruct CLO.
    + left. eapply dcpn2_greatest. apply COM. apply H.
    + right. eapply dcpn2_greatest. apply COM. apply H.
Qed.

Lemma dcpn2_base: forall r, r <2= dcpn2 r.
Proof.
  exists id; [|apply PR].
  econstructor; repeat intro.
  + apply LE, IN.
  + apply PR0.
  + destruct PR0.
    * left. apply H.
    * right. apply H.
Qed.

Lemma ucpn2_base: forall r, r <2= ucpn2 r.
Proof.
  right. apply dcpn2_base. apply PR.
Qed.

Lemma ucpn2_from_dcpn2_upaco r:
  dcpn2 (upaco2 gf r) <2= ucpn2 r.
Proof.
  intros.
  eapply (dcompat2_distr dcpn2_compat) in PR.
  destruct PR as [IN|IN]; cycle 1.
  - right. apply IN.
  - left. revert x0 x1 IN.
    pcofix CIH. intros.
    pstep. eapply gf_mon.
    + apply (dcompat2_compat dcpn2_compat).
      eapply dcpn2_mon. apply IN.
      intros. _punfold PR. apply PR. apply gf_mon.
    + intros. apply (dcompat2_distr dcpn2_compat) in PR.
      right. destruct PR.
      * apply CIH. apply H.
      * apply CIH0. apply H.
Qed.

Lemma dcpn2_dcpn: forall r,
    dcpn2 (dcpn2 r) <2= dcpn2 r.
Proof.
  intros. exists (compose dcpn2 dcpn2); [|apply PR].
  econstructor.
  - repeat intro. eapply dcpn2_mon; [apply IN|].
    intros. eapply dcpn2_mon; [apply PR0|apply LE].
  - intros. eapply (dcompat2_compat dcpn2_compat).
    eapply dcpn2_mon; [apply PR0|].
    intros. eapply (dcompat2_compat dcpn2_compat), PR1.
  - intros. eapply (dcompat2_distr dcpn2_compat).
    eapply dcpn2_mon, (dcompat2_distr dcpn2_compat).
    apply PR0.
Qed.

Lemma ucpn2_ucpn: forall r,
    ucpn2 (ucpn2 r) <2= ucpn2 r.
Proof.
  intros. destruct PR.
  - left. eapply paco2_mult_strong.
    eapply paco2_mon. apply H.
    intros. apply ucpn2_from_dcpn2_upaco in PR.
    eapply upaco2_mon. apply PR.
    intros. apply dcpn2_dcpn. apply PR0.
  - red. apply ucpn2_from_dcpn2_upaco in H.
    eapply upaco2_mon. apply H.
    intros. apply dcpn2_dcpn. apply PR.
Qed.

Lemma ucpn2_compat r: ucpn2 (gf r) <2= gf (ucpn2 r).
Proof.
  intros. destruct PR; cycle 1.
  - apply dcpn2_compat in H.
    eapply gf_mon. apply H.
    intros. right. apply PR.
  - _punfold H; [|apply gf_mon]. eapply gf_mon. apply H.
    intros. apply ucpn2_ucpn.
    eapply upaco2_mon. apply PR.
    intros. eapply dcpn2_mon. apply PR0.
    intros. left. pstep. eapply gf_mon. apply PR1.
    intros. apply ucpn2_base. apply PR2.
Qed.

Lemma ucpn2_init:
  ucpn2 bot2 <2= paco2 gf bot2.
Proof.
  pcofix CIH. intros.
  destruct PR; cycle 1.
  - eapply paco2_mon_bot; [| intros; apply PR].
    eapply paco2_algebra, H. apply gf_mon. intros.
    eapply (dcompat2_compat dcpn2_compat).
    eapply dcpn2_mon. apply PR. contradiction.
  - _punfold H; [|apply gf_mon]. pstep.
    eapply gf_mon. apply H. intros.
    right. apply CIH. apply PR.
Qed.

Lemma pcpn2_final r:
  paco2 gf r <2= pcpn2 r.
Proof.
  intros. eapply paco2_mon. apply PR.
  intros. apply dcpn2_base. apply PR0.
Qed.

Lemma ucpn2_final r:
  upaco2 gf r <2= ucpn2 r.
Proof.
  intros. eapply upaco2_mon. apply PR.
  intros. apply dcpn2_base. apply PR0.
Qed.

Lemma ucpn2_clo
      r clo (LE: clo <3= ucpn2):
  clo (ucpn2 r) <2= ucpn2 r.
Proof.
  intros. apply ucpn2_ucpn, LE, PR.
Qed.

Lemma pcpn2_clo
      r clo (LE: clo <3= ucpn2):
  clo (pcpn2 r) <2= pcpn2 r.
Proof.
  intros. pstep. eapply gf_mon, ucpn2_ucpn.
  apply ucpn2_compat. apply LE in PR.
  eapply ucpn2_mon. apply PR.
  intros. _punfold PR0. apply PR0. apply gf_mon.
Qed.

Lemma pcpn2_unfold r:
  pcpn2 r <2= gf (ucpn2 r).
Proof.
  intros. _punfold PR. apply PR. apply gf_mon.
Qed.

Lemma ucpn2_unfold:
  ucpn2 bot2 <2= gf(ucpn2 bot2).
Proof.
  intros. apply pcpn2_unfold, pcpn2_final, ucpn2_init, PR.
Qed.

Lemma pcpn2_step r:
  gf (ucpn2 r) <2= pcpn2 r.
Proof.
  intros. pstep. apply PR.
Qed.

Lemma ucpn2_step r:
  gf (ucpn2 r) <2= ucpn2 r.
Proof.
  left. apply pcpn2_step. apply PR.
Qed.

Lemma ucpn2_id r : ucpn2 r <2= ucpn2 r.
Proof. intros. apply PR. Qed.

Lemma pcpn2_id r : pcpn2 r <2= pcpn2 r.
Proof. intros. apply PR. Qed.

Lemma gf_dcpn2_mon: monotone2 (compose gf dcpn2).
Proof.
  repeat intro. eapply gf_mon. apply IN.
  intros. eapply dcpn2_mon. apply PR. apply LE.  
Qed.

Lemma pcpn2_from_paco r: paco2 (compose gf dcpn2) r <2= pcpn2 r.
Proof.
  intros. apply dcpn2_base in PR. revert x0 x1 PR.
  pcofix CIH. intros.
  pstep.
  eapply gf_mon; cycle 1.
  { instantiate (1:= _ \2/ _). right.
    destruct PR0; [apply CIH, H | apply CIH0, H]. }
  eapply gf_mon, (dcompat2_distr dcpn2_compat).
  eapply gf_mon, dcpn2_dcpn.
  eapply (dcompat2_compat dcpn2_compat).
  eapply dcpn2_mon. apply PR.
  intros. _punfold PR0. apply PR0. apply gf_dcpn2_mon.
Qed.

Lemma pcpn2_to_paco r: pcpn2 r <2= paco2 (compose gf dcpn2) r.
Proof.
  pcofix CIH. intros.
  pstep. _punfold PR; [|apply gf_mon].
  eapply gf_mon. apply PR. intros.
  destruct PR0; cycle 1.
  - eapply dcpn2_mon. apply H. intros.
    right. apply CIH0, PR0. 
  - apply dcpn2_base. right. apply CIH, H.
Qed.

Lemma pcpn2_cofix
    r l (OBG: forall rr (INC: r <2= rr) (CIH: l <2= rr), l <2= pcpn2 rr):
  l <2= pcpn2 r.
Proof.
  under_forall ltac:(apply pcpn2_from_paco).
  pcofix CIH. intros. apply pcpn2_to_paco.
  apply OBG. apply CIH0. apply CIH. apply PR.
Qed.

(**
  Recursive Closure & Weak Compatibility
*)

Inductive rclo2 (clo: rel->rel) (r: rel): rel :=
| rclo2_base
    x0 x1
    (R: r x0 x1):
    @rclo2 clo r x0 x1
| rclo2_clo'
    r' x0 x1
    (R': r' <2= rclo2 clo r)
    (CLOR': clo r' x0 x1):
    @rclo2 clo r x0 x1
| rclo2_dcpn'
    r' x0 x1
    (R': r' <2= rclo2 clo r)
    (CLOR': @dcpn2 r' x0 x1):
    @rclo2 clo r x0 x1
.

Structure wdcompatible2 (clo: rel -> rel) : Prop :=
  wdcompat2_intro {
      wdcompat2_mon: monotone2 clo;
      wdcompat2_wcompat: forall r,
          clo (gf r) <2= gf (rclo2 clo r);
      wdcompat2_distr : forall r1 r2,
          clo (r1 \2/ r2) <2= (clo r1 \2/ clo r2);
    }.

Lemma rclo2_mon_gen clo clo' r r' x0 x1
      (IN: @rclo2 clo r x0 x1)
      (LEclo: clo <3= clo')
      (LEr: r <2= r') :
  @rclo2 clo' r' x0 x1.
Proof.
  induction IN; intros.
  - econstructor 1. apply LEr, R.
  - econstructor 2; [intros; eapply H, PR|apply LEclo, CLOR'].
  - econstructor 3; [intros; eapply H, PR|].
    eapply dcpn2_mon; [apply CLOR'|].
    intros. apply PR.
Qed.

Lemma rclo2_mon clo:
  monotone2 (rclo2 clo).
Proof.
  repeat intro. eapply rclo2_mon_gen; [apply IN|intros; apply PR|apply LE].
Qed.

Lemma rclo2_clo clo r:
  clo (rclo2 clo r) <2= rclo2 clo r.
Proof.
  intros. econstructor 2; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo2_dcpn clo r:
  dcpn2 (rclo2 clo r) <2= rclo2 clo r.
Proof.
  intros. econstructor 3; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo2_mult clo r:
  rclo2 clo (rclo2 clo r) <2= rclo2 clo r.
Proof.
  intros. induction PR.
  - apply R.
  - econstructor 2; [eapply H | eapply CLOR'].
  - econstructor 3; [eapply H | eapply CLOR'].
Qed.

Lemma rclo2_compose clo r:
  rclo2 (rclo2 clo) r <2= rclo2 clo r.
Proof.
  intros. induction PR.
  - apply rclo2_base, R.
  - apply rclo2_mult.
    eapply rclo2_mon; [apply CLOR'|apply H].
  - apply rclo2_dcpn.
    eapply dcpn2_mon; [apply CLOR'|apply H].
Qed.

Lemma wdcompat2_dcompat
      clo (WCOM: wdcompatible2 clo):
  dcompatible2 (rclo2 clo).
Proof.
  econstructor; [eapply rclo2_mon| |]; intros.
  - induction PR; intros.
    + eapply gf_mon; [apply R|]. intros.
      apply rclo2_base. apply PR.
    + eapply gf_mon.
      * eapply (wdcompat2_wcompat WCOM).
        eapply (wdcompat2_mon WCOM); [apply CLOR'|apply H].
      * intros. apply rclo2_mult, PR.
    + eapply gf_mon; [|intros; apply rclo2_dcpn, PR].
      eapply (dcompat2_compat dcpn2_compat).
      eapply dcpn2_mon; [apply CLOR'|apply H].
  - induction PR; intros.
    + destruct R as [R|R]; [left | right]; econstructor; apply R.
    + assert (CLOR:= wdcompat2_mon WCOM _ _ _ CLOR' H).
      eapply (wdcompat2_distr WCOM) in CLOR.
      destruct CLOR as [CLOR|CLOR]; [left|right]; apply rclo2_clo, CLOR.
    + assert (CLOR:= dcpn2_mon _ CLOR' H).
      eapply (dcompat2_distr dcpn2_compat) in CLOR.
      destruct CLOR as [CLOR|CLOR]; [left|right]; apply rclo2_dcpn, CLOR.
Qed.

Lemma wcompat2_sound clo (WCOM: wdcompatible2 clo):
  clo <3= dcpn2.
Proof.
  intros. exists (rclo2 clo).
  - apply wdcompat2_dcompat, WCOM.
  - apply rclo2_clo.
    eapply (wdcompat2_mon WCOM); [apply PR|].
    intros. apply rclo2_base, PR0.
Qed.

End PacoCompanion2_main.

Lemma pcpn2_mon_bot (gf gf': rel -> rel) x0 x1 r
      (IN: @pcpn2 gf bot2 x0 x1)
      (MON: monotone2 gf)
      (LE: gf <3= gf'):
  @pcpn2 gf' r x0 x1.
Proof.
  eapply paco2_mon_bot, LE.
  apply ucpn2_init. apply MON. left. apply IN.
Qed.

Lemma ucpn2_mon_bot (gf gf': rel -> rel) x0 x1 r
      (IN: @ucpn2 gf bot2 x0 x1)
      (MON: monotone2 gf)
      (LE: gf <3= gf'):
  @ucpn2 gf' r x0 x1.
Proof.
  eapply upaco2_mon_bot, LE.
  left. apply ucpn2_init. apply MON. apply IN.
Qed.

End PacoCompanion2.

Hint Resolve ucpn2_base : paco.
Hint Resolve pcpn2_step : paco.
Hint Resolve ucpn2_step : paco.

Hint Constructors rclo2 : rclo.
Hint Resolve rclo2_clo rclo2_dcpn : rclo.
