Require Export Program.Basics. Open Scope program_scope.
Require Import paco6 pacotac.
Set Implicit Arguments.

Section PacoCompanion6.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.

Local Notation rel := (rel6 T0 T1 T2 T3 T4 T5).

Section PacoCompanion6_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone6 gf.

(** 
  Distributive Compatibility, Distributive Companion, (U)Paco Companion 
*)

Structure dcompatible6 (clo: rel -> rel) : Prop :=
  dcompat6_intro {
      dcompat6_mon: monotone6 clo;
      dcompat6_compat : forall r,
          clo (gf r) <6= gf (clo r);
      dcompat6_distr : forall r1 r2,
          clo (r1 \6/ r2) <6= (clo r1 \6/ clo r2);
    }.

Inductive dcpn6 (r: rel) x0 x1 x2 x3 x4 x5 : Prop :=
| dcpn6_intro
    clo
    (COM: dcompatible6 clo)
    (CLO: clo r x0 x1 x2 x3 x4 x5)
.

Definition pcpn6 r := paco6 gf (dcpn6 r).
Definition ucpn6 r := upaco6 gf (dcpn6 r).

Lemma dcpn6_mon: monotone6 dcpn6.
Proof.
  red; intros.
  destruct IN. exists clo.
  - apply COM.
  - eapply dcompat6_mon.
    + apply COM.
    + apply CLO.
    + apply LE.
Qed.

Lemma pcpn6_mon: monotone6 pcpn6.
Proof.
  red; intros. eapply paco6_mon. apply IN.
  intros. eapply dcpn6_mon. apply PR. apply LE.
Qed.

Lemma ucpn6_mon: monotone6 ucpn6.
Proof.
  red; intros. eapply upaco6_mon. apply IN.
  intros. eapply dcpn6_mon. apply PR. apply LE.
Qed.

Lemma dcpn6_greatest: forall clo (COM: dcompatible6 clo), clo <7= dcpn6.
Proof. intros. econstructor;[apply COM|apply PR]. Qed.

Lemma dcpn6_compat: dcompatible6 dcpn6.
Proof.
  econstructor; [apply dcpn6_mon| |]; intros.
  - destruct PR; eapply gf_mon with (r:=clo r).
    + eapply (dcompat6_compat COM); apply CLO.
    + intros. econstructor; [apply COM|apply PR].
  - destruct PR.
    eapply (dcompat6_distr COM) in CLO.
    destruct CLO.
    + left. eapply dcpn6_greatest. apply COM. apply H.
    + right. eapply dcpn6_greatest. apply COM. apply H.
Qed.

Lemma dcpn6_base: forall r, r <6= dcpn6 r.
Proof.
  exists id; [|apply PR].
  econstructor; repeat intro.
  + apply LE, IN.
  + apply PR0.
  + destruct PR0.
    * left. apply H.
    * right. apply H.
Qed.

Lemma ucpn6_base: forall r, r <6= ucpn6 r.
Proof.
  right. apply dcpn6_base. apply PR.
Qed.

Lemma ucpn6_from_dcpn6_upaco r:
  dcpn6 (upaco6 gf r) <6= ucpn6 r.
Proof.
  intros.
  eapply (dcompat6_distr dcpn6_compat) in PR.
  destruct PR as [IN|IN]; cycle 1.
  - right. apply IN.
  - left. revert x0 x1 x2 x3 x4 x5 IN.
    pcofix CIH. intros.
    pstep. eapply gf_mon.
    + apply (dcompat6_compat dcpn6_compat).
      eapply dcpn6_mon. apply IN.
      intros. _punfold PR. apply PR. apply gf_mon.
    + intros. apply (dcompat6_distr dcpn6_compat) in PR.
      right. destruct PR.
      * apply CIH. apply H.
      * apply CIH0. apply H.
Qed.

Lemma dcpn6_dcpn: forall r,
    dcpn6 (dcpn6 r) <6= dcpn6 r.
Proof.
  intros. exists (compose dcpn6 dcpn6); [|apply PR].
  econstructor.
  - repeat intro. eapply dcpn6_mon; [apply IN|].
    intros. eapply dcpn6_mon; [apply PR0|apply LE].
  - intros. eapply (dcompat6_compat dcpn6_compat).
    eapply dcpn6_mon; [apply PR0|].
    intros. eapply (dcompat6_compat dcpn6_compat), PR1.
  - intros. eapply (dcompat6_distr dcpn6_compat).
    eapply dcpn6_mon, (dcompat6_distr dcpn6_compat).
    apply PR0.
Qed.

Lemma ucpn6_ucpn: forall r,
    ucpn6 (ucpn6 r) <6= ucpn6 r.
Proof.
  intros. destruct PR.
  - left. eapply paco6_mult_strong.
    eapply paco6_mon. apply H.
    intros. apply ucpn6_from_dcpn6_upaco in PR.
    eapply upaco6_mon. apply PR.
    intros. apply dcpn6_dcpn. apply PR0.
  - red. apply ucpn6_from_dcpn6_upaco in H.
    eapply upaco6_mon. apply H.
    intros. apply dcpn6_dcpn. apply PR.
Qed.

Lemma ucpn6_compat r: ucpn6 (gf r) <6= gf (ucpn6 r).
Proof.
  intros. destruct PR; cycle 1.
  - apply dcpn6_compat in H.
    eapply gf_mon. apply H.
    intros. right. apply PR.
  - _punfold H; [|apply gf_mon]. eapply gf_mon. apply H.
    intros. apply ucpn6_ucpn.
    eapply upaco6_mon. apply PR.
    intros. eapply dcpn6_mon. apply PR0.
    intros. left. pstep. eapply gf_mon. apply PR1.
    intros. apply ucpn6_base. apply PR2.
Qed.

Lemma ucpn6_init:
  ucpn6 bot6 <6= paco6 gf bot6.
Proof.
  pcofix CIH. intros.
  destruct PR; cycle 1.
  - eapply paco6_mon_bot; [| intros; apply PR].
    eapply paco6_algebra, H. apply gf_mon. intros.
    eapply (dcompat6_compat dcpn6_compat).
    eapply dcpn6_mon. apply PR. contradiction.
  - _punfold H; [|apply gf_mon]. pstep.
    eapply gf_mon. apply H. intros.
    right. apply CIH. apply PR.
Qed.

Lemma pcpn6_final r:
  paco6 gf r <6= pcpn6 r.
Proof.
  intros. eapply paco6_mon. apply PR.
  intros. apply dcpn6_base. apply PR0.
Qed.

Lemma ucpn6_final r:
  upaco6 gf r <6= ucpn6 r.
Proof.
  intros. eapply upaco6_mon. apply PR.
  intros. apply dcpn6_base. apply PR0.
Qed.

Lemma ucpn6_clo
      r clo (LE: clo <7= ucpn6):
  clo (ucpn6 r) <6= ucpn6 r.
Proof.
  intros. apply ucpn6_ucpn, LE, PR.
Qed.

Lemma pcpn6_clo
      r clo (LE: clo <7= ucpn6):
  clo (pcpn6 r) <6= pcpn6 r.
Proof.
  intros. pstep. eapply gf_mon, ucpn6_ucpn.
  apply ucpn6_compat. apply LE in PR.
  eapply ucpn6_mon. apply PR.
  intros. _punfold PR0. apply PR0. apply gf_mon.
Qed.

Lemma pcpn6_unfold r:
  pcpn6 r <6= gf (ucpn6 r).
Proof.
  intros. _punfold PR. apply PR. apply gf_mon.
Qed.

Lemma ucpn6_unfold:
  ucpn6 bot6 <6= gf(ucpn6 bot6).
Proof.
  intros. apply pcpn6_unfold, pcpn6_final, ucpn6_init, PR.
Qed.

Lemma pcpn6_step r:
  gf (ucpn6 r) <6= pcpn6 r.
Proof.
  intros. pstep. apply PR.
Qed.

Lemma ucpn6_step r:
  gf (ucpn6 r) <6= ucpn6 r.
Proof.
  left. apply pcpn6_step. apply PR.
Qed.

Lemma ucpn6_id r : ucpn6 r <6= ucpn6 r.
Proof. intros. apply PR. Qed.

Lemma pcpn6_id r : pcpn6 r <6= pcpn6 r.
Proof. intros. apply PR. Qed.

Lemma gf_dcpn6_mon: monotone6 (compose gf dcpn6).
Proof.
  repeat intro. eapply gf_mon. apply IN.
  intros. eapply dcpn6_mon. apply PR. apply LE.  
Qed.

Lemma pcpn6_from_paco r: paco6 (compose gf dcpn6) r <6= pcpn6 r.
Proof.
  intros. apply dcpn6_base in PR. revert x0 x1 x2 x3 x4 x5 PR.
  pcofix CIH. intros.
  pstep.
  eapply gf_mon; cycle 1.
  { instantiate (1:= _ \6/ _). right.
    destruct PR0; [apply CIH, H | apply CIH0, H]. }
  eapply gf_mon, (dcompat6_distr dcpn6_compat).
  eapply gf_mon, dcpn6_dcpn.
  eapply (dcompat6_compat dcpn6_compat).
  eapply dcpn6_mon. apply PR.
  intros. _punfold PR0. apply PR0. apply gf_dcpn6_mon.
Qed.

Lemma pcpn6_to_paco r: pcpn6 r <6= paco6 (compose gf dcpn6) r.
Proof.
  pcofix CIH. intros.
  pstep. _punfold PR; [|apply gf_mon].
  eapply gf_mon. apply PR. intros.
  destruct PR0; cycle 1.
  - eapply dcpn6_mon. apply H. intros.
    right. apply CIH0, PR0. 
  - apply dcpn6_base. right. apply CIH, H.
Qed.

Lemma pcpn6_cofix
    r l (OBG: forall rr (INC: r <6= rr) (CIH: l <6= rr), l <6= pcpn6 rr):
  l <6= pcpn6 r.
Proof.
  under_forall ltac:(apply pcpn6_from_paco).
  pcofix CIH. intros. apply pcpn6_to_paco.
  apply OBG. apply CIH0. apply CIH. apply PR.
Qed.

(**
  Recursive Closure & Weak Compatibility
*)

Inductive rclo6 (clo: rel->rel) (r: rel): rel :=
| rclo6_base
    x0 x1 x2 x3 x4 x5
    (R: r x0 x1 x2 x3 x4 x5):
    @rclo6 clo r x0 x1 x2 x3 x4 x5
| rclo6_clo'
    r' x0 x1 x2 x3 x4 x5
    (R': r' <6= rclo6 clo r)
    (CLOR': clo r' x0 x1 x2 x3 x4 x5):
    @rclo6 clo r x0 x1 x2 x3 x4 x5
| rclo6_dcpn'
    r' x0 x1 x2 x3 x4 x5
    (R': r' <6= rclo6 clo r)
    (CLOR': @dcpn6 r' x0 x1 x2 x3 x4 x5):
    @rclo6 clo r x0 x1 x2 x3 x4 x5
.

Structure wdcompatible6 (clo: rel -> rel) : Prop :=
  wdcompat6_intro {
      wdcompat6_mon: monotone6 clo;
      wdcompat6_wcompat: forall r,
          clo (gf r) <6= gf (rclo6 clo r);
      wdcompat6_distr : forall r1 r2,
          clo (r1 \6/ r2) <6= (clo r1 \6/ clo r2);
    }.

Lemma rclo6_mon_gen clo clo' r r' x0 x1 x2 x3 x4 x5
      (IN: @rclo6 clo r x0 x1 x2 x3 x4 x5)
      (LEclo: clo <7= clo')
      (LEr: r <6= r') :
  @rclo6 clo' r' x0 x1 x2 x3 x4 x5.
Proof.
  induction IN; intros.
  - econstructor 1. apply LEr, R.
  - econstructor 2; [intros; eapply H, PR|apply LEclo, CLOR'].
  - econstructor 3; [intros; eapply H, PR|].
    eapply dcpn6_mon; [apply CLOR'|].
    intros. apply PR.
Qed.

Lemma rclo6_mon clo:
  monotone6 (rclo6 clo).
Proof.
  repeat intro. eapply rclo6_mon_gen; [apply IN|intros; apply PR|apply LE].
Qed.

Lemma rclo6_clo clo r:
  clo (rclo6 clo r) <6= rclo6 clo r.
Proof.
  intros. econstructor 2; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo6_dcpn clo r:
  dcpn6 (rclo6 clo r) <6= rclo6 clo r.
Proof.
  intros. econstructor 3; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo6_mult clo r:
  rclo6 clo (rclo6 clo r) <6= rclo6 clo r.
Proof.
  intros. induction PR.
  - apply R.
  - econstructor 2; [eapply H | eapply CLOR'].
  - econstructor 3; [eapply H | eapply CLOR'].
Qed.

Lemma rclo6_compose clo r:
  rclo6 (rclo6 clo) r <6= rclo6 clo r.
Proof.
  intros. induction PR.
  - apply rclo6_base, R.
  - apply rclo6_mult.
    eapply rclo6_mon; [apply CLOR'|apply H].
  - apply rclo6_dcpn.
    eapply dcpn6_mon; [apply CLOR'|apply H].
Qed.

Lemma wdcompat6_dcompat
      clo (WCOM: wdcompatible6 clo):
  dcompatible6 (rclo6 clo).
Proof.
  econstructor; [eapply rclo6_mon| |]; intros.
  - induction PR; intros.
    + eapply gf_mon; [apply R|]. intros.
      apply rclo6_base. apply PR.
    + eapply gf_mon.
      * eapply (wdcompat6_wcompat WCOM).
        eapply (wdcompat6_mon WCOM); [apply CLOR'|apply H].
      * intros. apply rclo6_mult, PR.
    + eapply gf_mon; [|intros; apply rclo6_dcpn, PR].
      eapply (dcompat6_compat dcpn6_compat).
      eapply dcpn6_mon; [apply CLOR'|apply H].
  - induction PR; intros.
    + destruct R as [R|R]; [left | right]; econstructor; apply R.
    + assert (CLOR:= wdcompat6_mon WCOM _ _ _ CLOR' H).
      eapply (wdcompat6_distr WCOM) in CLOR.
      destruct CLOR as [CLOR|CLOR]; [left|right]; apply rclo6_clo, CLOR.
    + assert (CLOR:= dcpn6_mon _ CLOR' H).
      eapply (dcompat6_distr dcpn6_compat) in CLOR.
      destruct CLOR as [CLOR|CLOR]; [left|right]; apply rclo6_dcpn, CLOR.
Qed.

Lemma wcompat6_sound clo (WCOM: wdcompatible6 clo):
  clo <7= dcpn6.
Proof.
  intros. exists (rclo6 clo).
  - apply wdcompat6_dcompat, WCOM.
  - apply rclo6_clo.
    eapply (wdcompat6_mon WCOM); [apply PR|].
    intros. apply rclo6_base, PR0.
Qed.

End PacoCompanion6_main.

Lemma pcpn6_mon_bot (gf gf': rel -> rel) x0 x1 x2 x3 x4 x5 r
      (IN: @pcpn6 gf bot6 x0 x1 x2 x3 x4 x5)
      (MON: monotone6 gf)
      (LE: gf <7= gf'):
  @pcpn6 gf' r x0 x1 x2 x3 x4 x5.
Proof.
  eapply paco6_mon_bot, LE.
  apply ucpn6_init. apply MON. left. apply IN.
Qed.

Lemma ucpn6_mon_bot (gf gf': rel -> rel) x0 x1 x2 x3 x4 x5 r
      (IN: @ucpn6 gf bot6 x0 x1 x2 x3 x4 x5)
      (MON: monotone6 gf)
      (LE: gf <7= gf'):
  @ucpn6 gf' r x0 x1 x2 x3 x4 x5.
Proof.
  eapply upaco6_mon_bot, LE.
  left. apply ucpn6_init. apply MON. apply IN.
Qed.

End PacoCompanion6.

Hint Resolve ucpn6_base : paco.
Hint Resolve pcpn6_step : paco.
Hint Resolve ucpn6_step : paco.

Hint Constructors rclo6 : rclo.
Hint Resolve rclo6_clo rclo6_dcpn : rclo.
