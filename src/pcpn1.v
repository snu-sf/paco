Require Export Program.Basics. Open Scope program_scope.
Require Import paco1 pacotac.
Set Implicit Arguments.

Section PacoCompanion1.

Variable T0 : Type.

Local Notation rel := (rel1 T0).

Section PacoCompanion1_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone1 gf.

(** 
  Distributive Compatibility, Distributive Companion, (U)Paco Companion 
*)

Structure dcompatible1 (clo: rel -> rel) : Prop :=
  dcompat1_intro {
      dcompat1_mon: monotone1 clo;
      dcompat1_compat : forall r,
          clo (gf r) <1= gf (clo r);
      dcompat1_distr : forall r1 r2,
          clo (r1 \1/ r2) <1= (clo r1 \1/ clo r2);
    }.

Inductive dcpn1 (r: rel) x0 : Prop :=
| dcpn1_intro
    clo
    (COM: dcompatible1 clo)
    (CLO: clo r x0)
.

Definition pcpn1 r := paco1 gf (dcpn1 r).
Definition ucpn1 r := upaco1 gf (dcpn1 r).

Lemma dcpn1_mon: monotone1 dcpn1.
Proof.
  red; intros.
  destruct IN. exists clo.
  - apply COM.
  - eapply dcompat1_mon.
    + apply COM.
    + apply CLO.
    + apply LE.
Qed.

Lemma pcpn1_mon: monotone1 pcpn1.
Proof.
  red; intros. eapply paco1_mon. apply IN.
  intros. eapply dcpn1_mon. apply PR. apply LE.
Qed.

Lemma ucpn1_mon: monotone1 ucpn1.
Proof.
  red; intros. eapply upaco1_mon. apply IN.
  intros. eapply dcpn1_mon. apply PR. apply LE.
Qed.

Lemma dcpn1_greatest: forall clo (COM: dcompatible1 clo), clo <2= dcpn1.
Proof. intros. econstructor;[apply COM|apply PR]. Qed.

Lemma dcpn1_compat: dcompatible1 dcpn1.
Proof.
  econstructor; [apply dcpn1_mon| |]; intros.
  - destruct PR; eapply gf_mon with (r:=clo r).
    + eapply (dcompat1_compat COM); apply CLO.
    + intros. econstructor; [apply COM|apply PR].
  - destruct PR.
    eapply (dcompat1_distr COM) in CLO.
    destruct CLO.
    + left. eapply dcpn1_greatest. apply COM. apply H.
    + right. eapply dcpn1_greatest. apply COM. apply H.
Qed.

Lemma dcpn1_base: forall r, r <1= dcpn1 r.
Proof.
  exists id; [|apply PR].
  econstructor; repeat intro.
  + apply LE, IN.
  + apply PR0.
  + destruct PR0.
    * left. apply H.
    * right. apply H.
Qed.

Lemma ucpn1_base: forall r, r <1= ucpn1 r.
Proof.
  right. apply dcpn1_base. apply PR.
Qed.

Lemma ucpn1_from_dcpn1_upaco r:
  dcpn1 (upaco1 gf r) <1= ucpn1 r.
Proof.
  intros.
  eapply (dcompat1_distr dcpn1_compat) in PR.
  destruct PR as [IN|IN]; cycle 1.
  - right. apply IN.
  - left. revert x0 IN.
    pcofix CIH. intros.
    pstep. eapply gf_mon.
    + apply (dcompat1_compat dcpn1_compat).
      eapply dcpn1_mon. apply IN.
      intros. _punfold PR. apply PR. apply gf_mon.
    + intros. apply (dcompat1_distr dcpn1_compat) in PR.
      right. destruct PR.
      * apply CIH. apply H.
      * apply CIH0. apply H.
Qed.

Lemma dcpn1_dcpn: forall r,
    dcpn1 (dcpn1 r) <1= dcpn1 r.
Proof.
  intros. exists (compose dcpn1 dcpn1); [|apply PR].
  econstructor.
  - repeat intro. eapply dcpn1_mon; [apply IN|].
    intros. eapply dcpn1_mon; [apply PR0|apply LE].
  - intros. eapply (dcompat1_compat dcpn1_compat).
    eapply dcpn1_mon; [apply PR0|].
    intros. eapply (dcompat1_compat dcpn1_compat), PR1.
  - intros. eapply (dcompat1_distr dcpn1_compat).
    eapply dcpn1_mon, (dcompat1_distr dcpn1_compat).
    apply PR0.
Qed.

Lemma ucpn1_ucpn: forall r,
    ucpn1 (ucpn1 r) <1= ucpn1 r.
Proof.
  intros. destruct PR.
  - left. eapply paco1_mult_strong.
    eapply paco1_mon. apply H.
    intros. apply ucpn1_from_dcpn1_upaco in PR.
    eapply upaco1_mon. apply PR.
    intros. apply dcpn1_dcpn. apply PR0.
  - red. apply ucpn1_from_dcpn1_upaco in H.
    eapply upaco1_mon. apply H.
    intros. apply dcpn1_dcpn. apply PR.
Qed.

Lemma ucpn1_compat r: ucpn1 (gf r) <1= gf (ucpn1 r).
Proof.
  intros. destruct PR; cycle 1.
  - apply dcpn1_compat in H.
    eapply gf_mon. apply H.
    intros. right. apply PR.
  - _punfold H; [|apply gf_mon]. eapply gf_mon. apply H.
    intros. apply ucpn1_ucpn.
    eapply upaco1_mon. apply PR.
    intros. eapply dcpn1_mon. apply PR0.
    intros. left. pstep. eapply gf_mon. apply PR1.
    intros. apply ucpn1_base. apply PR2.
Qed.

Lemma ucpn1_init:
  ucpn1 bot1 <1= paco1 gf bot1.
Proof.
  pcofix CIH. intros.
  destruct PR; cycle 1.
  - eapply paco1_mon_bot; [| intros; apply PR].
    eapply paco1_algebra, H. apply gf_mon. intros.
    eapply (dcompat1_compat dcpn1_compat).
    eapply dcpn1_mon. apply PR. contradiction.
  - _punfold H; [|apply gf_mon]. pstep.
    eapply gf_mon. apply H. intros.
    right. apply CIH. apply PR.
Qed.

Lemma pcpn1_final r:
  paco1 gf r <1= pcpn1 r.
Proof.
  intros. eapply paco1_mon. apply PR.
  intros. apply dcpn1_base. apply PR0.
Qed.

Lemma ucpn1_final r:
  upaco1 gf r <1= ucpn1 r.
Proof.
  intros. eapply upaco1_mon. apply PR.
  intros. apply dcpn1_base. apply PR0.
Qed.

Lemma ucpn1_clo
      r clo (LE: clo <2= ucpn1):
  clo (ucpn1 r) <1= ucpn1 r.
Proof.
  intros. apply ucpn1_ucpn, LE, PR.
Qed.

Lemma pcpn1_clo
      r clo (LE: clo <2= ucpn1):
  clo (pcpn1 r) <1= pcpn1 r.
Proof.
  intros. pstep. eapply gf_mon, ucpn1_ucpn.
  apply ucpn1_compat. apply LE in PR.
  eapply ucpn1_mon. apply PR.
  intros. _punfold PR0. apply PR0. apply gf_mon.
Qed.

Lemma pcpn1_unfold r:
  pcpn1 r <1= gf (ucpn1 r).
Proof.
  intros. _punfold PR. apply PR. apply gf_mon.
Qed.

Lemma ucpn1_unfold:
  ucpn1 bot1 <1= gf(ucpn1 bot1).
Proof.
  intros. apply pcpn1_unfold, pcpn1_final, ucpn1_init, PR.
Qed.

Lemma pcpn1_step r:
  gf (ucpn1 r) <1= pcpn1 r.
Proof.
  intros. pstep. apply PR.
Qed.

Lemma ucpn1_step r:
  gf (ucpn1 r) <1= ucpn1 r.
Proof.
  left. apply pcpn1_step. apply PR.
Qed.

Lemma ucpn1_id r : ucpn1 r <1= ucpn1 r.
Proof. intros. apply PR. Qed.

Lemma pcpn1_id r : pcpn1 r <1= pcpn1 r.
Proof. intros. apply PR. Qed.

Lemma gf_dcpn1_mon: monotone1 (compose gf dcpn1).
Proof.
  repeat intro. eapply gf_mon. apply IN.
  intros. eapply dcpn1_mon. apply PR. apply LE.  
Qed.

Lemma pcpn1_from_paco r: paco1 (compose gf dcpn1) r <1= pcpn1 r.
Proof.
  intros. apply dcpn1_base in PR. revert x0 PR.
  pcofix CIH. intros.
  pstep.
  eapply gf_mon; cycle 1.
  { instantiate (1:= _ \1/ _). right.
    destruct PR0; [apply CIH, H | apply CIH0, H]. }
  eapply gf_mon, (dcompat1_distr dcpn1_compat).
  eapply gf_mon, dcpn1_dcpn.
  eapply (dcompat1_compat dcpn1_compat).
  eapply dcpn1_mon. apply PR.
  intros. _punfold PR0. apply PR0. apply gf_dcpn1_mon.
Qed.

Lemma pcpn1_to_paco r: pcpn1 r <1= paco1 (compose gf dcpn1) r.
Proof.
  pcofix CIH. intros.
  pstep. _punfold PR; [|apply gf_mon].
  eapply gf_mon. apply PR. intros.
  destruct PR0; cycle 1.
  - eapply dcpn1_mon. apply H. intros.
    right. apply CIH0, PR0. 
  - apply dcpn1_base. right. apply CIH, H.
Qed.

Lemma pcpn1_cofix
    r l (OBG: forall rr (INC: r <1= rr) (CIH: l <1= rr), l <1= pcpn1 rr):
  l <1= pcpn1 r.
Proof.
  under_forall ltac:(apply pcpn1_from_paco).
  pcofix CIH. intros. apply pcpn1_to_paco.
  apply OBG. apply CIH0. apply CIH. apply PR.
Qed.

(**
  Recursive Closure & Weak Compatibility
*)

Inductive rclo1 (clo: rel->rel) (r: rel): rel :=
| rclo1_base
    x0
    (R: r x0):
    @rclo1 clo r x0
| rclo1_clo'
    r' x0
    (R': r' <1= rclo1 clo r)
    (CLOR': clo r' x0):
    @rclo1 clo r x0
| rclo1_dcpn'
    r' x0
    (R': r' <1= rclo1 clo r)
    (CLOR': @dcpn1 r' x0):
    @rclo1 clo r x0
.

Structure wdcompatible1 (clo: rel -> rel) : Prop :=
  wdcompat1_intro {
      wdcompat1_mon: monotone1 clo;
      wdcompat1_wcompat: forall r,
          clo (gf r) <1= gf (rclo1 clo r);
      wdcompat1_distr : forall r1 r2,
          clo (r1 \1/ r2) <1= (clo r1 \1/ clo r2);
    }.

Lemma rclo1_mon_gen clo clo' r r' x0
      (IN: @rclo1 clo r x0)
      (LEclo: clo <2= clo')
      (LEr: r <1= r') :
  @rclo1 clo' r' x0.
Proof.
  induction IN; intros.
  - econstructor 1. apply LEr, R.
  - econstructor 2; [intros; eapply H, PR|apply LEclo, CLOR'].
  - econstructor 3; [intros; eapply H, PR|].
    eapply dcpn1_mon; [apply CLOR'|].
    intros. apply PR.
Qed.

Lemma rclo1_mon clo:
  monotone1 (rclo1 clo).
Proof.
  repeat intro. eapply rclo1_mon_gen; [apply IN|intros; apply PR|apply LE].
Qed.

Lemma rclo1_clo clo r:
  clo (rclo1 clo r) <1= rclo1 clo r.
Proof.
  intros. econstructor 2; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo1_dcpn clo r:
  dcpn1 (rclo1 clo r) <1= rclo1 clo r.
Proof.
  intros. econstructor 3; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo1_mult clo r:
  rclo1 clo (rclo1 clo r) <1= rclo1 clo r.
Proof.
  intros. induction PR.
  - apply R.
  - econstructor 2; [eapply H | eapply CLOR'].
  - econstructor 3; [eapply H | eapply CLOR'].
Qed.

Lemma rclo1_compose clo r:
  rclo1 (rclo1 clo) r <1= rclo1 clo r.
Proof.
  intros. induction PR.
  - apply rclo1_base, R.
  - apply rclo1_mult.
    eapply rclo1_mon; [apply CLOR'|apply H].
  - apply rclo1_dcpn.
    eapply dcpn1_mon; [apply CLOR'|apply H].
Qed.

Lemma wdcompat1_dcompat
      clo (WCOM: wdcompatible1 clo):
  dcompatible1 (rclo1 clo).
Proof.
  econstructor; [eapply rclo1_mon| |]; intros.
  - induction PR; intros.
    + eapply gf_mon; [apply R|]. intros.
      apply rclo1_base. apply PR.
    + eapply gf_mon.
      * eapply (wdcompat1_wcompat WCOM).
        eapply (wdcompat1_mon WCOM); [apply CLOR'|apply H].
      * intros. apply rclo1_mult, PR.
    + eapply gf_mon; [|intros; apply rclo1_dcpn, PR].
      eapply (dcompat1_compat dcpn1_compat).
      eapply dcpn1_mon; [apply CLOR'|apply H].
  - induction PR; intros.
    + destruct R as [R|R]; [left | right]; econstructor; apply R.
    + assert (CLOR:= wdcompat1_mon WCOM _ _ _ CLOR' H).
      eapply (wdcompat1_distr WCOM) in CLOR.
      destruct CLOR as [CLOR|CLOR]; [left|right]; apply rclo1_clo, CLOR.
    + assert (CLOR:= dcpn1_mon _ CLOR' H).
      eapply (dcompat1_distr dcpn1_compat) in CLOR.
      destruct CLOR as [CLOR|CLOR]; [left|right]; apply rclo1_dcpn, CLOR.
Qed.

Lemma wcompat1_sound clo (WCOM: wdcompatible1 clo):
  clo <2= dcpn1.
Proof.
  intros. exists (rclo1 clo).
  - apply wdcompat1_dcompat, WCOM.
  - apply rclo1_clo.
    eapply (wdcompat1_mon WCOM); [apply PR|].
    intros. apply rclo1_base, PR0.
Qed.

End PacoCompanion1_main.

Lemma pcpn1_mon_bot (gf gf': rel -> rel) x0 r
      (IN: @pcpn1 gf bot1 x0)
      (MON: monotone1 gf)
      (LE: gf <2= gf'):
  @pcpn1 gf' r x0.
Proof.
  eapply paco1_mon_bot, LE.
  apply ucpn1_init. apply MON. left. apply IN.
Qed.

Lemma ucpn1_mon_bot (gf gf': rel -> rel) x0 r
      (IN: @ucpn1 gf bot1 x0)
      (MON: monotone1 gf)
      (LE: gf <2= gf'):
  @ucpn1 gf' r x0.
Proof.
  eapply upaco1_mon_bot, LE.
  left. apply ucpn1_init. apply MON. apply IN.
Qed.

End PacoCompanion1.

Hint Resolve ucpn1_base : paco.
Hint Resolve pcpn1_step : paco.
Hint Resolve ucpn1_step : paco.

Hint Constructors rclo1 : rclo.
Hint Resolve rclo1_clo rclo1_dcpn : rclo.
