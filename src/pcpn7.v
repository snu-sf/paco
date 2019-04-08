Require Export Program.Basics. Open Scope program_scope.
Require Import paco7 pacotac.
Set Implicit Arguments.

Section PacoCompanion7.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.

Local Notation rel := (rel7 T0 T1 T2 T3 T4 T5 T6).

Section PacoCompanion7_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone7 gf.

(** 
  Distributive Compatibility, Distributive Companion, (U)Paco Companion 
*)

Structure dcompatible7 (clo: rel -> rel) : Prop :=
  dcompat7_intro {
      dcompat7_mon: monotone7 clo;
      dcompat7_compat : forall r,
          clo (gf r) <7= gf (clo r);
      dcompat7_distr : forall r1 r2,
          clo (r1 \7/ r2) <7= (clo r1 \7/ clo r2);
    }.

Inductive dcpn7 (r: rel) x0 x1 x2 x3 x4 x5 x6 : Prop :=
| dcpn7_intro
    clo
    (COM: dcompatible7 clo)
    (CLO: clo r x0 x1 x2 x3 x4 x5 x6)
.

Definition pcpn7 r := paco7 gf (dcpn7 r).
Definition ucpn7 r := upaco7 gf (dcpn7 r).

Lemma dcpn7_mon: monotone7 dcpn7.
Proof.
  red; intros.
  destruct IN. exists clo.
  - apply COM.
  - eapply dcompat7_mon.
    + apply COM.
    + apply CLO.
    + apply LE.
Qed.

Lemma pcpn7_mon: monotone7 pcpn7.
Proof.
  red; intros. eapply paco7_mon. apply IN.
  intros. eapply dcpn7_mon. apply PR. apply LE.
Qed.

Lemma ucpn7_mon: monotone7 ucpn7.
Proof.
  red; intros. eapply upaco7_mon. apply IN.
  intros. eapply dcpn7_mon. apply PR. apply LE.
Qed.

Lemma dcpn7_greatest: forall clo (COM: dcompatible7 clo), clo <8= dcpn7.
Proof. intros. econstructor;[apply COM|apply PR]. Qed.

Lemma dcpn7_compat: dcompatible7 dcpn7.
Proof.
  econstructor; [apply dcpn7_mon| |]; intros.
  - destruct PR; eapply gf_mon with (r:=clo r).
    + eapply (dcompat7_compat COM); apply CLO.
    + intros. econstructor; [apply COM|apply PR].
  - destruct PR.
    eapply (dcompat7_distr COM) in CLO.
    destruct CLO.
    + left. eapply dcpn7_greatest. apply COM. apply H.
    + right. eapply dcpn7_greatest. apply COM. apply H.
Qed.

Lemma dcpn7_base: forall r, r <7= dcpn7 r.
Proof.
  exists id; [|apply PR].
  econstructor; repeat intro.
  + apply LE, IN.
  + apply PR0.
  + destruct PR0.
    * left. apply H.
    * right. apply H.
Qed.

Lemma ucpn7_base: forall r, r <7= ucpn7 r.
Proof.
  right. apply dcpn7_base. apply PR.
Qed.

Lemma ucpn7_from_dcpn7_upaco r:
  dcpn7 (upaco7 gf r) <7= ucpn7 r.
Proof.
  intros.
  eapply (dcompat7_distr dcpn7_compat) in PR.
  destruct PR as [IN|IN]; cycle 1.
  - right. apply IN.
  - left. revert x0 x1 x2 x3 x4 x5 x6 IN.
    pcofix CIH. intros.
    pstep. eapply gf_mon.
    + apply (dcompat7_compat dcpn7_compat).
      eapply dcpn7_mon. apply IN.
      intros. _punfold PR. apply PR. apply gf_mon.
    + intros. apply (dcompat7_distr dcpn7_compat) in PR.
      right. destruct PR.
      * apply CIH. apply H.
      * apply CIH0. apply H.
Qed.

Lemma dcpn7_dcpn: forall r,
    dcpn7 (dcpn7 r) <7= dcpn7 r.
Proof.
  intros. exists (compose dcpn7 dcpn7); [|apply PR].
  econstructor.
  - repeat intro. eapply dcpn7_mon; [apply IN|].
    intros. eapply dcpn7_mon; [apply PR0|apply LE].
  - intros. eapply (dcompat7_compat dcpn7_compat).
    eapply dcpn7_mon; [apply PR0|].
    intros. eapply (dcompat7_compat dcpn7_compat), PR1.
  - intros. eapply (dcompat7_distr dcpn7_compat).
    eapply dcpn7_mon, (dcompat7_distr dcpn7_compat).
    apply PR0.
Qed.

Lemma ucpn7_ucpn: forall r,
    ucpn7 (ucpn7 r) <7= ucpn7 r.
Proof.
  intros. destruct PR.
  - left. eapply paco7_mult_strong.
    eapply paco7_mon. apply H.
    intros. apply ucpn7_from_dcpn7_upaco in PR.
    eapply upaco7_mon. apply PR.
    intros. apply dcpn7_dcpn. apply PR0.
  - red. apply ucpn7_from_dcpn7_upaco in H.
    eapply upaco7_mon. apply H.
    intros. apply dcpn7_dcpn. apply PR.
Qed.

Lemma ucpn7_compat r: ucpn7 (gf r) <7= gf (ucpn7 r).
Proof.
  intros. destruct PR; cycle 1.
  - apply dcpn7_compat in H.
    eapply gf_mon. apply H.
    intros. right. apply PR.
  - _punfold H; [|apply gf_mon]. eapply gf_mon. apply H.
    intros. apply ucpn7_ucpn.
    eapply upaco7_mon. apply PR.
    intros. eapply dcpn7_mon. apply PR0.
    intros. left. pstep. eapply gf_mon. apply PR1.
    intros. apply ucpn7_base. apply PR2.
Qed.

Lemma ucpn7_init:
  ucpn7 bot7 <7= paco7 gf bot7.
Proof.
  pcofix CIH. intros.
  destruct PR; cycle 1.
  - eapply paco7_mon_bot; [| intros; apply PR].
    eapply paco7_algebra, H. apply gf_mon. intros.
    eapply (dcompat7_compat dcpn7_compat).
    eapply dcpn7_mon. apply PR. contradiction.
  - _punfold H; [|apply gf_mon]. pstep.
    eapply gf_mon. apply H. intros.
    right. apply CIH. apply PR.
Qed.

Lemma pcpn7_final r:
  paco7 gf r <7= pcpn7 r.
Proof.
  intros. eapply paco7_mon. apply PR.
  intros. apply dcpn7_base. apply PR0.
Qed.

Lemma ucpn7_final r:
  upaco7 gf r <7= ucpn7 r.
Proof.
  intros. eapply upaco7_mon. apply PR.
  intros. apply dcpn7_base. apply PR0.
Qed.

Lemma ucpn7_clo
      r clo (LE: clo <8= ucpn7):
  clo (ucpn7 r) <7= ucpn7 r.
Proof.
  intros. apply ucpn7_ucpn, LE, PR.
Qed.

Lemma pcpn7_clo
      r clo (LE: clo <8= ucpn7):
  clo (pcpn7 r) <7= pcpn7 r.
Proof.
  intros. pstep. eapply gf_mon, ucpn7_ucpn.
  apply ucpn7_compat. apply LE in PR.
  eapply ucpn7_mon. apply PR.
  intros. _punfold PR0. apply PR0. apply gf_mon.
Qed.

Lemma pcpn7_unfold r:
  pcpn7 r <7= gf (ucpn7 r).
Proof.
  intros. _punfold PR. apply PR. apply gf_mon.
Qed.

Lemma ucpn7_unfold:
  ucpn7 bot7 <7= gf(ucpn7 bot7).
Proof.
  intros. apply pcpn7_unfold, pcpn7_final, ucpn7_init, PR.
Qed.

Lemma pcpn7_step r:
  gf (ucpn7 r) <7= pcpn7 r.
Proof.
  intros. pstep. apply PR.
Qed.

Lemma ucpn7_step r:
  gf (ucpn7 r) <7= ucpn7 r.
Proof.
  left. apply pcpn7_step. apply PR.
Qed.

Lemma ucpn7_id r : ucpn7 r <7= ucpn7 r.
Proof. intros. apply PR. Qed.

Lemma pcpn7_id r : pcpn7 r <7= pcpn7 r.
Proof. intros. apply PR. Qed.

Lemma gf_dcpn7_mon: monotone7 (compose gf dcpn7).
Proof.
  repeat intro. eapply gf_mon. apply IN.
  intros. eapply dcpn7_mon. apply PR. apply LE.  
Qed.

Lemma pcpn7_from_paco r: paco7 (compose gf dcpn7) r <7= pcpn7 r.
Proof.
  intros. apply dcpn7_base in PR. revert x0 x1 x2 x3 x4 x5 x6 PR.
  pcofix CIH. intros.
  pstep.
  eapply gf_mon; cycle 1.
  { instantiate (1:= _ \7/ _). right.
    destruct PR0; [apply CIH, H | apply CIH0, H]. }
  eapply gf_mon, (dcompat7_distr dcpn7_compat).
  eapply gf_mon, dcpn7_dcpn.
  eapply (dcompat7_compat dcpn7_compat).
  eapply dcpn7_mon. apply PR.
  intros. _punfold PR0. apply PR0. apply gf_dcpn7_mon.
Qed.

Lemma pcpn7_to_paco r: pcpn7 r <7= paco7 (compose gf dcpn7) r.
Proof.
  pcofix CIH. intros.
  pstep. _punfold PR; [|apply gf_mon].
  eapply gf_mon. apply PR. intros.
  destruct PR0; cycle 1.
  - eapply dcpn7_mon. apply H. intros.
    right. apply CIH0, PR0. 
  - apply dcpn7_base. right. apply CIH, H.
Qed.

Lemma pcpn7_cofix
    r l (OBG: forall rr (INC: r <7= rr) (CIH: l <7= rr), l <7= pcpn7 rr):
  l <7= pcpn7 r.
Proof.
  under_forall ltac:(apply pcpn7_from_paco).
  pcofix CIH. intros. apply pcpn7_to_paco.
  apply OBG. apply CIH0. apply CIH. apply PR.
Qed.

(**
  Recursive Closure & Weak Compatibility
*)

Inductive rclo7 (clo: rel->rel) (r: rel): rel :=
| rclo7_base
    x0 x1 x2 x3 x4 x5 x6
    (R: r x0 x1 x2 x3 x4 x5 x6):
    @rclo7 clo r x0 x1 x2 x3 x4 x5 x6
| rclo7_clo'
    r' x0 x1 x2 x3 x4 x5 x6
    (R': r' <7= rclo7 clo r)
    (CLOR': clo r' x0 x1 x2 x3 x4 x5 x6):
    @rclo7 clo r x0 x1 x2 x3 x4 x5 x6
| rclo7_dcpn'
    r' x0 x1 x2 x3 x4 x5 x6
    (R': r' <7= rclo7 clo r)
    (CLOR': @dcpn7 r' x0 x1 x2 x3 x4 x5 x6):
    @rclo7 clo r x0 x1 x2 x3 x4 x5 x6
.

Structure wdcompatible7 (clo: rel -> rel) : Prop :=
  wdcompat7_intro {
      wdcompat7_mon: monotone7 clo;
      wdcompat7_wcompat: forall r,
          clo (gf r) <7= gf (rclo7 clo r);
      wdcompat7_distr : forall r1 r2,
          clo (r1 \7/ r2) <7= (clo r1 \7/ clo r2);
    }.

Lemma rclo7_mon_gen clo clo' r r' x0 x1 x2 x3 x4 x5 x6
      (IN: @rclo7 clo r x0 x1 x2 x3 x4 x5 x6)
      (LEclo: clo <8= clo')
      (LEr: r <7= r') :
  @rclo7 clo' r' x0 x1 x2 x3 x4 x5 x6.
Proof.
  induction IN; intros.
  - econstructor 1. apply LEr, R.
  - econstructor 2; [intros; eapply H, PR|apply LEclo, CLOR'].
  - econstructor 3; [intros; eapply H, PR|].
    eapply dcpn7_mon; [apply CLOR'|].
    intros. apply PR.
Qed.

Lemma rclo7_mon clo:
  monotone7 (rclo7 clo).
Proof.
  repeat intro. eapply rclo7_mon_gen; [apply IN|intros; apply PR|apply LE].
Qed.

Lemma rclo7_clo clo r:
  clo (rclo7 clo r) <7= rclo7 clo r.
Proof.
  intros. econstructor 2; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo7_dcpn clo r:
  dcpn7 (rclo7 clo r) <7= rclo7 clo r.
Proof.
  intros. econstructor 3; [|apply PR]. 
  intros. apply PR0.
Qed.

Lemma rclo7_mult clo r:
  rclo7 clo (rclo7 clo r) <7= rclo7 clo r.
Proof.
  intros. induction PR.
  - apply R.
  - econstructor 2; [eapply H | eapply CLOR'].
  - econstructor 3; [eapply H | eapply CLOR'].
Qed.

Lemma rclo7_compose clo r:
  rclo7 (rclo7 clo) r <7= rclo7 clo r.
Proof.
  intros. induction PR.
  - apply rclo7_base, R.
  - apply rclo7_mult.
    eapply rclo7_mon; [apply CLOR'|apply H].
  - apply rclo7_dcpn.
    eapply dcpn7_mon; [apply CLOR'|apply H].
Qed.

Lemma wdcompat7_dcompat
      clo (WCOM: wdcompatible7 clo):
  dcompatible7 (rclo7 clo).
Proof.
  econstructor; [eapply rclo7_mon| |]; intros.
  - induction PR; intros.
    + eapply gf_mon; [apply R|]. intros.
      apply rclo7_base. apply PR.
    + eapply gf_mon.
      * eapply (wdcompat7_wcompat WCOM).
        eapply (wdcompat7_mon WCOM); [apply CLOR'|apply H].
      * intros. apply rclo7_mult, PR.
    + eapply gf_mon; [|intros; apply rclo7_dcpn, PR].
      eapply (dcompat7_compat dcpn7_compat).
      eapply dcpn7_mon; [apply CLOR'|apply H].
  - induction PR; intros.
    + destruct R as [R|R]; [left | right]; econstructor; apply R.
    + assert (CLOR:= wdcompat7_mon WCOM _ _ _ CLOR' H).
      eapply (wdcompat7_distr WCOM) in CLOR.
      destruct CLOR as [CLOR|CLOR]; [left|right]; apply rclo7_clo, CLOR.
    + assert (CLOR:= dcpn7_mon _ CLOR' H).
      eapply (dcompat7_distr dcpn7_compat) in CLOR.
      destruct CLOR as [CLOR|CLOR]; [left|right]; apply rclo7_dcpn, CLOR.
Qed.

Lemma wcompat7_sound clo (WCOM: wdcompatible7 clo):
  clo <8= dcpn7.
Proof.
  intros. exists (rclo7 clo).
  - apply wdcompat7_dcompat, WCOM.
  - apply rclo7_clo.
    eapply (wdcompat7_mon WCOM); [apply PR|].
    intros. apply rclo7_base, PR0.
Qed.

End PacoCompanion7_main.

Lemma pcpn7_mon_bot (gf gf': rel -> rel) x0 x1 x2 x3 x4 x5 x6 r
      (IN: @pcpn7 gf bot7 x0 x1 x2 x3 x4 x5 x6)
      (MON: monotone7 gf)
      (LE: gf <8= gf'):
  @pcpn7 gf' r x0 x1 x2 x3 x4 x5 x6.
Proof.
  eapply paco7_mon_bot, LE.
  apply ucpn7_init. apply MON. left. apply IN.
Qed.

Lemma ucpn7_mon_bot (gf gf': rel -> rel) x0 x1 x2 x3 x4 x5 x6 r
      (IN: @ucpn7 gf bot7 x0 x1 x2 x3 x4 x5 x6)
      (MON: monotone7 gf)
      (LE: gf <8= gf'):
  @ucpn7 gf' r x0 x1 x2 x3 x4 x5 x6.
Proof.
  eapply upaco7_mon_bot, LE.
  left. apply ucpn7_init. apply MON. apply IN.
Qed.

End PacoCompanion7.

Hint Resolve ucpn7_base : paco.
Hint Resolve pcpn7_step : paco.
Hint Resolve ucpn7_step : paco.

Hint Constructors rclo7 : rclo.
Hint Resolve rclo7_clo rclo7_dcpn : rclo.
