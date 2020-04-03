From Coq Require Import Program.Basics. Local Open Scope program_scope. 
From Paco Require Export paconotation.
From Paco Require Import paco_sigma paco_internal.
Set Implicit Arguments.
Set Primitive Projections.

Lemma pcofix {T0} (gf : (T0 -> Prop) -> (T0 -> Prop)) (r0 : T0 -> Prop) {A} (f : A -> T0)
  : (forall (r : _ -> Prop),
      (forall y, r0 y -> r y) ->
      (forall x, r (f x)) ->
      forall x, paco gf r (f x)) ->
    forall x, paco gf r0 (f x).
Proof.
  intros H x. eapply paco_acc with (l := fun y => exists x, f x = y).
  - intros rr Hr0 Hrr _ [x' []]. apply H; eauto.
  - eauto.
Qed.

(* Simple variant of [cofix] with goals with one variable and one hypothesis *)
Ltac pcofix_ CIH :=
  let CIH1 := fresh CIH in
  let CIH' := fresh CIH in
  apply paco_sigT_curry;
  apply pcofix; intros r0 Hr0 CIH';
  assert (CIH1 := paco_sigT_curry (U := fun x _ => r0 x) CIH');
  clear CIH'; cbn in CIH1;
  apply (paco_sigT_uncurry_ (U := fun x _ => _ x)).

(* Apply monotonicity lemma [MON : monotonic F] to a goal:
[[
  H : F r x |- F r' x
]]
   And clears out [x] if it is no longer used.
 *)
Ltac monotonic MON H :=
  match goal with
  | [ |- _ ?x ] => revert H; try (revert x); apply MON
  end.

Section GeneralizedPaco.

Variable T0 : Type.

Local Notation rel := (rel1 T0).

Section RClo.

Inductive rclo (clo: rel->rel) (r: rel) (x0 : T0) : Prop :=
| rclo_base
    (IN: r x0):
    @rclo clo r x0
| rclo_clo'
    r'
    (LE: r' <1= rclo clo r)
    (IN: clo r' x0):
    @rclo clo r x0
.

Lemma rclo_mon_gen clo clo' r r'
      (LEclo: clo <2= clo')
      (LEr: r <1= r') :
  rclo clo r <1= @rclo clo' r'.
Proof.
  intros x IN; induction IN; intros.
  - econstructor 1. apply LEr, IN.
  - econstructor 2; [intros; eapply H, PR|apply LEclo, IN].
Qed.

Lemma rclo_mon clo : monotone (rclo clo).
Proof.
  repeat intro. eapply rclo_mon_gen; eassumption + eauto.
Qed.

Lemma rclo_clo clo r:
  clo (rclo clo r) <1= rclo clo r.
Proof.
  intros. econstructor 2; [exact (fun _ H => H) | apply PR]. 
Qed.

Lemma rclo_rclo clo r:
  rclo clo (rclo clo r) <1= rclo clo r.
Proof.
  intros. induction PR.
  - eapply IN.
  - econstructor 2; [eapply H | eapply IN].
Qed.

Lemma rclo_compose clo r:
  rclo (rclo clo) r <1= rclo clo r.
Proof.
  intros. induction PR.
  - apply rclo_base, IN.
  - apply rclo_rclo. monotonic rclo_mon IN. apply H.
Qed.

End RClo.  

Section Main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone gf.

Variant gpaco clo r rg x0 : Prop :=
| gpaco_intro (IN: @rclo clo (paco (compose gf (rclo clo)) (rg \1/ r) \1/ r) x0)
.

Definition gupaco clo r := gpaco clo r r.

Lemma monotone_compose gf' :
  monotone gf ->
  monotone gf' ->
  monotone (compose gf gf').
Proof.
  intros H H' x0 r Hr. apply H, H', Hr.
Qed.

Lemma gpaco_def_mon clo : monotone (compose gf (rclo clo)).
Proof.
  eapply monotone_compose. apply gf_mon. apply rclo_mon.
Qed.

Hint Resolve gpaco_def_mon : paco.

Lemma gpaco_mon clo r r' rg rg'
      (LEr: r <1= r')
      (LErg: rg <1= rg'):
  @gpaco clo r rg <1= @gpaco clo r' rg'.
Proof.
  intros x0 IN; destruct IN. constructor.
  monotonic rclo_mon IN.
  intros. destruct PR; [|right; apply LEr, H].
  left. monotonic paco_mon H.
  intros. destruct PR; [left|right]; auto.
Qed.

Lemma gupaco_mon clo r r'
      (LEr: r <1= r'):
  @gupaco clo r <1= @gupaco clo r'.
Proof.
  apply gpaco_mon; apply LEr.
Qed.

Lemma gpaco_base clo r rg: r <1= gpaco clo r rg.
Proof.
  econstructor. apply rclo_base. right. apply PR.
Qed.

Lemma gpaco_gen_guard  clo r rg:
  gpaco clo r (rg \1/ r) <1= gpaco clo r rg.
Proof.
  intros. destruct PR. econstructor.
  monotonic rclo_mon IN.
  intros.
  destruct PR; [|right; apply H].
  left. monotonic paco_mon_gen H. trivial.
  destruct 1; auto.
Qed.

Lemma gpaco_rclo clo r rg:
  rclo clo r <1= gpaco clo r rg.
Proof.
  intros. econstructor.
  monotonic rclo_mon PR.
  right; assumption.
Qed.

Lemma gpaco_clo clo r rg:
  clo r <1= gpaco clo r rg.
Proof.
  intros. apply gpaco_rclo. eapply rclo_clo', PR.
  apply rclo_base.
Qed.

Lemma gpaco_gen_rclo clo r rg:
  gpaco (rclo clo) r rg <1= gpaco clo r rg.
Proof.
  intros. destruct PR. econstructor.
  apply rclo_compose.
  monotonic rclo_mon IN.
  destruct 1; [|right; apply H].
  left. monotonic paco_mon_gen H.
  - intro; eapply gf_mon, rclo_compose.
  - trivial.
Qed.

Lemma gpaco_step_gen clo r rg:
  gf (gpaco clo (rg \1/ r) (rg \1/ r)) <1= gpaco clo r rg.
Proof.
  intros. econstructor. apply rclo_base. left.
  apply paco_fold. monotonic gf_mon PR.
  destruct 1. monotonic rclo_mon IN.
  destruct 1.
  - left. revert H; apply paco_mon. destruct 1; trivial.
  - right. trivial.
Qed.

Lemma gpaco_step clo r rg:
  gf (gpaco clo rg rg) <1= gpaco clo r rg.
Proof.
  intros. apply gpaco_step_gen.
  revert PR; apply gf_mon, gpaco_mon; auto.
Qed.

Lemma gpaco_final clo r rg:
  (r \1/ paco gf rg) <1= gpaco clo r rg.
Proof.
  intros. destruct PR. apply gpaco_base, H.
  econstructor. apply rclo_base.
  left. monotonic paco_mon_gen H.
  - intros. monotonic gf_mon PR; apply rclo_base.
  - auto.
Qed.

Lemma gpaco_unfold clo r rg:
  gpaco clo r rg <1= rclo clo (gf (gupaco clo (rg \1/ r)) \1/ r).
Proof.
  intros. destruct PR.
  monotonic rclo_mon IN.
  intros. destruct PR; cycle 1. right; apply H.
  left. apply paco_unfold in H; [|apply gpaco_def_mon].
  monotonic gf_mon H.
  intros. econstructor.
  monotonic rclo_mon PR.
  destruct 1 as [H|H]; [| right; apply H].
  left. monotonic paco_mon H.
  auto.
Qed.

Lemma gpaco_cofix clo r rg 
      l (OBG: forall rr (INC: rg <1= rr) (CIH: l <1= rr), l <1= gpaco clo r rr):
  l <1= gpaco clo r rg.
Proof.
  assert (IN: l <1= gpaco clo r (rg \1/ l)).
  { intros. apply OBG; [left; apply PR0 | right; apply PR0 | apply PR]. }
  clear OBG. intros. apply IN in PR.
  destruct PR. constructor.
  monotonic rclo_mon IN0.
  intros x0 H; destruct H as [H|H]; [left|right; apply H].
  revert x0 H. pcofix_ CIH.
  intros x SIM; apply paco_unfold in SIM; [..| apply gpaco_def_mon].
  apply paco_fold.
  monotonic gf_mon SIM. intros x PR.
  apply rclo_rclo. monotonic rclo_mon PR.
  destruct 1 as [H|H].
  - apply rclo_base. right. apply CIH, H. 
  - destruct H as [[] | ].
    + apply rclo_base. right. apply Hr0. left. apply H.
    + apply IN in H. destruct H.
      monotonic rclo_mon IN0.
      destruct 1.
      * right. apply CIH. apply H.      
      * right. apply Hr0. right. apply H.
    + apply rclo_base. right. apply Hr0. right. apply H.
Qed.

Lemma gpaco_gupaco clo r rg:
  gupaco clo (gpaco clo r rg) <1= gpaco clo r rg.
Proof.
  eapply gpaco_cofix.
  intros; destruct PR. econstructor.
  apply rclo_rclo. monotonic rclo_mon IN.
  intros. destruct PR.
  - apply rclo_base. left.
    monotonic paco_mon H.
    intros. left; apply CIH.
    econstructor. apply rclo_base. right.
    destruct PR; apply H.
  - destruct H. monotonic rclo_mon IN.
    intros. destruct PR; [| right; apply H].
    left. monotonic paco_mon H.
    intros. destruct PR as [H|H].
    + left. apply INC, H.
    + right. apply H.
Qed.

Lemma gpaco_gpaco clo r rg:
  gpaco clo (gpaco clo r rg) (gupaco clo (rg \1/ r)) <1= gpaco clo r rg.
Proof.
  intros. apply gpaco_unfold in PR.
  econstructor. apply rclo_rclo. eapply rclo_mon; [| apply PR]. clear x0 PR. intros.
  destruct PR; [|destruct H; apply IN].
  apply rclo_base. left. apply paco_fold.
  monotonic gf_mon H. intros.
  enough (@gupaco clo (rg \1/ r) x0).
  { destruct H. monotonic rclo_mon IN.
    destruct 1; [|right; apply H].
    left. monotonic paco_mon H. destruct 1 as [H|H]; apply H.
  }
  apply gpaco_gupaco. monotonic gupaco_mon PR.
  destruct 1; [apply H|].
  monotonic gpaco_mon H; [right|left]; apply PR.
Qed.

Lemma gpaco_uclo uclo clo r rg 
      (LEclo: uclo <2= gupaco clo) :
  uclo (gpaco clo r rg) <1= gpaco clo r rg.
Proof.
  intros. apply gpaco_gupaco. apply LEclo, PR.
Qed.

Lemma gpaco_weaken  clo r rg:
  gpaco (gupaco clo) r rg <1= gpaco clo r rg.
Proof.
  intros. apply gpaco_unfold in PR.
  induction PR.
  - destruct IN; cycle 1. apply gpaco_base, H.
    apply gpaco_step_gen. monotonic gf_mon H.
    eapply gpaco_cofix. intros.
    apply gpaco_unfold in PR.
    induction PR.
    + destruct IN; [| apply gpaco_base, H].
      apply gpaco_step. monotonic gf_mon H.
      intros. apply gpaco_base. apply CIH.
      monotonic gupaco_mon PR.
      destruct 1 as [H|H]; apply H.
    + apply gpaco_gupaco.
      monotonic gupaco_mon IN. apply H.
  - apply gpaco_gupaco.
    monotonic gupaco_mon IN. apply H.
Qed.

End Main.

Hint Resolve gpaco_def_mon : paco.

Section GeneralMonotonicity.

Variable gf: rel -> rel.
  
Lemma gpaco_mon_gen (gf' clo clo': rel -> rel) r r' rg rg'
      (gf_mon: monotone gf)
      (LEgf: gf <2= gf')
      (LEclo: clo <2= clo')
      (LEr: r <1= r')
      (LErg: rg <1= rg') :
  @gpaco gf clo r rg <1= @gpaco gf' clo' r' rg'.
Proof.
  intros x0 IN. eapply gpaco_mon; [apply LEr|apply LErg| ].
  destruct IN. econstructor.
  monotonic rclo_mon_gen IN. apply LEclo.
  destruct 1 as [H|H]; [left|right; apply H].
  monotonic paco_mon_gen H.
  - intros. eapply LEgf.
    monotonic gf_mon PR.
    intros. monotonic rclo_mon_gen PR. apply LEclo. trivial.
  - trivial.
Qed.

Lemma gpaco_mon_bot (gf' clo clo': rel -> rel) r' rg'
      (gf_mon: monotone gf)
      (LEgf: gf <2= gf')
      (LEclo: clo <2= clo'):
  @gpaco gf clo bot1 bot1 <1= @gpaco gf' clo' r' rg'.
Proof.
  apply gpaco_mon_gen; assumption + contradiction.
Qed.

Lemma gupaco_mon_gen (gf' clo clo': rel -> rel) r r'
      (gf_mon: monotone gf)
      (LEgf: gf <2= gf')
      (LEclo: clo <2= clo')
      (LEr: r <1= r'):
  @gupaco gf clo r <1= @gupaco gf' clo' r'.
Proof.
  apply gpaco_mon_gen; assumption.
Qed.

End GeneralMonotonicity.

Section Compatibility.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone gf.

Structure compatible (clo: rel -> rel) : Prop :=
  compat_intro {
      compat_mon: monotone clo;
      compat_compat : forall r,
          clo (gf r) <1= gf (clo r);
    }.

Structure wcompatible clo : Prop :=
  wcompat_intro {
      wcompat_mon: monotone clo;
      wcompat_wcompat : forall r,
          clo (gf r) <1= gf (gupaco gf clo r);
    }.

Lemma rclo_dist clo
      (MON: monotone clo)
      (DIST: forall r1 r2, clo (r1 \1/ r2) <1= (clo r1 \1/ clo r2)):
  forall r1 r2, rclo clo (r1 \1/ r2) <1= (rclo clo r1 \1/ rclo clo r2).
Proof.
  intros. induction PR.
  + destruct IN; [left|right]; apply rclo_base, H.
  + assert (REL: clo (rclo clo r1 \1/ rclo clo r2) x0).
    { monotonic MON IN. apply H. }
    apply DIST in REL. destruct REL; [left|right]; apply rclo_clo, H0.
Qed.

Lemma rclo_compat clo
      (COM: compatible clo):
  compatible (rclo clo).
Proof.
  econstructor.
  - apply rclo_mon.
  - intros. induction PR.
    + monotonic gf_mon IN.
      intros. eapply rclo_base. apply PR.
    + eapply gf_mon.
      * intros. eapply rclo_clo. apply PR.
      * eapply COM. eapply COM. apply H. apply IN.
Qed.

Lemma rclo_wcompat clo
      (COM: wcompatible clo):
  wcompatible (rclo clo).
Proof.
  econstructor.
  - apply rclo_mon.
  - intros. induction PR.
    + monotonic gf_mon IN.
      intros. apply gpaco_base. apply PR.
    + eapply gf_mon.
      * intros. eapply gpaco_gupaco. apply gf_mon.
        monotonic gupaco_mon_gen PR; [apply gf_mon|trivial| |eauto].
        intros ? ?; eapply rclo_clo'. apply rclo_base.
      * eapply COM. eapply COM. apply H. apply IN.
Qed.

Lemma compat_wcompat clo
      (CMP: compatible clo):
  wcompatible clo.
Proof.
  econstructor. apply CMP.
  intros. apply CMP in PR.
  monotonic gf_mon PR.
  intros. apply gpaco_clo, PR.
Qed.

Lemma wcompat_compat clo
      (WCMP: wcompatible clo) :
  compatible (gupaco gf clo).
Proof.
  econstructor.
  { red; red; intros. monotonic gpaco_mon PR; apply LE. }

  intros. apply gpaco_unfold in PR; [|apply gf_mon].
  induction PR.
  - destruct IN; cycle 1.
    + monotonic gf_mon H.
      intros. apply gpaco_base, PR.
    + monotonic gf_mon H.
      intros. apply gpaco_gupaco. apply gf_mon.
      monotonic gupaco_mon PR.
      intros. apply gpaco_step. apply gf_mon.
      apply (or_ind (fun x => x) (fun x => x)) in PR.
      monotonic gf_mon PR.
      apply gpaco_base.
  - eapply gf_mon; [ eapply gpaco_gupaco, gf_mon | ].
    apply WCMP. eapply WCMP. apply H. apply IN.
Qed.

Lemma wcompat_union clo1 clo2
      (WCMP1: wcompatible clo1)
      (WCMP2: wcompatible clo2):
  wcompatible (clo1 \2/ clo2).
Proof.
  econstructor.
  - apply monotone_union. apply WCMP1. apply WCMP2.
  - intros. destruct PR.
    + apply WCMP1 in H. monotonic gf_mon H.
      intros. monotonic gupaco_mon_gen PR; auto.
    + apply WCMP2 in H. monotonic gf_mon H.
      intros. monotonic gupaco_mon_gen PR; auto.
Qed.

End Compatibility.

Section Soundness.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone gf.

Lemma gpaco_compat_init clo
      (CMP: compatible gf clo):
  gpaco gf clo bot1 bot1 <1= paco gf bot1.
Proof.
  intros. destruct PR. revert x0 IN.
  pcofix_ CIH. intros x H. apply paco_fold.
  eapply gf_mon; [right; apply CIH, rclo_rclo, PR |].
  apply compat_compat with (gf:=gf). apply rclo_compat. apply gf_mon. apply CMP.
  monotonic rclo_mon H.
  intros. destruct PR; [|contradiction]. apply paco_unfold in H; [..|apply gpaco_def_mon, gf_mon].
  monotonic gpaco_def_mon H; [ apply gf_mon| ].
  intros. destruct PR; [left; apply H|destruct H; contradiction].
Qed.

Lemma gpaco_init clo
      (WCMP: wcompatible gf clo):
  gpaco gf clo bot1 bot1 <1= paco gf bot1.
Proof.
  intros. eapply gpaco_compat_init.
  - apply wcompat_compat, WCMP. apply gf_mon.
  - monotonic gpaco_mon_bot PR. apply gf_mon. intros; apply PR.
    intros. apply gpaco_clo, PR.
Qed.

Lemma gpaco_unfold_bot clo
      (WCMP: wcompatible gf clo):
  gpaco gf clo bot1 bot1 <1= gf (gpaco gf clo bot1 bot1).
Proof.
  intros. apply gpaco_init in PR; [|apply WCMP].
  apply paco_unfold in PR; [..|apply gf_mon].
  monotonic gf_mon PR.
  intros. destruct PR; [|contradiction]. apply gpaco_final; auto.
Qed.

End Soundness.

Section Distributivity.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone gf.

Lemma gpaco_dist clo r rg
      (CMP: wcompatible gf clo)
      (DIST: forall r1 r2, clo (r1 \1/ r2) <1= (clo r1 \1/ clo r2)):
  gpaco gf clo r rg <1= (paco gf (rclo clo (rg \1/ r)) \1/ rclo clo r).
Proof.
  intros x PR. apply gpaco_unfold in PR; [|apply gf_mon].
  apply rclo_dist in PR; [|apply CMP|apply DIST].
  destruct PR; [|right; apply H].
  left. revert x H.
  pcofix_ CIH; intros x PR.
  apply rclo_wcompat in PR; [|apply gf_mon|apply CMP].
  apply paco_fold. monotonic gf_mon PR. intros x PR.
  apply gpaco_unfold in PR; [|apply gf_mon].
  apply rclo_compose in PR.
  apply rclo_dist in PR; [|apply CMP|apply DIST].
  destruct PR as [PR|PR].
  - right. apply CIH.
    monotonic rclo_mon PR. apply gf_mon. intros x PR.
    apply gpaco_gupaco; [apply gf_mon |].
    apply gpaco_gen_rclo; [apply gf_mon|].
    monotonic gupaco_mon PR. intros x PR.
    destruct PR as [PR|PR]; apply PR.
  - assert (REL: @rclo clo (rclo clo (gf (gupaco gf clo ((rg \1/ r) \1/ (rg \1/ r))) \1/ (rg \1/ r))) x).
    { monotonic rclo_mon PR. intros. apply gpaco_unfold in PR; assumption. }
    apply rclo_rclo in REL.
    apply rclo_dist in REL; [|apply CMP|apply DIST].
    right. destruct REL as [REL|REL]; [| apply Hr0, REL].
    apply CIH.
    monotonic rclo_mon REL. apply gf_mon, gupaco_mon.
    destruct 1 as [PR1|PR1]; apply PR1.
Qed.

Lemma gpaco_dist_reverse clo r rg:
  (paco gf (rclo clo (rg \1/ r)) \1/ rclo clo r) <1= gpaco gf clo r rg.
Proof.
  intros. destruct PR; cycle 1.
  - eapply gpaco_rclo. apply H.
  - econstructor. apply rclo_base. left.
    revert x0 H. pcofix_ CIH; intros x PR.
    apply paco_unfold in PR; [|apply gf_mon].
    apply paco_fold.
    monotonic gf_mon PR. intros x PR.
    destruct PR as [PR|PR].
    + apply rclo_base. auto.
    + monotonic rclo_mon PR. auto.
Qed.

End Distributivity.

Section Companion.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone gf.

Inductive cpn (r: rel) x0 : Prop :=
| cpn_intro
    clo
    (COM: compatible gf clo)
    (CLO: clo r x0)
.

Lemma cpn_mon: monotone cpn.
Proof.
  red; red. destruct 2. exists clo.
  - apply COM.
  - eapply compat_mon; [apply COM|apply LE|apply CLO].
Qed.

Lemma cpn_greatest: forall clo (COM: compatible gf clo), clo <2= cpn.
Proof. intros. econstructor;[apply COM|apply PR]. Qed.

Lemma cpn_compat: compatible gf cpn.
Proof.
  econstructor; [apply cpn_mon|intros].
  destruct PR; eapply gf_mon with (r:=clo r).
  - intros. econstructor; [apply COM|apply PR].
  - eapply (compat_compat COM); apply CLO.
Qed.

Lemma cpn_wcompat: wcompatible gf cpn.
Proof. apply compat_wcompat, cpn_compat. apply gf_mon. Qed.

Lemma cpn_gupaco:
  gupaco gf cpn <2= cpn.
Proof.
  intros. eapply cpn_greatest, PR. apply wcompat_compat. apply gf_mon. apply cpn_wcompat.
Qed.

Lemma cpn_cpn r:
  cpn (cpn r) <1= cpn r.
Proof.
  intros. apply cpn_gupaco, gpaco_gupaco, gpaco_clo. apply gf_mon.
  eapply cpn_mon; [ apply gpaco_clo | apply PR ].
Qed.

Lemma cpn_base r:
  r <1= cpn r.
Proof.
  intros. apply cpn_gupaco. apply gpaco_base, PR.
Qed.

Lemma cpn_clo
      r clo (LE: clo <2= cpn):
  clo (cpn r) <1= cpn r.
Proof.
  intros. apply cpn_cpn, LE, PR.
Qed.

Lemma cpn_step r:
  gf (cpn r) <1= cpn r.
Proof.
  intros. apply cpn_gupaco. apply gpaco_step. apply gf_mon.
  monotonic gf_mon PR; apply gpaco_clo.
Qed.

Lemma cpn_uclo uclo
      (MON: monotone uclo)
      (WCOM: forall r, uclo (gf r) <1= gf (gupaco gf (uclo \2/ cpn) r)):
  uclo <2= gupaco gf cpn.
Proof.
  intros. apply gpaco_clo.
  exists (gupaco gf (uclo \2/ cpn)).
  - apply wcompat_compat. apply gf_mon.
    econstructor.
    + apply monotone_union. apply MON. apply cpn_mon.
    + intros. destruct PR0.
      * apply WCOM, H.
      * apply compat_compat with (gf:=gf) in H; [| apply cpn_compat].
        monotonic gf_mon H. intros.
        apply gpaco_clo. right. apply PR0.
  - apply gpaco_clo. left. apply PR.
Qed.
