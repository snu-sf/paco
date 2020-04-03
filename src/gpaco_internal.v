From Coq Require Import Program.Basics. Local Open Scope program_scope. 
From Paco Require Export paconotation.
From Paco Require Import paco_currying paco_internal (* TODO put sigT elsewhere *).
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
  apply paco_currying.paco_sigT_curry;
  apply pcofix; intros r0 Hr0 CIH';
  assert (CIH1 := paco_currying.paco_sigT_curry (U := fun x _ => r0 x) CIH');
  clear CIH'; cbn in CIH1;
  apply (paco_currying.paco_sigT_uncurry_ (U := fun x _ => _ x)).

Section GeneralizedPaco.

Variable T0 : Type.

Local Notation rel := (rel1 T0).

Section RClo.

Inductive rclo (clo: rel->rel) (r: rel): rel :=
| rclo_base
    x0
    (IN: r x0):
    @rclo clo r x0
| rclo_clo'
    r' x0
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
  intros. econstructor 2; [|apply PR]. 
  intros. apply PR0.
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
  - apply rclo_rclo.
    eapply rclo_mon; [apply H|apply IN].
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
  intros H H' x0 r Hr.
  apply H, H', Hr.
Qed.

Lemma gpaco_def_mon clo : monotone (compose gf (rclo clo)).
Proof.
  eapply monotone_compose. apply gf_mon. apply rclo_mon.
Qed.

Hint Resolve gpaco_def_mon : paco.

Lemma gpaco_mon clo r r' rg rg' x0
      (IN: @gpaco clo r rg x0)
      (LEr: r <1= r')
      (LErg: rg <1= rg'):
  @gpaco clo r' rg' x0.
Proof.
  destruct IN. econstructor.
  eapply rclo_mon; [ | apply IN ].
  intros. destruct PR; [|right; apply LEr, H].
  left. eapply paco_mon; [ | apply H].
  intros. destruct PR.
  - left. apply LErg, H0.
  - right. apply LEr, H0.
Qed.

Lemma gupaco_mon clo r r' x0
      (IN: @gupaco clo r x0)
      (LEr: r <1= r'):
  @gupaco clo r' x0.
Proof.
  eapply gpaco_mon. apply IN. apply LEr. apply LEr.
Qed.

Lemma gpaco_base clo r rg: r <1= gpaco clo r rg.
Proof.
  econstructor. apply rclo_base. right. apply PR.
Qed.

Lemma gpaco_gen_guard  clo r rg:
  gpaco clo r (rg \1/ r) <1= gpaco clo r rg.
Proof.
  intros. destruct PR. econstructor.
  eapply rclo_mon; [ | apply IN ]. intros.
  destruct PR; [|right; apply H].
  left. eapply paco_mon_gen; intros; [.. | apply H]. apply PR.
  destruct PR. apply H0. right. apply H0.
Qed.

Lemma gpaco_rclo clo r rg:
  rclo clo r <1= gpaco clo r rg.
Proof.
  intros. econstructor.
  eapply rclo_mon; [ | apply PR ].
  intros. right. apply PR0.
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
  eapply rclo_mon; [ | apply IN ]. intros.
  destruct PR; [|right; apply H].
  left. eapply paco_mon_gen; [ | intros; apply PR | apply H].
  intros r'; eapply gf_mon, rclo_compose.
Qed.

Lemma gpaco_step_gen clo r rg:
  gf (gpaco clo (rg \1/ r) (rg \1/ r)) <1= gpaco clo r rg.
Proof.
  intros. econstructor. apply rclo_base. left.
  apply paco_fold. eapply gf_mon; [ | apply PR].
  intros. destruct PR0. eapply rclo_mon; [ | apply IN].
  intros. destruct PR0.
  - left. eapply paco_mon; [ | apply H]. intros. destruct PR0; apply H0.
  - right. apply H.
Qed.

Lemma gpaco_step clo r rg:
  gf (gpaco clo rg rg) <1= gpaco clo r rg.
Proof.
  intros. apply gpaco_step_gen.
  eapply gf_mon; [ | apply PR ]. intros.
  eapply gpaco_mon. apply PR0. left; apply PR1. left; apply PR1.
Qed.

Lemma gpaco_final clo r rg:
  (r \1/ paco gf rg) <1= gpaco clo r rg.
Proof.
  intros. destruct PR. apply gpaco_base, H.
  econstructor. apply rclo_base.
  left. eapply paco_mon_gen; [ | | apply H].
  - intros. eapply gf_mon; [ | apply PR].
    intros. apply rclo_base. apply PR0.
  - intros. left. apply PR.
Qed.

Lemma gpaco_unfold clo r rg:
  gpaco clo r rg <1= rclo clo (gf (gupaco clo (rg \1/ r)) \1/ r).
Proof.
  intros. destruct PR.
  eapply rclo_mon; [ | apply IN].
  intros. destruct PR; cycle 1. right; apply H.
  left. apply paco_unfold in H; [|apply gpaco_def_mon].
  eapply gf_mon; [| apply H].
  intros. econstructor.
  eapply rclo_mon; [| apply PR].
  intros. destruct PR0; cycle 1. right. apply H0.
  left. eapply paco_mon; [| apply H0].
  intros. left. apply PR0.
Qed.

Lemma gpaco_cofix clo r rg 
      l (OBG: forall rr (INC: rg <1= rr) (CIH: l <1= rr), l <1= gpaco clo r rr):
  l <1= gpaco clo r rg.
Proof.
  assert (IN: l <1= gpaco clo r (rg \1/ l)).
  { intros. apply OBG; [left; apply PR0 | right; apply PR0 | apply PR]. }
  clear OBG. intros. apply IN in PR.
  destruct PR. econstructor.
  eapply rclo_mon; [| apply IN0].
  clear x0 IN0.
  intros. destruct PR; [|right; apply H].
  left. revert x0 H.
  pcofix_ CIH.
  intros x SIM; apply paco_unfold in SIM; [..| apply gpaco_def_mon].
  apply paco_fold.
  eapply gf_mon; [ | apply SIM ]. intros.
  apply rclo_rclo. eapply rclo_mon; [| apply PR].
  intros. destruct PR0.
  - apply rclo_base. right. apply CIH, H. 
  - destruct H as [[] | ].
    + apply rclo_base. right. apply Hr0. left. apply H.
    + apply IN in H. destruct H.
      eapply rclo_mon; [| apply IN0].
      intros. destruct PR0.
      * right. apply CIH. apply H.      
      * right. apply Hr0. right. apply H.
    + apply rclo_base. right. apply Hr0. right. apply H.
Qed.

Lemma gpaco_gupaco clo r rg:
  gupaco clo (gpaco clo r rg) <1= gpaco clo r rg.
Proof.
  eapply gpaco_cofix.
  intros. destruct PR. econstructor.
  apply rclo_rclo. eapply rclo_mon; [| apply IN].
  intros. destruct PR.
  - apply rclo_base. left.
    eapply paco_mon; [| apply H].
    intros. left; apply CIH.
    econstructor. apply rclo_base. right.
    destruct PR; apply H0.
  - destruct H. eapply rclo_mon; [| apply IN0].
    intros. destruct PR; [| right; apply H].
    left. eapply paco_mon; [| apply H].
    intros. destruct PR.
    + left. apply INC. apply H0.
    + right. apply H0.
Qed.

Lemma gpaco_gpaco clo r rg:
  gpaco clo (gpaco clo r rg) (gupaco clo (rg \1/ r)) <1= gpaco clo r rg.
Proof.
  intros. apply gpaco_unfold in PR.
  econstructor. apply rclo_rclo. eapply rclo_mon; [| apply PR]. clear x0 PR. intros.
  destruct PR; [|destruct H; apply IN].
  apply rclo_base. left. apply paco_fold.
  eapply gf_mon; [| apply H]. clear x0 H. intros.
  cut (@gupaco clo (rg \1/ r) x0).
  { intros. destruct H. eapply rclo_mon; [| apply IN]. intros.
    destruct PR0; [|right; apply H].
    left. eapply paco_mon; [| apply H]. intros. destruct PR0; apply H0.
  }
  apply gpaco_gupaco. eapply gupaco_mon. apply PR. intros.
  destruct PR0; [apply H|].
  eapply gpaco_mon; [apply H|right|left]; intros; apply PR0.
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
    apply gpaco_step_gen. eapply gf_mon; [| apply H].
    clear x0 H.
    eapply gpaco_cofix. intros.
    apply gpaco_unfold in PR.
    induction PR.
    + destruct IN; cycle 1. apply gpaco_base, H.
      apply gpaco_step. eapply gf_mon; [| apply H].
      intros. apply gpaco_base. apply CIH.
      eapply gupaco_mon. apply PR.
      intros. destruct PR0; apply H0.
    + apply gpaco_gupaco.
      eapply gupaco_mon. apply IN. apply H.
  - apply gpaco_gupaco.
    eapply gupaco_mon. apply IN. apply H.
Qed.

End Main.

Hint Resolve gpaco_def_mon : paco.

Section GeneralMonotonicity.

Variable gf: rel -> rel.
  
Lemma gpaco_mon_gen (gf' clo clo': rel -> rel) x0 r r' rg rg'
      (IN: @gpaco gf clo r rg x0)
      (gf_mon: monotone gf)
      (LEgf: gf <2= gf')
      (LEclo: clo <2= clo')
      (LEr: r <1= r')
      (LErg: rg <1= rg') :
  @gpaco gf' clo' r' rg' x0.
Proof.
  eapply gpaco_mon; [|apply LEr|apply LErg].
  destruct IN. econstructor.
  eapply rclo_mon_gen; [| | apply IN]. apply LEclo.
  intros. destruct PR; [| right; apply H].
  left. eapply paco_mon_gen; [| | apply H].
  - intros. eapply LEgf.
    eapply gf_mon; [| apply PR].
    intros. eapply rclo_mon_gen; [| | apply PR0]. apply LEclo. intros; apply PR1.
  - intros. apply PR.
Qed.

Lemma gpaco_mon_bot (gf' clo clo': rel -> rel) x0 r' rg'
      (IN: @gpaco gf clo bot1 bot1 x0)
      (gf_mon: monotone gf)
      (LEgf: gf <2= gf')
      (LEclo: clo <2= clo'):
  @gpaco gf' clo' r' rg' x0.
Proof.
  eapply gpaco_mon_gen. apply IN. apply gf_mon. apply LEgf. apply LEclo. contradiction. contradiction.
Qed.

Lemma gupaco_mon_gen (gf' clo clo': rel -> rel) x0 r r'
      (IN: @gupaco gf clo r x0)
      (gf_mon: monotone gf)
      (LEgf: gf <2= gf')
      (LEclo: clo <2= clo')
      (LEr: r <1= r'):
  @gupaco gf' clo' r' x0.
Proof.
  eapply gpaco_mon_gen. apply IN. apply gf_mon. apply LEgf. apply LEclo. apply LEr. apply LEr.
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
    { eapply MON. apply H. apply IN. }
    apply DIST in REL. destruct REL; [left|right]; apply rclo_clo, H0.
Qed.

Lemma rclo_compat clo
      (COM: compatible clo):
  compatible (rclo clo).
Proof.
  econstructor.
  - apply rclo_mon.
  - intros. induction PR.
    + eapply gf_mon; [| apply IN].
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
    + eapply gf_mon; [| apply IN].
      intros. apply gpaco_base. apply PR.
    + eapply gf_mon.
      * intros. eapply gpaco_gupaco. apply gf_mon.
        eapply gupaco_mon_gen; intros; [apply PR|apply gf_mon|apply PR0| |apply PR0].
        eapply rclo_clo'. apply rclo_base. apply PR0.
      * eapply COM. eapply COM. apply H. apply IN.
Qed.

Lemma compat_wcompat clo
      (CMP: compatible clo):
  wcompatible clo.
Proof.
  econstructor. apply CMP.
  intros. apply CMP in PR.
  eapply gf_mon; [| apply PR].
  intros. apply gpaco_clo, PR0. 
Qed.

Lemma wcompat_compat clo
      (WCMP: wcompatible clo) :
  compatible (gupaco gf clo).
Proof.
  econstructor.
  { red; red; intros. eapply gpaco_mon. apply PR. apply LE. apply LE. }

  intros. apply gpaco_unfold in PR; [|apply gf_mon].
  induction PR.
  - destruct IN; cycle 1.
    + eapply gf_mon; [| apply H].
      intros. apply gpaco_base, PR.
    + eapply gf_mon; [| apply H].
      intros. apply gpaco_gupaco. apply gf_mon.
      eapply gupaco_mon; [apply PR | ].
      intros. apply gpaco_step. apply gf_mon.
      eapply gf_mon; [| destruct PR0 as [X|X]; apply X].
      intros. apply gpaco_base, PR1.
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
    + apply WCMP1 in H. eapply gf_mon; [| apply H].
      intros. eapply gupaco_mon_gen. apply PR. apply gf_mon. 
      intros; apply PR0. left; apply PR0. intros; apply PR0.
    + apply WCMP2 in H. eapply gf_mon; [| apply H].
      intros. eapply gupaco_mon_gen; try eassumption.
      intros; apply PR0. right; apply PR0. intros; apply PR0.
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
  pcofix_ CIH. intros. apply paco_fold.
  eapply gf_mon; [right; apply CIH, rclo_rclo, PR |].
  apply compat_compat with (gf:=gf). apply rclo_compat. apply gf_mon. apply CMP.
  eapply rclo_mon; [| eassumption].
  intros. destruct PR; [|contradiction]. apply paco_unfold in H; [..|apply gpaco_def_mon, gf_mon].
  eapply gpaco_def_mon; [ apply gf_mon| | apply H].
  intros. destruct PR; [|destruct H0; contradiction]. left. apply H0.
Qed.

Lemma gpaco_init clo
      (WCMP: wcompatible gf clo):
  gpaco gf clo bot1 bot1 <1= paco gf bot1.
Proof.
  intros. eapply gpaco_compat_init.
  - apply wcompat_compat, WCMP. apply gf_mon.
  - eapply gpaco_mon_bot. apply PR. apply gf_mon. intros; apply PR0.
    intros. apply gpaco_clo, PR0.
Qed.

Lemma gpaco_unfold_bot clo
      (WCMP: wcompatible gf clo):
  gpaco gf clo bot1 bot1 <1= gf (gpaco gf clo bot1 bot1).
Proof.
  intros. apply gpaco_init in PR; [|apply WCMP].
  apply paco_unfold in PR; [..|apply gf_mon].
  eapply gf_mon; [| apply PR].
  intros. destruct PR0; [|contradiction]. apply gpaco_final. apply gf_mon. right. apply H.
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
  apply paco_fold. eapply gf_mon; [| apply PR]. intros x1 PR1.
  apply gpaco_unfold in PR1; [|apply gf_mon].
  apply rclo_compose in PR1.
  apply rclo_dist in PR1; [|apply CMP|apply DIST].
  destruct PR1 as [PR1|PR1].
  - right. apply CIH.
    eapply rclo_mon; [| apply PR1]. intros x2 PR2.
    eapply gf_mon; [| apply PR2]. intros x3 PR3.
    apply gpaco_gupaco; [apply gf_mon |].
    apply gpaco_gen_rclo; [apply gf_mon|].
    eapply gupaco_mon. apply PR3. intros x4 PR4.
    destruct PR4; apply H.
  - assert (REL: @rclo clo (rclo clo (gf (gupaco gf clo ((rg \1/ r) \1/ (rg \1/ r))) \1/ (rg \1/ r))) x1).
    { eapply rclo_mon; [| apply PR1]. intros. apply gpaco_unfold in PR0. apply PR0. apply gf_mon. }
    apply rclo_rclo in REL.
    apply rclo_dist in REL; [|apply CMP|apply DIST].
    right. destruct REL as [REL|REL]; cycle 1.
    + apply Hr0, REL.
    + apply CIH.
      eapply rclo_mon; [| apply REL]. intros x2 PR2.
      eapply gf_mon; [| apply PR2]. intros x3 PR3.
      eapply gupaco_mon; [apply PR3 |]. intros x4 PR4.
      destruct PR4 as [PR4|PR4]; apply PR4.
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
    eapply gf_mon; [| apply PR]. intros x1 PR1.
    destruct PR1 as [PR1|PR1].
    + apply rclo_base. right. apply CIH, PR1.
    + eapply rclo_mon; [| apply PR1]. intros x2 PR2.
      right. apply Hr0. apply PR2.
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
  eapply gf_mon; [apply gpaco_clo | apply PR].
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
        eapply gf_mon; [| apply H]. intros.
        apply gpaco_clo. right. apply PR0.
  - apply gpaco_clo. left. apply PR.
Qed.
