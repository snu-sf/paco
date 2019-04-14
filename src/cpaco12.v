Require Export Program.Basics. Open Scope program_scope.
Require Import paco12 pacotac cpn12.
Set Implicit Arguments.

Section CompatiblePaco12.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.
Variable T7 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5), Type.
Variable T8 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6), Type.
Variable T9 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7), Type.
Variable T10 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8), Type.
Variable T11 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4) (x6: @T6 x0 x1 x2 x3 x4 x5) (x7: @T7 x0 x1 x2 x3 x4 x5 x6) (x8: @T8 x0 x1 x2 x3 x4 x5 x6 x7) (x9: @T9 x0 x1 x2 x3 x4 x5 x6 x7 x8) (x10: @T10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9), Type.

Local Notation rel := (rel12 T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11).

Section CompatiblePaco12_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone12 gf.

Variable clo : rel -> rel.
Hypothesis clo_compat: compatible12 gf clo.

Inductive cpaco12 r rg x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Prop :=
| cpaco12_intro (IN: rclo12 clo (paco12 (compose gf (rclo12 clo)) (r \12/ rg) \12/ r) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)
.

Definition cupaco12 r := cpaco12 r r.

Lemma cpaco12_def_mon : monotone12 (compose gf (rclo12 clo)).
Proof.
  eapply monotone12_compose. apply gf_mon. apply rclo12_mon.
Qed.

Hint Resolve cpaco12_def_mon : paco.

Lemma cpaco12_mon r r' rg rg' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11
      (IN: @cpaco12 r rg x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)
      (LEr: r <12= r')
      (LErg: rg <12= rg'):
  @cpaco12 r' rg' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11.
Proof.
  destruct IN. econstructor.
  eapply rclo12_mon. apply IN.
  intros. destruct PR; [|right; apply LEr, H].
  left. eapply paco12_mon. apply H.
  intros. destruct PR.
  - left. apply LEr, H0.
  - right. apply LErg, H0.
Qed.

Lemma cpaco12_cofix r rg 
      l (OBG: forall rr (INC: rg <12= rr) (CIH: l <12= rr), l <12= cpaco12 r rr):
  l <12= cpaco12 r rg.
Proof.
  assert (IN: l <12= cpaco12 r (rg \12/ l)).
  { intros. apply OBG; [left; apply PR0 | right; apply PR0 | apply PR]. }
  clear OBG. intros. apply IN in PR.
  destruct PR. econstructor.
  eapply rclo12_mon. apply IN0.
  clear x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 IN0.
  intros. destruct PR; [|right; apply H].
  left. revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 H.
  pcofix CIH. intros.
  _punfold H0; [..|apply cpaco12_def_mon]. pstep.
  eapply gf_mon. apply H0. intros.
  apply rclo12_rclo. eapply rclo12_mon. apply PR.
  intros. destruct PR0.
  - apply rclo12_base. right. apply CIH. apply H.
  - destruct H; [|destruct H].
    + apply rclo12_base. right. apply CIH0. left. apply H.
    + apply rclo12_base. right. apply CIH0. right. apply H.
    + apply IN in H. destruct H.
      eapply rclo12_mon. apply IN0.
      intros. destruct PR0.
      * right. apply CIH. apply H.      
      * right. apply CIH0. left. apply H.
Qed.

Lemma cpaco12_cupaco r rg:
  cupaco12 (cpaco12 r rg) <12= cpaco12 r rg.
Proof.
  eapply cpaco12_cofix.
  intros. destruct PR. econstructor.
  apply rclo12_rclo. eapply rclo12_mon. apply IN.
  intros. destruct PR.
  - apply rclo12_base. left.
    eapply paco12_mon. apply H.
    intros. right; apply CIH.
    econstructor. apply rclo12_base. right.
    destruct PR as [PR|PR]; apply PR.
  - destruct H. eapply rclo12_mon. apply IN0.
    intros. destruct PR; [| right; apply H].
    left. eapply paco12_mon. apply H.
    intros. destruct PR. left; apply H0.
    right. apply INC, H0.
Qed.

Lemma cpaco12_uclo (uclo: rel -> rel) r rg 
      (LEclo: uclo <13= cupaco12) :
  uclo (cpaco12 r rg) <12= cpaco12 r rg.
Proof.
  intros. apply cpaco12_cupaco. apply LEclo, PR.
Qed.

Lemma cpaco12_base r rg: r <12= cpaco12 r rg.
Proof.
  econstructor. apply rclo12_base. right. apply PR.
Qed.

Lemma cpaco12_rclo r:
  rclo12 clo r <12= cupaco12 r.
Proof.
  intros. econstructor.
  eapply rclo12_mon. apply PR.
  intros. right. apply PR0.
Qed.

Lemma cpaco12_clo r:
  clo r <12= cupaco12 r.
Proof.
  intros. apply cpaco12_rclo. apply rclo12_clo.
  eapply clo_compat. apply PR.
  intros. apply rclo12_base. apply PR0.
Qed.

Lemma cpaco12_step r rg:
  gf (cpaco12 rg rg) <12= cpaco12 r rg.
Proof.
  intros. econstructor. apply rclo12_base. left.
  pstep. eapply gf_mon. apply PR.
  intros. destruct PR0. eapply rclo12_mon. apply IN.
  intros. destruct PR0.
  - left. eapply paco12_mon. apply H. right. destruct PR0; apply H0.
  - right. right. apply H.
Qed.

Lemma cpaco12_init:
  cpaco12 bot12 bot12 <12= paco12 gf bot12.
Proof.
  intros. destruct PR. revert x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 IN.
  pcofix CIH. intros.
  pstep. eapply gf_mon; [| right; apply CIH, rclo12_rclo, PR]. 
  apply compat12_compat with (gf:=gf). apply rclo12_compat. apply gf_mon. apply clo_compat.
  eapply rclo12_mon. apply IN.
  intros. pclearbot. _punfold PR; [..|apply cpaco12_def_mon].
  eapply cpaco12_def_mon. apply PR.
  intros. pclearbot. left. apply PR0.
Qed.

Lemma cpaco12_final r rg:
  (r \12/ paco12 gf rg) <12= cpaco12 r rg.
Proof.
  intros. destruct PR. apply cpaco12_base, H.
  econstructor. apply rclo12_base.
  left. eapply paco12_mon_gen. apply H.
  - intros. eapply gf_mon. apply PR.
    intros. apply rclo12_base. apply PR0.
  - intros. right. apply PR.
Qed.

Lemma cpaco12_unfold:
  cpaco12 bot12 bot12 <12= gf (cpaco12 bot12 bot12).
Proof.
  intros. apply cpaco12_init in PR. _punfold PR; [..|apply gf_mon].
  eapply gf_mon. apply PR.
  intros. pclearbot. apply cpaco12_final. right. apply PR0.
Qed.

End CompatiblePaco12_main.

Lemma cpaco12_mon_gen (gf gf' clo clo': rel -> rel) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 r r' rg rg'
      (IN: @cpaco12 gf clo r rg x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)
      (MON: monotone12 gf)
      (LEgf: gf <13= gf')
      (LEclo: clo <13= clo')
      (LEr: r <12= r')
      (LErg: rg <12= rg') :
  @cpaco12 gf' clo' r' rg' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11.
Proof.
  eapply cpaco12_mon; [|apply LEr|apply LErg].
  destruct IN. econstructor.
  eapply rclo12_mon_gen. apply IN. apply LEclo.
  intros. destruct PR; [| right; apply H].
  left. eapply paco12_mon_gen. apply H.
  - intros. eapply LEgf.
    eapply MON. apply PR.
    intros. eapply rclo12_mon_gen. apply PR0. apply LEclo. intros; apply PR1.
  - intros. apply PR.
Qed.

Lemma cpaco12_mon_bot (gf gf' clo clo': rel -> rel) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 r' rg'
      (IN: @cpaco12 gf clo bot12 bot12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)
      (MON: monotone12 gf)
      (LEgf: gf <13= gf')
      (LEclo: clo <13= clo'):
  @cpaco12 gf' clo' r' rg' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11.
Proof.
  eapply cpaco12_mon_gen. apply IN. apply MON. apply LEgf. apply LEclo. contradiction. contradiction.
Qed.

End CompatiblePaco12.

Hint Resolve cpaco12_base : paco.
Hint Resolve cpaco12_step : paco.
Hint Resolve cpaco12_final : paco.
Hint Resolve rclo12_base : paco.
