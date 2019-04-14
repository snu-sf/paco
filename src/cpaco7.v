Require Export Program.Basics. Open Scope program_scope.
Require Import paco7 pacotac cpn7.
Set Implicit Arguments.

Section CompatiblePaco7.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.
Variable T6 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3) (x5: @T5 x0 x1 x2 x3 x4), Type.

Local Notation rel := (rel7 T0 T1 T2 T3 T4 T5 T6).

Section CompatiblePaco7_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone7 gf.

Variable clo : rel -> rel.
Hypothesis clo_compat: compatible7 gf clo.

Inductive cpaco7 r rg x0 x1 x2 x3 x4 x5 x6 : Prop :=
| cpaco7_intro (IN: rclo7 clo (paco7 (compose gf (rclo7 clo)) (r \7/ rg) \7/ r) x0 x1 x2 x3 x4 x5 x6)
.

Definition cupaco7 r := cpaco7 r r.

Lemma cpaco7_def_mon : monotone7 (compose gf (rclo7 clo)).
Proof.
  eapply monotone7_compose. apply gf_mon. apply rclo7_mon.
Qed.

Hint Resolve cpaco7_def_mon : paco.

Lemma cpaco7_mon r r' rg rg' x0 x1 x2 x3 x4 x5 x6
      (IN: @cpaco7 r rg x0 x1 x2 x3 x4 x5 x6)
      (LEr: r <7= r')
      (LErg: rg <7= rg'):
  @cpaco7 r' rg' x0 x1 x2 x3 x4 x5 x6.
Proof.
  destruct IN. econstructor.
  eapply rclo7_mon. apply IN.
  intros. destruct PR; [|right; apply LEr, H].
  left. eapply paco7_mon. apply H.
  intros. destruct PR.
  - left. apply LEr, H0.
  - right. apply LErg, H0.
Qed.

Lemma cpaco7_cofix r rg 
      l (OBG: forall rr (INC: rg <7= rr) (CIH: l <7= rr), l <7= cpaco7 r rr):
  l <7= cpaco7 r rg.
Proof.
  assert (IN: l <7= cpaco7 r (rg \7/ l)).
  { intros. apply OBG; [left; apply PR0 | right; apply PR0 | apply PR]. }
  clear OBG. intros. apply IN in PR.
  destruct PR. econstructor.
  eapply rclo7_mon. apply IN0.
  clear x0 x1 x2 x3 x4 x5 x6 IN0.
  intros. destruct PR; [|right; apply H].
  left. revert x0 x1 x2 x3 x4 x5 x6 H.
  pcofix CIH. intros.
  _punfold H0; [..|apply cpaco7_def_mon]. pstep.
  eapply gf_mon. apply H0. intros.
  apply rclo7_rclo. eapply rclo7_mon. apply PR.
  intros. destruct PR0.
  - apply rclo7_base. right. apply CIH. apply H.
  - destruct H; [|destruct H].
    + apply rclo7_base. right. apply CIH0. left. apply H.
    + apply rclo7_base. right. apply CIH0. right. apply H.
    + apply IN in H. destruct H.
      eapply rclo7_mon. apply IN0.
      intros. destruct PR0.
      * right. apply CIH. apply H.      
      * right. apply CIH0. left. apply H.
Qed.

Lemma cpaco7_cupaco r rg:
  cupaco7 (cpaco7 r rg) <7= cpaco7 r rg.
Proof.
  eapply cpaco7_cofix.
  intros. destruct PR. econstructor.
  apply rclo7_rclo. eapply rclo7_mon. apply IN.
  intros. destruct PR.
  - apply rclo7_base. left.
    eapply paco7_mon. apply H.
    intros. right; apply CIH.
    econstructor. apply rclo7_base. right.
    destruct PR as [PR|PR]; apply PR.
  - destruct H. eapply rclo7_mon. apply IN0.
    intros. destruct PR; [| right; apply H].
    left. eapply paco7_mon. apply H.
    intros. destruct PR. left; apply H0.
    right. apply INC, H0.
Qed.

Lemma cpaco7_uclo (uclo: rel -> rel) r rg 
      (LEclo: uclo <8= cupaco7) :
  uclo (cpaco7 r rg) <7= cpaco7 r rg.
Proof.
  intros. apply cpaco7_cupaco. apply LEclo, PR.
Qed.

Lemma cpaco7_base r rg: r <7= cpaco7 r rg.
Proof.
  econstructor. apply rclo7_base. right. apply PR.
Qed.

Lemma cpaco7_rclo r:
  rclo7 clo r <7= cupaco7 r.
Proof.
  intros. econstructor.
  eapply rclo7_mon. apply PR.
  intros. right. apply PR0.
Qed.

Lemma cpaco7_clo r:
  clo r <7= cupaco7 r.
Proof.
  intros. apply cpaco7_rclo. apply rclo7_clo.
  eapply clo_compat. apply PR.
  intros. apply rclo7_base. apply PR0.
Qed.

Lemma cpaco7_step r rg:
  gf (cpaco7 rg rg) <7= cpaco7 r rg.
Proof.
  intros. econstructor. apply rclo7_base. left.
  pstep. eapply gf_mon. apply PR.
  intros. destruct PR0. eapply rclo7_mon. apply IN.
  intros. destruct PR0.
  - left. eapply paco7_mon. apply H. right. destruct PR0; apply H0.
  - right. right. apply H.
Qed.

Lemma cpaco7_init:
  cpaco7 bot7 bot7 <7= paco7 gf bot7.
Proof.
  intros. destruct PR. revert x0 x1 x2 x3 x4 x5 x6 IN.
  pcofix CIH. intros.
  pstep. eapply gf_mon; [| right; apply CIH, rclo7_rclo, PR]. 
  apply compat7_compat with (gf:=gf). apply rclo7_compat. apply gf_mon. apply clo_compat.
  eapply rclo7_mon. apply IN.
  intros. pclearbot. _punfold PR; [..|apply cpaco7_def_mon].
  eapply cpaco7_def_mon. apply PR.
  intros. pclearbot. left. apply PR0.
Qed.

Lemma cpaco7_final r rg:
  (r \7/ paco7 gf rg) <7= cpaco7 r rg.
Proof.
  intros. destruct PR. apply cpaco7_base, H.
  econstructor. apply rclo7_base.
  left. eapply paco7_mon_gen. apply H.
  - intros. eapply gf_mon. apply PR.
    intros. apply rclo7_base. apply PR0.
  - intros. right. apply PR.
Qed.

Lemma cpaco7_unfold:
  cpaco7 bot7 bot7 <7= gf (cpaco7 bot7 bot7).
Proof.
  intros. apply cpaco7_init in PR. _punfold PR; [..|apply gf_mon].
  eapply gf_mon. apply PR.
  intros. pclearbot. apply cpaco7_final. right. apply PR0.
Qed.

End CompatiblePaco7_main.

Lemma cpaco7_mon_gen (gf gf' clo clo': rel -> rel) x0 x1 x2 x3 x4 x5 x6 r r' rg rg'
      (IN: @cpaco7 gf clo r rg x0 x1 x2 x3 x4 x5 x6)
      (MON: monotone7 gf)
      (LEgf: gf <8= gf')
      (LEclo: clo <8= clo')
      (LEr: r <7= r')
      (LErg: rg <7= rg') :
  @cpaco7 gf' clo' r' rg' x0 x1 x2 x3 x4 x5 x6.
Proof.
  eapply cpaco7_mon; [|apply LEr|apply LErg].
  destruct IN. econstructor.
  eapply rclo7_mon_gen. apply IN. apply LEclo.
  intros. destruct PR; [| right; apply H].
  left. eapply paco7_mon_gen. apply H.
  - intros. eapply LEgf.
    eapply MON. apply PR.
    intros. eapply rclo7_mon_gen. apply PR0. apply LEclo. intros; apply PR1.
  - intros. apply PR.
Qed.

Lemma cpaco7_mon_bot (gf gf' clo clo': rel -> rel) x0 x1 x2 x3 x4 x5 x6 r' rg'
      (IN: @cpaco7 gf clo bot7 bot7 x0 x1 x2 x3 x4 x5 x6)
      (MON: monotone7 gf)
      (LEgf: gf <8= gf')
      (LEclo: clo <8= clo'):
  @cpaco7 gf' clo' r' rg' x0 x1 x2 x3 x4 x5 x6.
Proof.
  eapply cpaco7_mon_gen. apply IN. apply MON. apply LEgf. apply LEclo. contradiction. contradiction.
Qed.

End CompatiblePaco7.

Hint Resolve cpaco7_base : paco.
Hint Resolve cpaco7_step : paco.
Hint Resolve cpaco7_final : paco.
Hint Resolve rclo7_base : paco.
