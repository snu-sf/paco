Require Export Program.Basics. Open Scope program_scope.
Require Import paco6 pacotac cpn6.
Set Implicit Arguments.

Section CompatiblePaco6.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.
Variable T4 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2), Type.
Variable T5 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1) (x3: @T3 x0 x1 x2) (x4: @T4 x0 x1 x2 x3), Type.

Local Notation rel := (rel6 T0 T1 T2 T3 T4 T5).

Section CompatiblePaco6_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone6 gf.

Variable clo : rel -> rel.
Hypothesis clo_compat: compatible6 gf clo.

Inductive cpaco6 r rg x0 x1 x2 x3 x4 x5 : Prop :=
| cpaco6_intro (IN: rclo6 clo (paco6 (compose gf (rclo6 clo)) (r \6/ rg) \6/ r) x0 x1 x2 x3 x4 x5)
.

Definition cupaco6 r := cpaco6 r r.

Lemma cpaco6_def_mon : monotone6 (compose gf (rclo6 clo)).
Proof.
  eapply monotone6_compose. apply gf_mon. apply rclo6_mon.
Qed.

Hint Resolve cpaco6_def_mon : paco.

Lemma cpaco6_mon r r' rg rg' x0 x1 x2 x3 x4 x5
      (IN: @cpaco6 r rg x0 x1 x2 x3 x4 x5)
      (LEr: r <6= r')
      (LErg: rg <6= rg'):
  @cpaco6 r' rg' x0 x1 x2 x3 x4 x5.
Proof.
  destruct IN. econstructor.
  eapply rclo6_mon. apply IN.
  intros. destruct PR; [|right; apply LEr, H].
  left. eapply paco6_mon. apply H.
  intros. destruct PR.
  - left. apply LEr, H0.
  - right. apply LErg, H0.
Qed.

Lemma cpaco6_cofix r rg 
      l (OBG: forall rr (INC: rg <6= rr) (CIH: l <6= rr), l <6= cpaco6 r rr):
  l <6= cpaco6 r rg.
Proof.
  assert (IN: l <6= cpaco6 r (rg \6/ l)).
  { intros. apply OBG; [left; apply PR0 | right; apply PR0 | apply PR]. }
  clear OBG. intros. apply IN in PR.
  destruct PR. econstructor.
  eapply rclo6_mon. apply IN0.
  clear x0 x1 x2 x3 x4 x5 IN0.
  intros. destruct PR; [|right; apply H].
  left. revert x0 x1 x2 x3 x4 x5 H.
  pcofix CIH. intros.
  _punfold H0; [..|apply cpaco6_def_mon]. pstep.
  eapply gf_mon. apply H0. intros.
  apply rclo6_rclo. eapply rclo6_mon. apply PR.
  intros. destruct PR0.
  - apply rclo6_base. right. apply CIH. apply H.
  - destruct H; [|destruct H].
    + apply rclo6_base. right. apply CIH0. left. apply H.
    + apply rclo6_base. right. apply CIH0. right. apply H.
    + apply IN in H. destruct H.
      eapply rclo6_mon. apply IN0.
      intros. destruct PR0.
      * right. apply CIH. apply H.      
      * right. apply CIH0. left. apply H.
Qed.

Lemma cpaco6_cupaco r rg:
  cupaco6 (cpaco6 r rg) <6= cpaco6 r rg.
Proof.
  eapply cpaco6_cofix.
  intros. destruct PR. econstructor.
  apply rclo6_rclo. eapply rclo6_mon. apply IN.
  intros. destruct PR.
  - apply rclo6_base. left.
    eapply paco6_mon. apply H.
    intros. right; apply CIH.
    econstructor. apply rclo6_base. right.
    destruct PR as [PR|PR]; apply PR.
  - destruct H. eapply rclo6_mon. apply IN0.
    intros. destruct PR; [| right; apply H].
    left. eapply paco6_mon. apply H.
    intros. destruct PR. left; apply H0.
    right. apply INC, H0.
Qed.

Lemma cpaco6_uclo (uclo: rel -> rel) r rg 
      (LEclo: uclo <7= cupaco6) :
  uclo (cpaco6 r rg) <6= cpaco6 r rg.
Proof.
  intros. apply cpaco6_cupaco. apply LEclo, PR.
Qed.

Lemma cpaco6_base r rg: r <6= cpaco6 r rg.
Proof.
  econstructor. apply rclo6_base. right. apply PR.
Qed.

Lemma cpaco6_rclo r:
  rclo6 clo r <6= cupaco6 r.
Proof.
  intros. econstructor.
  eapply rclo6_mon. apply PR.
  intros. right. apply PR0.
Qed.

Lemma cpaco6_clo r:
  clo r <6= cupaco6 r.
Proof.
  intros. apply cpaco6_rclo. apply rclo6_clo.
  eapply clo_compat. apply PR.
  intros. apply rclo6_base. apply PR0.
Qed.

Lemma cpaco6_step r rg:
  gf (cpaco6 rg rg) <6= cpaco6 r rg.
Proof.
  intros. econstructor. apply rclo6_base. left.
  pstep. eapply gf_mon. apply PR.
  intros. destruct PR0. eapply rclo6_mon. apply IN.
  intros. destruct PR0.
  - left. eapply paco6_mon. apply H. right. destruct PR0; apply H0.
  - right. right. apply H.
Qed.

Lemma cpaco6_init:
  cpaco6 bot6 bot6 <6= paco6 gf bot6.
Proof.
  intros. destruct PR. revert x0 x1 x2 x3 x4 x5 IN.
  pcofix CIH. intros.
  pstep. eapply gf_mon; [| right; apply CIH, rclo6_rclo, PR]. 
  apply compat6_compat with (gf:=gf). apply rclo6_compat. apply gf_mon. apply clo_compat.
  eapply rclo6_mon. apply IN.
  intros. pclearbot. _punfold PR; [..|apply cpaco6_def_mon].
  eapply cpaco6_def_mon. apply PR.
  intros. pclearbot. left. apply PR0.
Qed.

Lemma cpaco6_final r rg:
  (r \6/ paco6 gf rg) <6= cpaco6 r rg.
Proof.
  intros. destruct PR. apply cpaco6_base, H.
  econstructor. apply rclo6_base.
  left. eapply paco6_mon_gen. apply H.
  - intros. eapply gf_mon. apply PR.
    intros. apply rclo6_base. apply PR0.
  - intros. right. apply PR.
Qed.

Lemma cpaco6_unfold:
  cpaco6 bot6 bot6 <6= gf (cpaco6 bot6 bot6).
Proof.
  intros. apply cpaco6_init in PR. _punfold PR; [..|apply gf_mon].
  eapply gf_mon. apply PR.
  intros. pclearbot. apply cpaco6_final. right. apply PR0.
Qed.

End CompatiblePaco6_main.

Lemma cpaco6_mon_gen (gf gf' clo clo': rel -> rel) x0 x1 x2 x3 x4 x5 r r' rg rg'
      (IN: @cpaco6 gf clo r rg x0 x1 x2 x3 x4 x5)
      (MON: monotone6 gf)
      (LEgf: gf <7= gf')
      (LEclo: clo <7= clo')
      (LEr: r <6= r')
      (LErg: rg <6= rg') :
  @cpaco6 gf' clo' r' rg' x0 x1 x2 x3 x4 x5.
Proof.
  eapply cpaco6_mon; [|apply LEr|apply LErg].
  destruct IN. econstructor.
  eapply rclo6_mon_gen. apply IN. apply LEclo.
  intros. destruct PR; [| right; apply H].
  left. eapply paco6_mon_gen. apply H.
  - intros. eapply LEgf.
    eapply MON. apply PR.
    intros. eapply rclo6_mon_gen. apply PR0. apply LEclo. intros; apply PR1.
  - intros. apply PR.
Qed.

Lemma cpaco6_mon_bot (gf gf' clo clo': rel -> rel) x0 x1 x2 x3 x4 x5 r' rg'
      (IN: @cpaco6 gf clo bot6 bot6 x0 x1 x2 x3 x4 x5)
      (MON: monotone6 gf)
      (LEgf: gf <7= gf')
      (LEclo: clo <7= clo'):
  @cpaco6 gf' clo' r' rg' x0 x1 x2 x3 x4 x5.
Proof.
  eapply cpaco6_mon_gen. apply IN. apply MON. apply LEgf. apply LEclo. contradiction. contradiction.
Qed.

End CompatiblePaco6.

Hint Resolve cpaco6_base : paco.
Hint Resolve cpaco6_step : paco.
Hint Resolve cpaco6_final : paco.
Hint Resolve rclo6_base : paco.
