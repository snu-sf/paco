Require Export Program.Basics. Open Scope program_scope.
Require Import paco3 pacotac cpn3.
Set Implicit Arguments.

Section CompatiblePaco3.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.
Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.

Local Notation rel := (rel3 T0 T1 T2).

Section CompatiblePaco3_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone3 gf.

Variable clo : rel -> rel.
Hypothesis clo_compat: compatible3 gf clo.

Inductive cpaco3 r rg x0 x1 x2 : Prop :=
| cpaco3_intro (IN: rclo3 clo (r \3/ paco3 (compose gf (rclo3 clo)) rg) x0 x1 x2)
.

Definition cupaco3 r := cpaco3 r r.

Lemma cpaco3_def_mon : monotone3 (compose gf (rclo3 clo)).
Proof.
  eapply monotone3_compose. apply gf_mon. apply rclo3_mon.
Qed.

Hint Resolve cpaco3_def_mon : paco.

Lemma cpaco3_mon r r' rg rg' x0 x1 x2
      (IN: @cpaco3 r rg x0 x1 x2)
      (LEr: r <3= r')
      (LErg: rg <3= rg'):
  @cpaco3 r' rg' x0 x1 x2.
Proof.
  destruct IN. econstructor.
  eapply rclo3_mon. apply IN.
  intros. destruct PR. left. apply LEr, H.
  right. eapply paco3_mon. apply H. apply LErg.
Qed.

Lemma cpaco3_base r rg: r <3= cpaco3 r rg.
Proof.
  econstructor. apply rclo3_base. left. apply PR.
Qed.

Lemma cpaco3_rclo r rg:
  rclo3 clo (cpaco3 r rg) <3= cpaco3 r rg.
Proof.
  intros. econstructor. apply rclo3_rclo.
  eapply rclo3_mon. apply PR.
  intros. apply PR0.
Qed.

Lemma cpaco3_clo r rg:
  clo (cpaco3 r rg) <3= cpaco3 r rg.
Proof.
  intros. apply cpaco3_rclo. apply rclo3_clo.
  eapply clo_compat. apply PR.
  intros. apply rclo3_base. apply PR0.
Qed.

Lemma cpaco3_step r rg:
  gf (cpaco3 rg rg) <3= cpaco3 r rg.
Proof.
  intros. econstructor. apply rclo3_base. right.
  pstep. eapply gf_mon. apply PR.
  intros. destruct PR0.
  eapply rclo3_mon. apply IN.
  intros. destruct PR0; [right|left]; apply H.
Qed.

Lemma cpaco3_init:
  cpaco3 bot3 bot3 <3= paco3 gf bot3.
Proof.
  intros. destruct PR. revert x0 x1 x2 IN.
  pcofix CIH. intros.
  pstep. eapply gf_mon; [| right; apply CIH, rclo3_rclo, PR]. 
  apply compat3_compat with (gf:=gf). apply rclo3_compat. apply gf_mon. apply clo_compat.
  eapply rclo3_mon. apply IN.
  intros. destruct PR. contradiction.
  _punfold H; [..|apply cpaco3_def_mon]. eapply cpaco3_def_mon. apply H.
  intros. pclearbot. right. apply PR.
Qed.

Lemma cpaco3_final:
  paco3 gf bot3 <3= cpaco3 bot3 bot3.
Proof.
  intros. econstructor. apply rclo3_base.
  right. eapply paco3_mon_bot. apply PR.
  intros. eapply gf_mon. apply PR0.
  intros. apply rclo3_base. apply PR1.
Qed.

Lemma cpaco3_unfold:
  cpaco3 bot3 bot3 <3= gf (cpaco3 bot3 bot3).
Proof.
  intros. apply cpaco3_init in PR. _punfold PR; [..|apply gf_mon].
  eapply gf_mon. apply PR.
  intros. pclearbot. apply cpaco3_final, PR0.
Qed.

Lemma cpaco3_cofix
      r rg (LE: r <3= rg)
      l (OBG: forall rr (INC: rg <3= rr) (CIH: l <3= rr), l <3= cpaco3 r rr):
  l <3= cpaco3 r rg.
Proof.
  assert (IN: l <3= cpaco3 r (rg \3/ l)).
  { intros. apply OBG; [left; apply PR0 | right; apply PR0 | apply PR]. }
  clear OBG. intros. apply IN in PR.
  destruct PR. econstructor.
  eapply rclo3_mon. apply IN0.
  clear x0 x1 x2 IN0.
  intros. destruct PR. left. apply H.
  right. revert x0 x1 x2 H.
  pcofix CIH. intros.
  _punfold H0; [..|apply cpaco3_def_mon]. pstep.
  eapply gf_mon. apply H0. intros.
  apply rclo3_rclo. eapply rclo3_mon. apply PR.
  intros. destruct PR0.
  - apply rclo3_base. right. apply CIH. apply H.
  - destruct H.
    + apply rclo3_base. right. apply CIH0, H.
    + apply IN in H. destruct H.
      eapply rclo3_mon. apply IN0.
      intros. destruct PR0.
      * right. apply CIH0. apply LE, H.
      * right. apply CIH. apply H.
Qed.

Lemma cpaco3_cupaco
      r rg (LEr: r <3= rg):
  cupaco3 (cpaco3 r rg) <3= cpaco3 r rg.
Proof.
  eapply cpaco3_cofix. apply LEr.
  intros. destruct PR. econstructor.
  apply rclo3_rclo. eapply rclo3_mon. apply IN.
  intros. destruct PR.
  - destruct H.  eapply rclo3_mon. apply IN0.
    intros. destruct PR. left. apply H.
    right. eapply paco3_mon. apply H. apply INC.
  - apply rclo3_base. right.
    eapply paco3_mon. apply H.
    intros. apply CIH.
    econstructor. apply rclo3_base. left. apply PR.
Qed.

Lemma cpaco3_uclo (uclo: rel -> rel)
      r rg (LEr: r <3= rg)
      (LEclo: uclo <4= cupaco3) :
  uclo (cpaco3 r rg) <3= cpaco3 r rg.
Proof.
  intros. apply cpaco3_cupaco. apply LEr. apply LEclo, PR.
Qed.

End CompatiblePaco3_main.

Lemma cpaco3_mon_gen (gf gf' clo clo': rel -> rel) x0 x1 x2 r r' rg rg'
      (IN: @cpaco3 gf clo r rg x0 x1 x2)
      (MON: monotone3 gf)
      (LEgf: gf <4= gf')
      (LEclo: clo <4= clo')
      (LEr: r <3= r')
      (LErg: rg <3= rg') :
  @cpaco3 gf' clo' r' rg' x0 x1 x2.
Proof.
  eapply cpaco3_mon; [|apply LEr|apply LErg].
  destruct IN. econstructor.
  eapply rclo3_mon_gen. apply IN. apply LEclo.
  intros. destruct PR. left; apply H.
  right. eapply paco3_mon_gen. apply H.
  - intros. eapply LEgf.
    eapply MON. apply PR.
    intros. eapply rclo3_mon_gen. apply PR0. apply LEclo. intros; apply PR1.
  - intros. apply PR.
Qed.

End CompatiblePaco3.

Hint Resolve cpaco3_base : paco.
Hint Resolve cpaco3_step : paco.
Hint Resolve rclo3_base : paco.
Hint Resolve rclo3_clo : paco.
