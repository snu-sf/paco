Require Import paco2 cpn2 cpntac.
Set Implicit Arguments.

Section WCompanion2.

Variable T0 : Type.
Variable T1 : forall (x0: @T0), Type.

Local Notation rel := (rel2 T0 T1).

Section WCompanion2_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone2 gf.

Inductive gcpn2 (r rg : rel) e0 e1 : Prop :=
| gcpn2_intro (IN: cpn2 gf (r \2/ fcpn2 gf rg) e0 e1)
.              

Lemma gcpn2_mon r r' rg rg' e0 e1
      (IN: @gcpn2 r rg e0 e1)
      (LEr: r <2= r')
      (LErg: rg <2= rg'):
  @gcpn2 r' rg' e0 e1.
Proof.
  destruct IN. constructor.
  eapply cpn2_mon. apply IN. intros.
  destruct PR. left. apply LEr, H. right.
  eapply fcpn2_mon. apply gf_mon. apply H. apply LErg.
Qed.

Lemma gcpn2_inc_mon r rg:
  monotone2 (fun x : rel => gcpn2 r (rg \2/ x)).
Proof.
  red; intros.
  eapply gcpn2_mon. apply IN. intros. apply PR.
  intros. destruct PR. left. apply H. right. apply LE, H. 
Qed.

Lemma gcpn2_init r: gcpn2 r r <2= cpn2 gf r.
Proof.
  intros. destruct PR.
  ucpn.
  eapply cpn2_mon; [apply IN|].
  intros. destruct PR.
  - ubase. apply H.
  - ustep. apply H.
Qed.

Lemma gcpn2_final r rg: cpn2 gf r <2= gcpn2 r rg.
Proof.
  constructor. eapply cpn2_mon. apply PR.
  intros. left. apply PR0.
Qed.

Lemma gcpn2_unfold:
  gcpn2 bot2 bot2 <2= gf (gcpn2 bot2 bot2).
Proof.
  intros. apply gcpn2_init in PR. uunfold PR.
  eapply gf_mon; [apply PR|].
  intros. apply gcpn2_final. apply PR0.
Qed.

Lemma gcpn2_base r rg:
  r <2= gcpn2 r rg.
Proof.
  intros. constructor. ubase. left. apply PR.
Qed.

Lemma gcpn2_step r rg:
  gf (gcpn2 rg rg) <2= gcpn2 r rg.
Proof.
  intros. constructor. ubase. right.
  eapply gf_mon. apply PR.
  intros. apply gcpn2_init. apply PR0.
Qed.

Lemma gcpn2_cpn r rg:
  cpn2 gf (gcpn2 r rg) <2= gcpn2 r rg.
Proof.
  intros. constructor. ucpn.
  eapply cpn2_mon. apply PR.
  intros. destruct PR0. apply IN.
Qed.

Lemma gcpn2_clo r rg
      clo (LE: clo <3= cpn2 gf):
  clo (gcpn2 r rg) <2= gcpn2 r rg.
Proof.
  intros. apply gcpn2_cpn, LE, PR.
Qed.

Definition cut2 (x y z: rel) : rel := fun e0 e1 => y <2= z /\ x e0 e1.

Lemma cut2_mon x y : monotone2 (cut2 x y).
Proof.
  repeat red. intros. destruct IN. split.
  - intros. apply LE, H, PR.
  - apply H0.
Qed.

Lemma cut2_wcomp r rg (LE: r <2= rg) :
  wcompatible2 gf (cut2 (cpn2 (fun x => gcpn2 r (rg \2/ x)) bot2) rg).
Proof.
  set (pfix := cpn2 (fun x => gcpn2 r (rg \2/ x)) bot2).
  
  econstructor; [apply cut2_mon|]. intros.
  destruct PR as [LEz FIX].
  uunfold FIX; [|apply gcpn2_inc_mon].
  eapply gf_mon, rclo2_cpn.
  apply cpn2_compat; [apply gf_mon|].
  eapply cpn2_mon; [apply FIX|]. clear x0 x1 FIX; intros.

  destruct PR as [PR | PR].
  - apply LE in PR. apply LEz in PR.
    eapply gf_mon. apply PR.
    intros. apply rclo2_base. apply PR0.
  - eapply gf_mon; [apply PR|]. clear x0 x1 PR; intros.
    eapply rclo2_cpn.
    eapply cpn2_mon. apply PR. clear x0 x1 PR; intros.
    destruct PR as [PR | PR].
    + apply rclo2_step. eapply gf_mon. apply LEz, PR.
      intros. apply rclo2_base, PR0.
    + apply rclo2_clo. split.
      * intros. apply rclo2_step.
        eapply gf_mon. apply LEz. apply PR0.
        intros. apply rclo2_base. apply PR1.
      * apply PR.
Qed.

Lemma fix2_le_cpn r rg (LE: r <2= rg) :
  cpn2 (fun x => gcpn2 r (rg \2/ x)) bot2 <2= cpn2 gf rg.
Proof.
  intros. eexists.
  - apply wcompat2_compat, cut2_wcomp. apply gf_mon. apply LE.
  - apply rclo2_clo. split.
    + intros. apply rclo2_base. apply PR0.
    + apply PR.
Qed.

Lemma fix2_le_gcpn r rg (LE: r <2= rg):
  cpn2 (fun x => gcpn2 r (rg \2/ x)) bot2 <2= gcpn2 r rg.
Proof.
  (*
    fix
    =
    c(r + gc(rg + fix))
    <=
    c(r + gc(rg + c(rg)))  (by Lemma fix2_le_cpn)
    <=
    c(r + gc(rg))
   *)
  
  intros. uunfold PR; [| apply gcpn2_inc_mon].
  destruct PR. constructor.
  eapply cpn2_mon. apply IN. intros.
  destruct PR. left; apply H. right.
  eapply gf_mon.  apply H. intros.
  ucpn.
  eapply cpn2_mon. apply PR. intros.
  destruct PR0.
  - ubase. apply H0.
  - eapply fix2_le_cpn. apply LE. apply H0.
Qed.

Lemma gcpn2_cofix: forall
    r rg (LE: r <2= rg)
    l (OBG: forall rr (INC: rg <2= rr) (CIH: l <2= rr), l <2= gcpn2 r rr),
  l <2= gcpn2 r rg.
Proof.
  intros. apply fix2_le_gcpn. apply LE.
  eapply cpn2_algebra, PR. apply gcpn2_inc_mon.
  intros. eapply OBG; intros.
  - left. apply PR1.
  - right. apply PR1.
  - apply PR0.
Qed.

End WCompanion2_main.

Lemma gcpn2_mon_bot (gf gf': rel -> rel) e0 e1 r rg
      (IN: @gcpn2 gf bot2 bot2 e0 e1)
      (MONgf: monotone2 gf)
      (MONgf': monotone2 gf')
      (LE: gf <3= gf'):
  @gcpn2 gf' r rg e0 e1.
Proof.
  destruct IN. constructor.
  eapply cpn2_mon; [| intros; right; eapply PR].
  ubase.
  eapply fcpn2_mon_bot, LE; [|apply MONgf|apply MONgf'].
  eapply MONgf, cpn2_cpn; [| apply MONgf].
  eapply (compat2_compat (cpn2_compat MONgf)).
  eapply cpn2_mon. apply IN.
  intros. destruct PR. contradiction. apply H.
Qed.

End WCompanion2.

Hint Resolve gcpn2_base : paco.
Hint Resolve gcpn2_step : paco.

