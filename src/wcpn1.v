Require Import paco1 cpn1 cpntac.
Set Implicit Arguments.

Section WCompanion1.

Variable T0 : Type.

Local Notation rel := (rel1 T0).

Section WCompanion1_main.

Variable gf: rel -> rel.
Hypothesis gf_mon: monotone1 gf.

Inductive wcpn1 (r rg : rel) e0 : Prop :=
| wcpn1_intro (IN: cpn1 gf (r \1/ gcpn1 gf rg) e0)
.              
Hint Constructors wcpn1.

Lemma wcpn1_mon r r' rg rg' e0
      (IN: @wcpn1 r rg e0)
      (LEr: r <1= r')
      (LErg: rg <1= rg'):
  @wcpn1 r' rg' e0.
Proof.
  destruct IN. constructor.
  eapply cpn1_mon. apply IN. intros.
  destruct PR. left. apply LEr, H. right.
  eapply gcpn1_mon. apply gf_mon. apply H. apply LErg.
Qed.

Lemma wcpn1_inc_mon r rg:
  monotone1 (fun x : rel => wcpn1 r (rg \1/ x)).
Proof.
  red; intros.
  eapply wcpn1_mon. apply IN. intros. apply PR.
  intros. destruct PR. left. apply H. right. apply LE, H. 
Qed.

Lemma wcpn1_init r: wcpn1 r r <1= cpn1 gf r.
Proof.
  intros. destruct PR.
  ucpn.
  eapply cpn1_mon; [apply IN|].
  intros. destruct PR.
  - ubase. apply H.
  - ustep. apply H.
Qed.

Lemma wcpn1_final r rg: cpn1 gf r <1= wcpn1 r rg.
Proof.
  constructor. eapply cpn1_mon. apply PR.
  intros. left. apply PR0.
Qed.

Lemma wcpn1_unfold:
  wcpn1 bot1 bot1 <1= gf (wcpn1 bot1 bot1).
Proof.
  intros. apply wcpn1_init in PR. uunfold PR.
  eapply gf_mon; [apply PR|].
  intros. apply wcpn1_final. apply PR0.
Qed.

Lemma wcpn1_base r rg:
  r <1= wcpn1 r rg.
Proof.
  intros. constructor. ubase. left. apply PR.
Qed.

Lemma wcpn1_step r rg:
  gf (wcpn1 rg rg) <1= wcpn1 r rg.
Proof.
  intros. constructor. ubase. right.
  eapply gf_mon. apply PR.
  intros. apply wcpn1_init. apply PR0.
Qed.

Lemma wcpn1_cpn r rg:
  cpn1 gf (wcpn1 r rg) <1= wcpn1 r rg.
Proof.
  intros. constructor. ucpn.
  eapply cpn1_mon. apply PR.
  intros. destruct PR0. apply IN.
Qed.

Lemma wcpn1_clo r rg
      clo (LE: clo <2= cpn1 gf):
  clo (wcpn1 r rg) <1= wcpn1 r rg.
Proof.
  intros. apply wcpn1_cpn, LE, PR.
Qed.

Definition cut1 (x y z: rel) : rel := fun e0 => y <1= z /\ x e0.

Lemma cut1_mon x y : monotone1 (cut1 x y).
Proof.
  repeat red. intros. destruct IN. split.
  - intros. apply LE, H, PR.
  - apply H0.
Qed.

Lemma cut1_wcomp r rg (LE: r <1= rg) :
  wcompatible1 gf (cut1 (cpn1 (fun x => wcpn1 r (rg \1/ x)) bot1) rg).
Proof.
  set (pfix := cpn1 (fun x => wcpn1 r (rg \1/ x)) bot1).
  
  econstructor; [apply cut1_mon|]. intros.
  destruct PR as [LEz FIX].
  uunfold FIX; [|apply wcpn1_inc_mon].
  eapply gf_mon, rclo1_cpn.
  apply cpn1_compat; [apply gf_mon|].
  eapply cpn1_mon; [apply FIX|]. clear x0 FIX; intros.

  destruct PR as [PR | PR].
  - apply LE in PR. apply LEz in PR.
    eapply gf_mon. apply PR.
    intros. apply rclo1_base. apply PR0.
  - eapply gf_mon; [apply PR|]. clear x0 PR; intros.
    eapply rclo1_cpn.
    eapply cpn1_mon. apply PR. clear x0 PR; intros.
    destruct PR as [PR | PR].
    + apply rclo1_step. eapply gf_mon. apply LEz, PR.
      intros. apply rclo1_base, PR0.
    + apply rclo1_clo. split.
      * intros. apply rclo1_step.
        eapply gf_mon. apply LEz. apply PR0.
        intros. apply rclo1_base. apply PR1.
      * apply PR.
Qed.

Lemma fix1_le_cpn r rg (LE: r <1= rg) :
  cpn1 (fun x => wcpn1 r (rg \1/ x)) bot1 <1= cpn1 gf rg.
Proof.
  intros. eexists.
  - apply wcompat1_compat, cut1_wcomp. apply gf_mon. apply LE.
  - apply rclo1_clo. split.
    + intros. apply rclo1_base. apply PR0.
    + apply PR.
Qed.

Lemma fix1_le_wcpn r rg (LE: r <1= rg):
  cpn1 (fun x => wcpn1 r (rg \1/ x)) bot1 <1= wcpn1 r rg.
Proof.
  (*
    fix
    =
    c(r + gc(rg + fix))
    <=
    c(r + gc(rg + c(rg)))  (by Lemma fix1_le_cpn)
    <=
    c(r + gc(rg))
   *)
  
  intros. uunfold PR; [| apply wcpn1_inc_mon].
  destruct PR. constructor.
  eapply cpn1_mon. apply IN. intros.
  destruct PR. left; apply H. right.
  eapply gf_mon.  apply H. intros.
  ucpn.
  eapply cpn1_mon. apply PR. intros.
  destruct PR0.
  - ubase. apply H0.
  - eapply fix1_le_cpn. apply LE. apply H0.
Qed.

Lemma wcpn1_cofix: forall
    r rg (LE: r <1= rg)
    l (OBG: forall rr (INC: rg <1= rr) (CIH: l <1= rr), l <1= wcpn1 r rr),
  l <1= wcpn1 r rg.
Proof.
  intros. apply fix1_le_wcpn. apply LE.
  eapply cpn1_algebra, PR. apply wcpn1_inc_mon.
  intros. eapply OBG; intros.
  - left. apply PR1.
  - right. apply PR1.
  - apply PR0.
Qed.

End WCompanion1_main.

Lemma wcpn1_mon_bot (gf gf': rel -> rel) e0 r rg
      (IN: @wcpn1 gf bot1 bot1 e0)
      (MONgf: monotone1 gf)
      (MONgf': monotone1 gf')
      (LE: gf <2= gf'):
  @wcpn1 gf' r rg e0.
Proof.
  destruct IN. constructor.
  eapply cpn1_mon; [| intros; right; eapply PR].
  ubase.
  eapply gcpn1_mon_bot, LE; [|apply MONgf|apply MONgf'].
  eapply MONgf, cpn1_cpn; [| apply MONgf].
  eapply (compat1_compat (cpn1_compat MONgf)).
  eapply cpn1_mon. apply IN.
  intros. destruct PR. contradiction. apply H.
Qed.

End WCompanion1.

Hint Constructors wcpn1 : paco.

Hint Resolve wcpn1_base : paco.
Hint Resolve wcpn1_step : paco.

