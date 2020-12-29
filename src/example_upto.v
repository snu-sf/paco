Require Import Paco.paco.
Require Import Program.Tactics.
Require Import RelationClasses.
Require Import Morphisms.

Set Implicit Arguments.

(*** A minimal example describing upto technique. ***)



(*** Tactics ***)
Ltac inv H := inversion H; subst; clear H.



(*** Coinductive stream ***)
CoInductive stream :=
| snil
| scons (n: nat) (s: stream)
.

Definition match_stream (s: stream) :=
  match s with
  | snil => snil
  | scons n s => scons n s
  end.

Lemma unfold_stream s
  :
    s = match_stream s.
Proof.
  destruct s; auto.
Qed.



(*** Concat of two streams ***)
Definition match_concat concat (s0 s1: stream): stream :=
  match s0 with
  | snil => s1
  | scons n s0 => scons n (concat s0 s1)
  end
.

CoFixpoint concat (s0 s1: stream): stream := match_concat concat s0 s1.

Declare Scope stream_scope.

Notation "x ++ y" := (concat x y) : stream_scope.
Notation "[ ]" := snil (format "[ ]") : stream_scope.
Notation "[ x ]" := (scons x snil) : stream_scope.
Notation "[ x ; y ; .. ; z ]" := (scons x (scons y .. (scons z snil) ..)) : stream_scope.
Open Scope stream_scope.

Lemma unfold_concat: forall s0 s1, s0 ++ s1 = match_concat concat s0 s1.
Proof.
  intros.
  rewrite unfold_stream with (concat s0 s1). simpl.
  destruct (match_concat concat s0 s1) eqn:T; reflexivity.
Qed.



(*** Bisimulation between two streams ***)
Inductive _sim (sim : stream -> stream -> Prop): stream -> stream -> Prop :=
| SimNil: _sim sim snil snil
| SimCons n sl sr (REL: sim sl sr): _sim sim (scons n sl) (scons n sr)
.
Hint Constructors _sim : core.

Lemma _sim_mon : monotone2 (_sim).
Proof.
  intros x0 x1 r r' IN LE. induction IN; auto.
Qed.
Hint Resolve _sim_mon : paco.

Definition sim (sl sr: stream) := paco2 (_sim) bot2 sl sr.
Hint Unfold sim : core.



(*** First (failing) attempt without upto technique ***)
Lemma sim_concat
      s0 s1 t0 t1
      (EQ0: sim s0 t0)
      (EQ1: sim s1 t1)
  :
    @sim (concat s0 s1) (concat t0 t1)
.
Proof.
  revert_until s0. revert s0.
  pcofix CIH. intros. pfold.
  punfold EQ0. punfold EQ1.
  inv EQ0.
  - rewrite ! unfold_concat. cbn.
    eapply _sim_mon; eauto. intros. pclearbot. left. eapply paco2_mon; eauto. intros.
    red in PR0. contradict PR0.
  - rewrite ! unfold_concat. cbn. pclearbot.
    econstructor; eauto. left.
    inv EQ1.
    + (*** We are stuck here..? ***) admit.
    + pclearbot. pfold.
      (*** We are stuck here..? ***) admit.
      (*** TODO: give better explanation ***)
Abort.



(*** Second attempt with upto technique ***)
Inductive prefixC (R : stream -> stream -> Prop): stream -> stream -> Prop :=
| prefixC_intro
    s0 s1 t0 t1
    (REL: sim s0 t0)
    (REL: R s1 t1)
  :
    prefixC R (concat s0 s1) (concat t0 t1)
.
Hint Constructors prefixC: core.

Lemma prefixC_spec
      simC
  :
    prefixC <3= gupaco2 (_sim) (simC)
.
Proof.
  gcofix CIH. intros. destruct PR.
  punfold REL. inv REL.
  - rewrite ! unfold_concat. cbn. gbase. eauto. (* Note: "eauto with paco" also works *)
  - gstep.
    rewrite ! unfold_concat. cbn.
    econstructor; eauto.
    pclearbot. gbase. eauto. (* Note: "eauto with paco" also works *)
Qed.

Lemma sim_concat
      s0 s1 t0 t1
      (EQ0: sim s0 t0)
      (EQ1: sim s1 t1)
  :
    @sim (concat s0 s1) (concat t0 t1)
.
Proof.
  intros. ginit. { eapply cpn2_wcompat; pmonauto. } guclo prefixC_spec.
Qed.

Lemma sim_concat_proper: Proper (sim ==> sim ==> sim) concat.
Proof.
  repeat intro. eapply sim_concat; eauto.
Qed.
