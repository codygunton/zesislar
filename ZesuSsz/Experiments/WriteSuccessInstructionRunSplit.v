From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.

Import ListNotations.

Lemma islaInstructionRun_split firstCount secondCount before segments after :
  IslaInstructionRun (firstCount + secondCount) before segments after ->
  exists first middle second,
    segments = first ++ second /\
    IslaInstructionRun firstCount before first middle /\
    IslaInstructionRun secondCount middle second after.
Proof.
  revert before segments after.
  induction firstCount as [|firstCount IH]; intros before segments after Hrun.
  - cbn in Hrun. exists [], before, segments. repeat split; try assumption.
    constructor.
  - cbn in Hrun. inversion Hrun as
      [|count before' observations middle rest after' Hsegment Hrest]; subst.
    destruct (IH _ _ _ Hrest) as (first & splitState & second & -> & Hfirst & Hsecond).
    exists (observations :: first), splitState, second.
    split; first reflexivity. split.
    + econstructor; eassumption.
    + exact Hsecond.
Qed.

Print Assumptions islaInstructionRun_split.
