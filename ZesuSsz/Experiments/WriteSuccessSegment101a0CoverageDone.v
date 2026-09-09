(* Generated from the pinned return trace shape. *)
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101a0.

Lemma segment_101a0_done_covered regs global (ra : bv 64)
    prefix11 done labels spawned after :
  IslaInstructionPrefixPath
    (writeSuccess15694Local (writeSuccess101a0Trace11 ra)
      (writeSuccess101a0Regs regs ra), global) prefix11 done ->
  done.1.(seq_trace) = tnil ->
  seq_step done.1 done.2 labels after.1 after.2 spawned ->
  after = writeSuccess101a0After regs global ra /\
  prefix11 ++ ({| microLabels := labels; microAfter := after |} :: []) =
    [({| microLabels := writeSuccess101a0DoneLabels global ra;
         microAfter := writeSuccess101a0After regs global ra |})].
Proof.
  intros Hprefix Hnil Hdone. inversion Hprefix; subst; last contradiction.
  destruct (global.(seq_instrs) !! writeSuccess101a0Target ra)
    as [targetTrace|] eqn:Htarget.
  - eapply writeSuccessDoneTabledCovered in Hdone.
    2: reflexivity.
    2: { unfold writeSuccess101a0Regs. rewrite lookup_insert. reflexivity. }
    2: exact Htarget.
    destruct Hdone as (-> & HafterLocal & HafterGlobal & ->).
    destruct after as [afterLocal afterGlobal]. cbn in *.
    subst afterLocal afterGlobal.
    unfold writeSuccess101a0After,
      writeSuccess101a0DoneLabels. rewrite Htarget. split; reflexivity.
  - eapply writeSuccessDoneTrapCovered in Hdone.
    2: reflexivity.
    2: { unfold writeSuccess101a0Regs. rewrite lookup_insert. reflexivity. }
    2: exact Htarget.
    destruct Hdone as (-> & HafterLocal & HafterGlobal & ->).
    destruct after as [afterLocal afterGlobal]. cbn in *.
    subst afterLocal afterGlobal.
    unfold writeSuccess101a0After,
      writeSuccess101a0DoneLabels. rewrite Htarget. split; reflexivity.
Qed.
Print Assumptions segment_101a0_done_covered.
