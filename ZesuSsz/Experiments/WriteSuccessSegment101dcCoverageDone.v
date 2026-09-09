(* Generated from the pinned return trace shape. *)
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101dc.

Lemma segment_101dc_done_covered regs global (ra : bv 64)
    prefix11 done labels spawned after :
  IslaInstructionPrefixPath
    (writeSuccess15694Local (writeSuccess101dcTrace11 ra)
      (writeSuccess101dcRegs regs ra), global) prefix11 done ->
  done.1.(seq_trace) = tnil ->
  seq_step done.1 done.2 labels after.1 after.2 spawned ->
  after = writeSuccess101dcAfter regs global ra /\
  prefix11 ++ ({| microLabels := labels; microAfter := after |} :: []) =
    [({| microLabels := writeSuccess101dcDoneLabels global ra;
         microAfter := writeSuccess101dcAfter regs global ra |})].
Proof.
  intros Hprefix Hnil Hdone. inversion Hprefix; subst; last contradiction.
  destruct (global.(seq_instrs) !! writeSuccess101dcTarget ra)
    as [targetTrace|] eqn:Htarget.
  - eapply writeSuccessDoneTabledCovered in Hdone.
    2: reflexivity.
    2: { unfold writeSuccess101dcRegs. rewrite lookup_insert. reflexivity. }
    2: exact Htarget.
    destruct Hdone as (-> & HafterLocal & HafterGlobal & ->).
    destruct after as [afterLocal afterGlobal]. cbn in *.
    subst afterLocal afterGlobal.
    unfold writeSuccess101dcAfter,
      writeSuccess101dcDoneLabels. rewrite Htarget. split; reflexivity.
  - eapply writeSuccessDoneTrapCovered in Hdone.
    2: reflexivity.
    2: { unfold writeSuccess101dcRegs. rewrite lookup_insert. reflexivity. }
    2: exact Htarget.
    destruct Hdone as (-> & HafterLocal & HafterGlobal & ->).
    destruct after as [afterLocal afterGlobal]. cbn in *.
    subst afterLocal afterGlobal.
    unfold writeSuccess101dcAfter,
      writeSuccess101dcDoneLabels. rewrite Htarget. split; reflexivity.
Qed.
Print Assumptions segment_101dc_done_covered.
