Require Import ZesuSsz.Automation.All.
From Coq Require Import Lia Arith.Wf_nat.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Executor.
Require Import ZesuSsz.Export.WriteSuccessControl.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Generated.Level1.

Open Scope list_scope.

(** This theorem consumes the rank obligation. It does not prove that obligation. *)
Lemma writeSuccess_rank_completed_run inputSize control remaining rank :
  WriteSuccessFuelInvariant inputSize control remaining rank ->
  forall theta sigma,
    control theta sigma ->
    exists instructions labels finish memory pc,
      (instructions <= S (rank theta sigma))%nat /\
      CompletedInstructionRun instructions theta sigma labels finish memory /\
      seq_regs finish !! "PC" = Some (RVal_Bits (Z_to_bv 64 pc)) /\
      PcInList writeSuccessExitPcs pc.
Proof.
  intros [_ [Hprogress [Hclosed Hdecreases]]].
  assert (Hbounded : forall bound theta sigma,
    rank theta sigma = bound -> control theta sigma ->
    exists instructions labels finish memory pc,
      (instructions <= S bound)%nat /\
      CompletedInstructionRun instructions theta sigma labels finish memory /\
      seq_regs finish !! "PC" = Some (RVal_Bits (Z_to_bv 64 pc)) /\
      PcInList writeSuccessExitPcs pc).
  { intros bound. induction bound using lt_wf_ind.
    intros theta sigma Hrank Hcontrol.
    destruct (Hprogress theta sigma Hcontrol) as [prefix [next [nextMemory Hstep]]].
    destruct (Hclosed theta sigma prefix next nextMemory Hcontrol Hstep)
      as [Hnext | [pc [Hpc Hexit]]].
    - assert (Hlt : (rank next nextMemory < bound)%nat).
      { rewrite <- Hrank. eapply Hdecreases; eassumption. }
      destruct (H _ Hlt next nextMemory eq_refl Hnext)
        as [count [tail [finish [memory [pc [Hcount [Hrun [Hpc Hexit]]]]]]]].
      exists (S count), (prefix ++ tail), finish, memory, pc.
      split; [lia|]. split; [econstructor; eassumption|]. auto.
    - exists 1%nat, prefix, next, nextMemory, pc.
      split; [lia|]. split; [|auto].
      replace prefix with (prefix ++ []) by apply app_nil_r.
      econstructor; [exact Hstep|constructor]. }
  intros theta sigma Hcontrol.
  exact (Hbounded (rank theta sigma) theta sigma eq_refl Hcontrol).
Qed.

Theorem writeSuccess_fuel_invariant_terminates inputSize control remaining rank
    theta sigma :
  WriteSuccessFuelInvariant inputSize control remaining rank ->
  control theta sigma ->
  exists instructions labels finish memory pc,
    (instructions <= writeSuccessFuelBound inputSize)%nat /\
    CompletedInstructionRun instructions theta sigma labels finish memory /\
    seq_regs finish !! "PC" = Some (RVal_Bits (Z_to_bv 64 pc)) /\
    PcInList writeSuccessExitPcs pc.
Proof.
  intros Hinvariant Hcontrol.
  destruct (writeSuccess_rank_completed_run _ _ _ _ Hinvariant theta sigma Hcontrol)
    as [count [labels [finish [memory [pc [Hcount Hrun]]]]]].
  destruct Hinvariant as [Hbound _].
  destruct (Hbound theta sigma Hcontrol)
    as [_ [transactions [withdrawals [headers [bytes [_ [_ Hrank]]]]]]].
  exists count, labels, finish, memory, pc. split; [lia|exact Hrun].
Qed.

Print Assumptions writeSuccess_rank_completed_run.
Print Assumptions writeSuccess_fuel_invariant_terminates.
