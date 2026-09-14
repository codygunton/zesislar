Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsPriority WriteSuccessExactTransactionsPriorityBooleanCall
  WriteSuccessExactTransactionsPriorityToBoolean WriteSuccessExactTransactionsGasPriceToPriority
  WriteSuccessExactBooleanSpec.

Lemma transactions_priority_branch_continuation `{!islaG Sigma} `{!threadG}
    (sp low high tag : bv 64) someTail noneTail (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_38.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_39.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_42.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_03.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15128 (encoderBooleanExactPost (BV 64 1) sp (BV 64 0x15128)
    someTail (transactionPriorityBooleanCallerFrame sp low high tag P)) -∗
  □ instr_pre 0x15148 (encoderBooleanExactPost (BV 64 0) sp (BV 64 0x15148)
    noneTail (transactionPriorityBooleanCallerFrame sp low high tag P)) -∗
  □ instr_pre 0x15118 (transactionPriorityBranchState tag
    (transactionGasPricePriorityFrame sp low high
      (if bool_decide (tag = BV 64 0) then
        writeOutputEvents (sp - BV 64 9)%bv (BV 64 1) (writeSuccessBooleanWordPayload (BV 64 0)) noneTail
       else writeOutputEvents (sp - BV 64 9)%bv (BV 64 1) (writeSuccessBooleanWordPayload (BV 64 1)) someTail) P)).
Proof.
  iIntros "#Hbranch #Hsome #Hnone #Hboolean #Houtput #HsomeNext #HnoneNext".
  iPoseProof (transactions_priority_boolean_call_correct true sp (BV 64 0x15118)
    (sp - BV 64 32)%bv (BV 64 0x2401a0b8) (BV 64 16) someTail
    (transactionPriorityBooleanCallerFrame sp low high tag P)
    with "Hsome Hboolean Houtput") as "HsomeBody".
  iPoseProof (transactions_priority_boolean_call_correct false sp (BV 64 0x15118)
    (sp - BV 64 32)%bv (BV 64 0x2401a0b8) (BV 64 16) noneTail
    (transactionPriorityBooleanCallerFrame sp low high tag P)
    with "Hnone Hboolean Houtput") as "HnoneBody".
  iModIntro. iApply instr_pre_to_body. iNext.
  iApply (transactions_priority_branch_correct with "Hbranch").
  - iApply (instr_pre_wand 0x1511c 0x1511c false false with "HsomeBody"); [done | done |].
    iIntros "(Hstate & %Htag & _)".
    have Hchoice : bool_decide (tag = BV 64 0) = false by apply bool_decide_false.
    iEval (rewrite Hchoice) in "Hstate".
    iApply (transactions_priority_to_boolean true with "Hstate HsomeNext").
  - iApply (instr_pre_wand 0x1513c 0x1513c false false with "HnoneBody"); [done | done |].
    iIntros "(Hstate & %Htag & _)".
    have Hchoice : bool_decide (tag = BV 64 0) = true by apply bool_decide_true.
    iEval (rewrite Hchoice) in "Hstate".
    iApply (transactions_priority_to_boolean false with "Hstate HnoneNext").
Qed.
Print Assumptions transactions_priority_branch_continuation.
