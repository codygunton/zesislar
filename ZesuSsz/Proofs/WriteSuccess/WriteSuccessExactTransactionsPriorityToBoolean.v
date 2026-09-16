Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsGasPriceToPriority WriteSuccessExactTransactionsGasPriceCall
  WriteSuccessExactTransactionsPriority WriteSuccessExactTransactionsPriorityBooleanCall
  WriteSuccessExactBooleanSpec.

Definition transactionPriorityBooleanCallerFrame `{!islaG Sigma} `{!threadG}
    (sp low high tag : bv 64) (P : iProp Sigma) : iProp Sigma :=
  ("x27" ↦ᵣ RVal_Bits tag ∗ (bv_unsigned sp - 32) ↦ₘ? 16 ∗
   transactionGasPriceFrame sp low high P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionPriorityBooleanCallerFrame) := I.

Lemma transactions_priority_to_boolean `{!islaG Sigma} `{!threadG}
    (present : bool) (sp low high tag : bv 64) tail (P : iProp Sigma) :
  transactionPriorityBranchState tag (transactionGasPricePriorityFrame sp low high
    (writeOutputEvents (sp - BV 64 9)%bv (BV 64 1)
      (writeSuccessBooleanWordPayload (if present then BV 64 1 else BV 64 0)) tail) P) -∗
  instr_pre (if present then 0x15128 else 0x15148)
    (encoderBooleanExactPost (if present then BV 64 1 else BV 64 0) sp
      (if present then BV 64 0x15128 else BV 64 0x15148) tail
      (transactionPriorityBooleanCallerFrame sp low high tag P)) -∗
  transactionPriorityBooleanEntry present sp (BV 64 0x15118) (sp - BV 64 32)%bv
    (BV 64 (mapIoContextAddress defaultMap)) (BV 64 16) tail
    (transactionPriorityBooleanCallerFrame sp low high tag P).
Proof.
  iIntros "Hstate Hnext".
  iDestruct "Hstate" as "(Hsys & Htag & Hframe & _)".
  iDestruct "Hframe" as "(Hsp & H1 & H5 & H10 & H11 & Hscratch & Hmmio & Htrace & Hsource & _)".
  iDestruct "Hsource" as "(Hhighword & Hlowword & %Halign & %Hlow & %Hhigh & HP & _)".
  iDestruct (mem_mapsto_uninit_split 16 with "Hscratch") as "[Hlower Hupper]"; first lia.
  iEval (replace (bv_unsigned sp - 32 + 16)%Z with (bv_unsigned sp - 16)%Z by lia) in "Hupper".
  unfold transactionPriorityBooleanEntry, encoderBooleanExactPrefixFrame,
    encoderBooleanExactFacts, transactionPriorityBooleanCallerFrame, transactionGasPriceFrame.
  destruct present;
    iFrame "Hsys H1 Hsp H10 Hupper H5 H11 Hmmio Htrace Hnext Htag Hlower Hhighword Hlowword HP";
    repeat iSplit; iPureIntro; first [assumption | bv_solve].
Qed.
Print Assumptions transactions_priority_to_boolean.
Lemma transactions_priority_boolean_continuation `{!islaG Sigma} `{!threadG}
    (present : bool) (sp low high tag : bv 64) tail (P : iProp Sigma) :
  ([∗ list] instruction ∈ (if present then IslaTraces.write_success_39.instrs.instr_map
    else IslaTraces.write_success_42.instrs.instr_map),
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_03.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre (if present then 0x15128 else 0x15148)
    (encoderBooleanExactPost (if present then BV 64 1 else BV 64 0) sp
      (if present then BV 64 0x15128 else BV 64 0x15148) tail
      (transactionPriorityBooleanCallerFrame sp low high tag P)) -∗
  □ instr_pre (if present then 0x1511c else 0x1513c)
    (transactionPriorityBranchState tag (transactionGasPricePriorityFrame sp low high
      (writeOutputEvents (sp - BV 64 9)%bv (BV 64 1)
        (writeSuccessBooleanWordPayload (if present then BV 64 1 else BV 64 0)) tail) P)).
Proof.
  iIntros "#Hcode #Hboolean #Houtput #Hnext".
  iPoseProof (transactions_priority_boolean_call_correct present sp (BV 64 0x15118)
    (sp - BV 64 32)%bv (BV 64 (mapIoContextAddress defaultMap)) (BV 64 16) tail
    (transactionPriorityBooleanCallerFrame sp low high tag P)
    with "Hcode Hboolean Houtput") as "Hcallee".
  iModIntro. iApply (instr_pre_wand (if present then 0x1511c else 0x1513c)
    (if present then 0x1511c else 0x1513c) false true with "Hcallee"); [done | done |].
  iIntros "Hstate". iApply (transactions_priority_to_boolean with "Hstate Hnext").
Qed.
Print Assumptions transactions_priority_boolean_continuation.
