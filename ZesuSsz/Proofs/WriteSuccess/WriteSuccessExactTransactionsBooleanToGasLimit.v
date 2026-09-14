Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.CallScratchBoolean.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsPriorityToBoolean WriteSuccessExactTransactionsGasLimitCall
  WriteSuccessExactTransactionsGasPriceCall WriteSuccessExactBooleanSpec
  WriteSuccessObservation WriteSuccessOutputSemantic.

Definition transactionGasLimitCallerFrame `{!islaG Sigma} `{!threadG}
    (sp low high tag : bv 64) (P : iProp Sigma) : iProp Sigma :=
  ("x27" ↦ᵣ RVal_Bits tag ∗ (bv_unsigned sp - 32) ↦ₘ? 16 ∗
   transactionGasPriceFrame sp low high P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionGasLimitCallerFrame) := I.

Lemma transactions_boolean_to_gas_limit `{!islaG Sigma} `{!threadG}
    (sp low high tag value : bv 64) tail (P : iProp Sigma) :
  encoderBooleanExactPost (BV 64 0) sp (BV 64 0x15148)
    (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
      (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned value))) tail)
    (transactionPriorityBooleanCallerFrame sp low high tag
      ("x26" ↦ᵣ RVal_Bits value ∗ P ∗ True)) -∗
  instr_pre 0x15154 (transactionGasLimitPost sp value tail
    (transactionGasLimitCallerFrame sp low high tag P)) -∗
  transactionGasLimitEntry sp value (BV 64 0x15148) (BV 64 (mapIoContextAddress defaultMap)) (BV 64 1) tail
    (transactionGasLimitCallerFrame sp low high tag P).
Proof.
  iIntros "Hpost Hnext".
  iDestruct "Hpost" as "(Hsys & H1 & Hsp & Hret & Hreturned & _)".
  iDestruct "Hreturned" as "(H5 & H10 & H11 & Hpayload & Hgap & Hmmio & Htrace & Hcaller & _)".
  iDestruct "Hcaller" as "(Htag & Hlower & Hsource & _)".
  iDestruct "Hsource" as "(Hhighword & Hlowword & %Halign & %Hlow & %Hhigh & Hvalue & _)".
  iDestruct "Hvalue" as "(H26 & HP & _)".
  have Haddress : bv_unsigned (sp - BV 64 9)%bv = bv_unsigned sp - 9.
  { clear -Hlow. bv_solve. }
  iEval (rewrite /writeSuccessBooleanWordPayload mem_mapsto_array_singleton Haddress) in "Hpayload".
  iPoseProof (call_boolean_scratch_reuse sp (BV 64 0x15148) _
    with "[$Hgap $Hpayload $Hret]") as "Hscratch".
  iAssert (reg_col [(KindReg "x10", BitsShape 64)])%I with "[H10]" as "Harg".
  { rewrite reg_col_cons reg_col_nil. iSplitL "H10"; last done. iExists _; iFrame; done. }
  unfold transactionGasLimitEntry, transactionGasLimitCallerFrame, transactionGasPriceFrame.
  iFrame. repeat iSplit; try done; iPureIntro; lia.
Qed.
Print Assumptions transactions_boolean_to_gas_limit.
Lemma transactions_boolean_gas_continuation `{!islaG Sigma} `{!threadG}
    (sp low high tag value : bv 64) tail (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_43.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15154 (transactionGasLimitPost sp value tail
    (transactionGasLimitCallerFrame sp low high tag P)) -∗
  □ instr_pre 0x15148 (encoderBooleanExactPost (BV 64 0) sp (BV 64 0x15148)
    (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
      (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned value))) tail)
    (transactionPriorityBooleanCallerFrame sp low high tag
      ("x26" ↦ᵣ RVal_Bits value ∗ P ∗ True))).
Proof.
  iIntros "#Hcaller #Hint #Houtput #Hnext".
  iPoseProof (transactions_gas_limit_call_correct sp value (BV 64 0x15148)
    (BV 64 (mapIoContextAddress defaultMap)) (BV 64 1) tail (transactionGasLimitCallerFrame sp low high tag P)
    with "Hcaller Hint Houtput") as "Hcallee".
  iModIntro. iApply (instr_pre_wand 0x15148 0x15148 false true with "Hcallee"); [done | done |].
  iIntros "Hpost". iApply (transactions_boolean_to_gas_limit with "Hpost Hnext").
Qed.
Print Assumptions transactions_boolean_gas_continuation.
