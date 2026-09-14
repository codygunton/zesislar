Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.CodeLookup.
Require Import InstrSpecs.Lookup.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeCode.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsPriorityBranchContinuation WriteSuccessExactTransactionsPresentFeeGasContinuation
  WriteSuccessExactTransactionsPriorityGasJoin WriteSuccessExactTransactionsPriorityToBoolean
  WriteSuccessExactTransactionsGasPriceToPriority WriteSuccessExactTransactionsPriorityValueToGasLimit
  WriteSuccessExactTransactionsPriority WriteSuccessExactTransactionsGasLimitCall
  WriteSuccessExactBooleanSpec WriteSuccessExactEncoderU128 WriteSuccessObservation WriteSuccessOutputSemantic.

Definition transactionPriorityGasTrace (sp tag low high value : bv 64) tail : spec :=
  let gas := writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
    (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned value))) tail in
  if bool_decide (tag = BV 64 0) then
    writeOutputEvents (sp - BV 64 9)%bv (BV 64 1) (writeSuccessBooleanWordPayload (BV 64 0)) gas
  else writeOutputEvents (sp - BV 64 9)%bv (BV 64 1) (writeSuccessBooleanWordPayload (BV 64 1))
    (writeOutputEvents (sp - BV 64 32)%bv (BV 64 16) (writeSuccessU128WordsPayload low high) gas).

Lemma transactions_priority_gas_region_correct `{!islaG Sigma} `{!threadG}
    (sp gaslow gashigh tag low high value : bv 64) tail (P : iProp Sigma) :
  ([∗ list] i ∈ IslaTraces.write_success_38.instrs.instr_map, instr i.1 (Some i.2))%I -∗
  ([∗ list] i ∈ IslaTraces.write_success_39.instrs.instr_map, instr i.1 (Some i.2))%I -∗
  ([∗ list] i ∈ IslaTraces.write_success_42.instrs.instr_map, instr i.1 (Some i.2))%I -∗
  ([∗ list] i ∈ IslaTraces.write_success_03.instrs.instr_map, instr i.1 (Some i.2))%I -∗
  ([∗ list] i ∈ IslaTraces.write_success_40.instrs.instr_map, instr i.1 (Some i.2))%I -∗
  ([∗ list] i ∈ IslaTraces.write_success_127.instrs.instr_map, instr i.1 (Some i.2))%I -∗
  ([∗ list] i ∈ IslaTraces.write_success_41.instrs.instr_map, instr i.1 (Some i.2))%I -∗
  ([∗ list] i ∈ IslaTraces.write_success_43.instrs.instr_map, instr i.1 (Some i.2))%I -∗
  ([∗ list] i ∈ IslaTraces.write_success_07.instrs.instr_map, instr i.1 (Some i.2))%I -∗
  ([∗ list] i ∈ IslaTraces.write_success_01.instrs.instr_map, instr i.1 (Some i.2))%I -∗
  □ instr_pre 0x15154 (transactionGasLimitPost sp value tail
    (transactionFeeGasLimitFrame sp gaslow gashigh tag low high P)) -∗
  □ instr_pre 0x15118 (transactionPriorityBranchState tag
    (transactionGasPricePriorityFrame sp gaslow gashigh
      (transactionPriorityGasTrace sp tag low high value tail)
      ("x9" ↦ᵣ RVal_Bits low ∗ "x23" ↦ᵣ RVal_Bits high ∗
       ("x26" ↦ᵣ RVal_Bits value ∗ P ∗ True) ∗ True))).
Proof.
  iIntros "#Hbranch #Hsome #Hnone #Hbool #Hfee #Hu128 #Hjoin #Hgas #Hint #Houtput #Hnext".
  iPoseProof (transactions_present_fee_gas_continuation sp gaslow gashigh tag low high value tail P
    with "Hfee Hu128 Hjoin Hgas Hint Houtput Hnext") as "#HsomeNext".
  iPoseProof (transactions_absent_fee_gas_continuation sp gaslow gashigh tag low high value tail P
    with "Hgas Hint Houtput Hnext") as "#HnoneNext".
  iAssert (□ instr_pre 0x15148 (encoderBooleanExactPost (BV 64 0) sp (BV 64 0x15148)
    (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
      (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned value))) tail)
    (transactionPriorityBooleanCallerFrame sp gaslow gashigh tag
      ("x9" ↦ᵣ RVal_Bits low ∗ "x23" ↦ᵣ RVal_Bits high ∗
       ("x26" ↦ᵣ RVal_Bits value ∗ P ∗ True) ∗ True))))%I as "#HnoneCommon".
  { iModIntro. iApply (instr_pre_wand 0x15148 0x15148 true true with "HnoneNext"); [done | done |].
    iIntros "Hpost". iApply (transactions_priority_boolean_frame_permutation with "Hpost"). }
  unfold transactionPriorityGasTrace.
  iApply (transactions_priority_branch_continuation with
    "Hbranch Hsome Hnone Hbool Houtput HsomeNext HnoneCommon").
Qed.
Print Assumptions transactions_priority_gas_region_correct.
Lemma transactions_priority_gas_native_pre `{!islaG Sigma} `{!threadG}
    (sp gaslow gashigh tag low high value : bv 64) tail (P : iProp Sigma) :
  writeSuccessCompleteNativeCode -∗
  □ instr_pre 0x15154 (transactionGasLimitPost sp value tail
    (transactionFeeGasLimitFrame sp gaslow gashigh tag low high P)) -∗
  □ instr_pre 0x15118 (transactionPriorityBranchState tag
    (transactionGasPricePriorityFrame sp gaslow gashigh
      (transactionPriorityGasTrace sp tag low high value tail)
      ("x9" ↦ᵣ RVal_Bits low ∗ "x23" ↦ᵣ RVal_Bits high ∗
       ("x26" ↦ᵣ RVal_Bits value ∗ P ∗ True) ∗ True))).
Proof.
  iIntros "#Hcode #Hnext".
  iEval (rewrite /writeSuccessCompleteNativeCode) in "Hcode".
  iDestruct "Hcode" as "#(Hprologue & Hlookup & Hmain & Houtput & Hmemcpy & Hboolean & Hoptional & HbyteLists & Hbytes & Hint & Hu256 & Hu128)".
  iApply (transactions_priority_gas_region_correct with
    "[] [] [] Hboolean [] Hu128 [] [] Hint Houtput Hnext").
  all: iApply instr_lookup_collect; last iExact "Hlookup".
  all: repeat constructor; reflexivity.
Qed.
Print Assumptions transactions_priority_gas_native_pre.
