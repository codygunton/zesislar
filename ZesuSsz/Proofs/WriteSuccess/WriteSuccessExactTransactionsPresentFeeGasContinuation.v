Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsBooleanToPriorityValue WriteSuccessExactTransactionsPriorityValueToGasLimit
  WriteSuccessExactTransactionsPriorityToBoolean WriteSuccessExactTransactionsGasLimitCall
  WriteSuccessExactBooleanSpec WriteSuccessExactEncoderU128 WriteSuccessObservation WriteSuccessOutputSemantic.

Lemma transactions_present_fee_gas_continuation `{!islaG Sigma} `{!threadG}
    (sp gaslow gashigh tag low high value : bv 64) tail (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_40.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_127.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_41.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_43.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15154 (transactionGasLimitPost sp value tail
    (transactionFeeGasLimitFrame sp gaslow gashigh tag low high P)) -∗
  □ instr_pre 0x15128 (encoderBooleanExactPost (BV 64 1) sp (BV 64 0x15128)
    (writeOutputEvents (sp - BV 64 32)%bv (BV 64 16) (writeSuccessU128WordsPayload low high)
      (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
        (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned value))) tail))
    (transactionPriorityBooleanCallerFrame sp gaslow gashigh tag
      ("x9" ↦ᵣ RVal_Bits low ∗ "x23" ↦ᵣ RVal_Bits high ∗
       ("x26" ↦ᵣ RVal_Bits value ∗ P ∗ True) ∗ True))).
Proof.
  iIntros "#Hfee #Hu128 #Hjoin #Hgas #Hint #Houtput #Hnext".
  iPoseProof (transactions_fee_gas_continuation sp gaslow gashigh tag low high value tail P
    with "Hjoin Hgas Hint Houtput Hnext") as "#HfeeNext".
  iApply (transactions_boolean_fee_continuation sp gaslow gashigh tag low high
    (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
      (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned value))) tail)
    ("x26" ↦ᵣ RVal_Bits value ∗ P ∗ True)%I with "Hfee Hu128 Houtput HfeeNext").
Qed.
Print Assumptions transactions_present_fee_gas_continuation.
