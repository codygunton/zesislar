Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsPriorityToBoolean WriteSuccessExactBooleanSpec WriteSuccessObservation WriteSuccessOutputSemantic.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsBooleanToGasLimit WriteSuccessExactTransactionsPriorityValueToGasLimit
  WriteSuccessExactTransactionsGasPriceCall WriteSuccessExactTransactionsGasLimitCall
  WriteSuccessExactEncoderIntFramedCall.

Lemma transactions_absent_gas_frame_pack `{!islaG Sigma} `{!threadG}
    (sp gaslow gashigh tag low high value : bv 64) tail (P : iProp Sigma) :
  transactionGasLimitPost sp value tail (transactionGasLimitCallerFrame sp gaslow gashigh tag
    ("x9" ↦ᵣ RVal_Bits low ∗ "x23" ↦ᵣ RVal_Bits high ∗ P ∗ True)) -∗
  transactionGasLimitPost sp value tail (transactionFeeGasLimitFrame sp gaslow gashigh tag low high P).
Proof.
  iIntros "Hpost".
  iDestruct "Hpost" as "(Hsys & H1 & Hsp & H5 & H10 & H11 & Hscratch & Hmmio & Htrace & Hlimit & _)".
  iDestruct "Hlimit" as "(Hvalue & %Halign & %Hlow & %Hhigh & Hcaller & _)".
  iDestruct "Hcaller" as "(Htag & Hlower & Hgas & _)".
  iDestruct "Hgas" as "(HgasHigh & HgasLow & %HgasAlign & %HgasLow & %HgasHigh & Hfee & _)".
  iDestruct "Hfee" as "(Hlowword & Hhighword & HP & _)".
  unfold transactionGasLimitPost, encoderIntExactFramedPost,
    transactionGasLimitFrame, transactionFeeGasLimitFrame, transactionGasPriceFrame.
  iFrame. repeat iSplit; done.
Qed.
Print Assumptions transactions_absent_gas_frame_pack.
Lemma transactions_absent_fee_gas_continuation `{!islaG Sigma} `{!threadG}
    (sp gaslow gashigh tag low high value : bv 64) tail (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_43.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15154 (transactionGasLimitPost sp value tail
    (transactionFeeGasLimitFrame sp gaslow gashigh tag low high P)) -∗
  □ instr_pre 0x15148 (encoderBooleanExactPost (BV 64 0) sp (BV 64 0x15148)
    (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
      (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned value))) tail)
    (transactionPriorityBooleanCallerFrame sp gaslow gashigh tag
      ("x26" ↦ᵣ RVal_Bits value ∗ ("x9" ↦ᵣ RVal_Bits low ∗ "x23" ↦ᵣ RVal_Bits high ∗ P ∗ True) ∗ True))).
Proof.
  iIntros "#Hgas #Hint #Houtput #Hnext".
  iAssert (□ instr_pre 0x15154 (transactionGasLimitPost sp value tail
    (transactionGasLimitCallerFrame sp gaslow gashigh tag
      ("x9" ↦ᵣ RVal_Bits low ∗ "x23" ↦ᵣ RVal_Bits high ∗ P ∗ True))))%I as "#HfalseNext".
  { iModIntro. iApply (instr_pre_wand 0x15154 0x15154 true true with "Hnext"); [done | done |].
    iIntros "Hpost". iApply (transactions_absent_gas_frame_pack with "Hpost"). }
  iApply (transactions_boolean_gas_continuation sp gaslow gashigh tag value tail
    ("x9" ↦ᵣ RVal_Bits low ∗ "x23" ↦ᵣ RVal_Bits high ∗ P ∗ True)%I
    with "Hgas Hint Houtput HfalseNext").
Qed.
Print Assumptions transactions_absent_fee_gas_continuation.
