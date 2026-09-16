Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.CallScratchBoolean.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsPriorityToBoolean WriteSuccessExactTransactionsPriorityValueCall
  WriteSuccessExactTransactionsGasPriceCall WriteSuccessExactBooleanSpec WriteSuccessExactEncoderU128.

Definition transactionPriorityValueCallerFrame `{!islaG Sigma} `{!threadG}
    (sp gaslow gashigh tag : bv 64) (P : iProp Sigma) : iProp Sigma :=
  ("x27" ↦ᵣ RVal_Bits tag ∗ transactionGasPriceFrame sp gaslow gashigh P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionPriorityValueCallerFrame) := I.

Lemma transactions_boolean_to_priority_value `{!islaG Sigma} `{!threadG}
    (sp gaslow gashigh tag low high : bv 64) tail (P : iProp Sigma) :
  encoderBooleanExactPost (BV 64 1) sp (BV 64 0x15128)
    (writeOutputEvents (sp - BV 64 32)%bv (BV 64 16)
      (writeSuccessU128WordsPayload low high) tail)
    (transactionPriorityBooleanCallerFrame sp gaslow gashigh tag
      ("x9" ↦ᵣ RVal_Bits low ∗ "x23" ↦ᵣ RVal_Bits high ∗ P ∗ True)) -∗
  instr_pre 0x15138 (transactionPriorityValuePost sp low high tail
    (transactionPriorityValueCallerFrame sp gaslow gashigh tag P)) -∗
  transactionPriorityValueEntry sp low high (BV 64 0x15128) (BV 64 (mapIoContextAddress defaultMap)) tail
    (transactionPriorityValueCallerFrame sp gaslow gashigh tag P).
Proof.
  iIntros "Hpost Hnext".
  iDestruct "Hpost" as "(Hsys & H1 & Hsp & Hret & Hreturned & _)".
  iDestruct "Hreturned" as "(H5 & H10 & H11 & Hpayload & Hgap & Hmmio & Htrace & Hcaller & _)".
  iDestruct "Hcaller" as "(Htag & Hlower & Hsource & _)".
  iDestruct "Hsource" as "(HgasHigh & HgasLow & %Halign & %Hlow & %Hhigh & Hfee & _)".
  iDestruct "Hfee" as "(Hlowword & Hhighword & HP & _)".
  have Haddress : bv_unsigned (sp - BV 64 9)%bv = bv_unsigned sp - 9.
  { clear -Hlow. bv_solve. }
  iEval (rewrite /writeSuccessBooleanWordPayload mem_mapsto_array_singleton Haddress) in "Hpayload".
  iPoseProof (call_boolean_scratch_reuse sp (BV 64 0x15128) _
    with "[$Hgap $Hpayload $Hret]") as "Hupper".
  iAssert ((bv_unsigned sp - 32) ↦ₘ? 32)%I with "[Hlower Hupper]" as "Hscratch".
  { iApply (mem_mapsto_uninit_combine 16 with "Hlower"); first lia.
    replace (bv_unsigned sp - 32 + 16)%Z with (bv_unsigned sp - 16)%Z by lia.
    iExact "Hupper". }
  iAssert (reg_col [(KindReg "x10", BitsShape 64); (KindReg "x11", BitsShape 64)])%I
    with "[H10 H11]" as "Hargs".
  { rewrite !reg_col_cons reg_col_nil. iSplitL "H10"; first (iExists _; iFrame; done).
    iSplitL "H11"; last done. iExists _; iFrame; done. }
  unfold transactionPriorityValueEntry, transactionPriorityValueCallerFrame, transactionGasPriceFrame.
  iFrame. repeat iSplit; done.
Qed.
Print Assumptions transactions_boolean_to_priority_value.
Lemma transactions_boolean_fee_continuation `{!islaG Sigma} `{!threadG}
    (sp gaslow gashigh tag low high : bv 64) tail (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_40.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_127.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15138 (transactionPriorityValuePost sp low high tail
    (transactionPriorityValueCallerFrame sp gaslow gashigh tag P)) -∗
  □ instr_pre 0x15128 (encoderBooleanExactPost (BV 64 1) sp (BV 64 0x15128)
    (writeOutputEvents (sp - BV 64 32)%bv (BV 64 16)
      (writeSuccessU128WordsPayload low high) tail)
    (transactionPriorityBooleanCallerFrame sp gaslow gashigh tag
      ("x9" ↦ᵣ RVal_Bits low ∗ "x23" ↦ᵣ RVal_Bits high ∗ P ∗ True))).
Proof.
  iIntros "#Hcaller #Hu128 #Houtput #Hnext".
  iPoseProof (transactions_priority_value_call_correct sp low high (BV 64 0x15128)
    (BV 64 (mapIoContextAddress defaultMap)) tail (transactionPriorityValueCallerFrame sp gaslow gashigh tag P)
    with "Hcaller Hu128 Houtput") as "Hcallee".
  iModIntro. iApply (instr_pre_wand 0x15128 0x15128 false true with "Hcallee"); [done | done |].
  iIntros "Hpost". iApply (transactions_boolean_to_priority_value with "Hpost Hnext").
Qed.
Print Assumptions transactions_boolean_fee_continuation.
