Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
From ZesuSsz.Proofs.WriteSuccess Require Import
  Interfaces WriteSuccessNativeCode WriteSuccessNativeContract
  WriteSuccessRepresentation WriteSuccessExactSuffixHashesLoopSpec
  WriteSuccessSuffixHashesEntryResources Contract
  ContractChainTailSecond ContractChainSuffixEntry.

(** The TF2 wand below is a translated hypothesis.
    The frozen TF2 draft has code and call premises and fixes its tail.
    The 0x15744, 0x1596c, and scratch adapters remain open. *)
Lemma draft_open_segment_chain
    `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded) (P : iProp Sigma)
    (pointer sp data size : bv 64) (base hashBase : Z)
    (total processed remaining : nat)
    (source hashBytes bytes : list (bv 8))
    (tail : spec) (Hwf : writeSuccessWitnessWellFormed args witness) :
  writeSuccessCompleteNativeCode -∗
  □ (instr_body 0x15744
       (writeSuccessSuffixHashesEntryPostSpec (writeSuccessFrameSp witness)
         (Z_to_bv 64 (Z.of_nat (S remaining))) remaining tail
         (writeSuccessSuffixHashesEntryFrame (writeSuccessFrameSp witness)
           pointer base total processed remaining source tail P)) -∗
     instr_body 0x156e8
       (writeSuccessExactPostWithdrawalsBoundary
         (writeSuccessFrameSp witness)
         (bv_unsigned (writeSuccessWithdrawalsBase witness))
         (writeSuccessWithdrawalsBytes witness)
         (writeSuccessExactPostWithdrawalsEvents witness)
         (writeSuccessExactPostWithdrawalsCallerFrame args witness ∗ P))) -∗
  □ instr_pre 0x15744
    (writeSuccessSuffixHashesEntryPostSpec (writeSuccessFrameSp witness)
      (Z_to_bv 64 (Z.of_nat (S remaining))) remaining tail
      (writeSuccessSuffixHashesEntryFrame (writeSuccessFrameSp witness)
        pointer base total processed remaining source tail P)) -∗
  □ (instr_body 0x1596c
       (writeSuccessTailFirstBranchBoundary (fun _ => P)) -∗
     instr_body 0x158e0
       (writeSuccessExactTailFieldsEntryBoundary sp data size (BV 64 0)
         (Z_to_bv 64 (hashBase + Z.of_nat (length hashBytes))) bytes tail
         (hashBase ↦ₘ∗ hashBytes ∗ P))) -∗
  □ (instr_body 0x1596c
       (writeSuccessExactTailFirstBranchState args witness tail) -∗
     instr_body 0x1596c
       (writeSuccessTailFirstBranchBoundary (fun _ => P))) -∗
  □ (instr_body 0x159b8
       (writeSuccessExactTailSecondBranchState args witness) -∗
     instr_body 0x1596c
       (writeSuccessExactTailFirstBranchState args witness tail)) -∗
  □ (instr_body 0x158e0
       (writeSuccessExactTailFieldsEntryBoundary sp data size (BV 64 0)
         (Z_to_bv 64 (hashBase + Z.of_nat (length hashBytes))) bytes tail
         (hashBase ↦ₘ∗ hashBytes ∗ P)) -∗
     instr_body 0x158e0
       (writeSuccessExactTailFieldsEntryBoundary sp data size (BV 64 0)
         (Z_to_bv 64 (hashBase + Z.of_nat (length hashBytes))) bytes tail
         (hashBase ↦ₘ∗ hashBytes ∗ suffixLoopScratch sp ∗ P))) -∗
  □ instr_pre 0x15bc8 encoderOptionalEntryBoundary -∗
  □ instr_pre 0x15c10 encoderByteListsEntryBoundary -∗
  (instr_body 0x14d30
     (write_success_prologue_entry
       (writeSuccessEntrySp witness) (writeSuccessDecodedPointer witness)
       (writeSuccessReturnValue witness)
       (writeSuccessSavedS0 witness) (writeSuccessSavedS1 witness)
       (writeSuccessSavedS2 witness) (writeSuccessSavedS3 witness)
       (writeSuccessSavedS4 witness) (writeSuccessSavedS5 witness)
       (writeSuccessSavedS6 witness) (writeSuccessSavedS7 witness)
       (writeSuccessSavedS8 witness) (writeSuccessSavedS9 witness)
       (writeSuccessSavedS10 witness) (writeSuccessSavedS11 witness)
       (writeSuccessProloguePayload witness ∗ P)) ∗
   instr_body 0x158e0
     (writeSuccessExactTailFieldsEntryBoundary sp data size (BV 64 0)
       (Z_to_bv 64 (hashBase + Z.of_nat (length hashBytes))) bytes tail
       (hashBase ↦ₘ∗ hashBytes ∗ suffixLoopScratch sp ∗ P))).
Proof.
  iIntros "#Hcode #HpostSegment #HsuffixEntry #Hfirst".
  iIntros "#HbranchAdapter #Hsecond #Hscratch #Hoptional #Hlists".
  iPoseProof (write_success_native_main_code with "Hcode") as "#HmainCode".
  iEval (rewrite /writeSuccessNativeMainCode) in "HmainCode".
  iDestruct "HmainCode" as "(#Hlookup & #Hspec & _)".
  iSplit.
  - iApply (draft_contract_from_suffix_entry args witness P pointer base
      total processed remaining source tail Hwf
      with "Hcode HpostSegment HsuffixEntry").
  - iApply "Hscratch". iApply "Hfirst". iApply "HbranchAdapter".
    iApply (draft_tail_second_through_epilogue args witness tail
      with "Hlookup Hoptional Hlists Hsecond").
Qed.

Print Assumptions draft_open_segment_chain.
