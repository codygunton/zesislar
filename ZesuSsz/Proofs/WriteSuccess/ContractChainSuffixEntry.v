Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  Interfaces WriteSuccessNativeContract WriteSuccessRepresentation
  WriteSuccessNativeCode WriteSuccessSuffixHashesEntryResources Contract
  ContractChainPostWithdrawals.

(** The 0x15744 premise uses the suffix-entry predicate.
    The frozen post-withdrawals exit uses writeSuccessSuffixHashesBoundary.
    The first wand is a translated segment hypothesis; its adapter is open. *)
Lemma draft_contract_from_suffix_entry
    `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded) (P : iProp Sigma)
    (pointer : bv 64) (base : Z)
    (total processed remaining : nat) (bytes : list (bv 8))
    (tail : spec) (Hwf : writeSuccessWitnessWellFormed args witness) :
  writeSuccessCompleteNativeCode -∗
  □ (instr_body 0x15744
       (writeSuccessSuffixHashesEntryPostSpec (writeSuccessFrameSp witness)
         (Z_to_bv 64 (Z.of_nat (S remaining))) remaining tail
         (writeSuccessSuffixHashesEntryFrame (writeSuccessFrameSp witness)
           pointer base total processed remaining bytes tail P)) -∗
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
        pointer base total processed remaining bytes tail P)) -∗
  instr_body 0x14d30
    (write_success_prologue_entry
      (writeSuccessEntrySp witness) (writeSuccessDecodedPointer witness)
      (writeSuccessReturnValue witness)
      (writeSuccessSavedS0 witness) (writeSuccessSavedS1 witness)
      (writeSuccessSavedS2 witness) (writeSuccessSavedS3 witness)
      (writeSuccessSavedS4 witness) (writeSuccessSavedS5 witness)
      (writeSuccessSavedS6 witness) (writeSuccessSavedS7 witness)
      (writeSuccessSavedS8 witness) (writeSuccessSavedS9 witness)
      (writeSuccessSavedS10 witness) (writeSuccessSavedS11 witness)
      (writeSuccessProloguePayload witness ∗ P)).
Proof.
  iIntros "#Hcode #HpostSegment #HsuffixEntry".
  iAssert (□ instr_pre 0x156e8
      (writeSuccessExactPostWithdrawalsBoundary
        (writeSuccessFrameSp witness)
        (bv_unsigned (writeSuccessWithdrawalsBase witness))
        (writeSuccessWithdrawalsBytes witness)
        (writeSuccessExactPostWithdrawalsEvents witness)
        (writeSuccessExactPostWithdrawalsCallerFrame args witness ∗ P)))%I
    with "[]" as "#Hpost".
  { iModIntro. iApply instr_pre_to_body. iNext.
    iApply "HpostSegment".
    iApply instr_pre_to_body. iNext. iExact "HsuffixEntry". }
  iPoseProof (draft_tail_from_post_withdrawals args witness P Hwf
    with "Hcode Hpost") as "#Htail".
  iApply (write_success_contract_from_tail args witness P Hwf
    with "Hcode Htail").
Qed.

Print Assumptions draft_contract_from_suffix_entry.

(** This pair records the three open segment premises without closing their
    boundary adapters. The 0x15744, 0x1596c, and scratch gaps stay explicit. *)
