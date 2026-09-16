Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactStorageKeysPairHandoff.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactBlobHashesLoads0 WriteSuccessExactBlobHashesPairs8Load0
  WriteSuccessExactBlobHashesRemainingShifts WriteSuccessExactBlobHashesShiftsHandoff
  WriteSuccessExactBlobHashesLowPairs WriteSuccessExactBlobHashesLowPairsHandoff
  WriteSuccessExactBlobHashesWide WriteSuccessExactBlobHashesWordAssembly.

Lemma blob_shift_assembly_correct `{!islaG Sigma} `{!threadG}
    row count base bytes index (P : iProp Sigma) :
  ([∗ list] instruction ∈ drop 2 IslaTraces.write_success_68.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ take 17 IslaTraces.write_success_69.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15538 (blobWidePost row count base bytes index P) -∗
  instr_body 0x1549c (blobLoads0Post row base bytes index (blobPairs8Carry count bytes index P)).
Proof.
  iStartProof. iIntros "#H68 #H69 Hnext".
  iPoseProof (blob_word_assembly_correct row count base bytes index P with "[] H69 Hnext") as "Hwords".
  { iApply (big_sepL_submseteq with "H68").
    change (drop 14 (drop 2 IslaTraces.write_success_68.instrs.instr_map) ⊆+ drop 2 IslaTraces.write_success_68.instrs.instr_map).
    apply sublist_submseteq, sublist_drop. }
  iAssert (instr_body 0x154d4 (blobRemainingShiftsPost (storageKeyByte bytes index 14) (storageKeyByte bytes index 15) (storageKeyByte bytes index 1) (storageKeyByte bytes index 2) (storageKeyByte bytes index 3) (storageKeyByte bytes index 5) (storageKeyByte bytes index 6) (storageKeyByte bytes index 7) (storageKeyByte bytes index 25) (storageKeyByte bytes index 26) (storageKeyByte bytes index 27) (storageKeyByte bytes index 29) (storageKeyByte bytes index 30) (storageKeyByte bytes index 31)
    (blobShiftsFrame row count base bytes index P))) with "[Hwords]" as "Hhandoff".
  { iApply (instr_pre_wand 0x154d4 0x154d4 false false with "Hwords"); [done | reflexivity |].
    iApply blob_shifts_to_low_pairs. }
  iPoseProof (blob_remaining_shifts_correct (storageKeyByte bytes index 14) (storageKeyByte bytes index 15) (storageKeyByte bytes index 1) (storageKeyByte bytes index 2) (storageKeyByte bytes index 3) (storageKeyByte bytes index 5) (storageKeyByte bytes index 6) (storageKeyByte bytes index 7) (storageKeyByte bytes index 25) (storageKeyByte bytes index 26) (storageKeyByte bytes index 27) (storageKeyByte bytes index 29) (storageKeyByte bytes index 30) (storageKeyByte bytes index 31)
    (blobShiftsFrame row count base bytes index P) with "[] Hhandoff") as "Hshifts".
  { iApply (big_sepL_submseteq with "H68"). apply sublist_submseteq, sublist_take. }
  iApply (instr_pre_wand 0x1549c 0x1549c false false with "Hshifts"); [done | reflexivity |].
  iApply blob_load0_to_shifts.
Qed.
Print Assumptions blob_shift_assembly_correct.
