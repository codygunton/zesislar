Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactStorageKeysPairHandoff.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactBlobHashesLowPairs WriteSuccessExactBlobHashesLowPairsHandoff
  WriteSuccessExactBlobHashesUpperWords WriteSuccessExactBlobHashesUpperWordsHandoff
  WriteSuccessExactBlobHashesLowerWords WriteSuccessExactBlobHashesLowerWordsHandoff
  WriteSuccessExactBlobHashesWide WriteSuccessExactBlobHashesWideHandoff.

Lemma blob_word_assembly_correct `{!islaG Sigma} `{!threadG}
    row count base bytes index (P : iProp Sigma) :
  ([∗ list] instruction ∈ drop 16 IslaTraces.write_success_68.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ take 17 IslaTraces.write_success_69.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15538 (blobWidePost row count base bytes index P) -∗
  instr_body 0x154d4 (blobLowPairsEntry (storageKeyByte bytes index 0) (storageKeyByte bytes index 1) (storageKeyByte bytes index 2) (storageKeyByte bytes index 3) (storageKeyByte bytes index 4) (storageKeyByte bytes index 5) (storageKeyByte bytes index 6) (storageKeyByte bytes index 7) (storageKeyByte bytes index 14) (storageKeyByte bytes index 15) (storageKeyByte bytes index 24) (storageKeyByte bytes index 25) (storageKeyByte bytes index 26) (storageKeyByte bytes index 27) (storageKeyByte bytes index 28) (storageKeyByte bytes index 29) (storageKeyByte bytes index 30) (storageKeyByte bytes index 31)
    (blobLowPairsFrame row count base bytes index P)).
Proof.
  iStartProof. iIntros "#H68 #H69 Hnext".
  iPoseProof (blob_wide_correct row count base bytes index P with "[] Hnext") as "Hwide".
  { iApply (big_sepL_submseteq with "H69").
    change (drop 9 (take 17 IslaTraces.write_success_69.instrs.instr_map) ⊆+ take 17 IslaTraces.write_success_69.instrs.instr_map).
    apply sublist_submseteq, sublist_drop. }
  iAssert (instr_body 0x15518 (blobLowerWordsPost (storageKeyByte bytes index 0) (storageKeyByte bytes index 1) (storageKeyByte bytes index 2) (storageKeyByte bytes index 3) (storageKeyByte bytes index 4) (storageKeyByte bytes index 5) (storageKeyByte bytes index 6) (storageKeyByte bytes index 7) (storageKeyByte bytes index 24) (storageKeyByte bytes index 25) (storageKeyByte bytes index 26) (storageKeyByte bytes index 27) (storageKeyByte bytes index 28) (storageKeyByte bytes index 29) (storageKeyByte bytes index 30) (storageKeyByte bytes index 31)
    (blobLowerWordsFrame row count base bytes index P))) with "[Hwide]" as "Hlower".
  { iApply (instr_pre_wand 0x15518 0x15518 false false with "Hwide"); [done | reflexivity |].
    iApply blob_lower_words_to_wide. }
  iPoseProof (blob_lower_words_correct (storageKeyByte bytes index 0) (storageKeyByte bytes index 1) (storageKeyByte bytes index 2) (storageKeyByte bytes index 3) (storageKeyByte bytes index 4) (storageKeyByte bytes index 5) (storageKeyByte bytes index 6) (storageKeyByte bytes index 7) (storageKeyByte bytes index 24) (storageKeyByte bytes index 25) (storageKeyByte bytes index 26) (storageKeyByte bytes index 27) (storageKeyByte bytes index 28) (storageKeyByte bytes index 29) (storageKeyByte bytes index 30) (storageKeyByte bytes index 31)
    (blobLowerWordsFrame row count base bytes index P) with "[] Hlower") as "HlowerEntry".
  { iApply (big_sepL_submseteq with "H69").
    change (take 4 (drop 5 (take 17 IslaTraces.write_success_69.instrs.instr_map)) ⊆+ take 17 IslaTraces.write_success_69.instrs.instr_map).
    etransitivity; apply sublist_submseteq; [apply sublist_take | apply sublist_drop]. }
  iAssert (instr_body 0x15508 (blobUpperWordsPost (storageKeyByte bytes index 16) (storageKeyByte bytes index 17) (storageKeyByte bytes index 18) (storageKeyByte bytes index 19) (storageKeyByte bytes index 20) (storageKeyByte bytes index 21) (storageKeyByte bytes index 22) (storageKeyByte bytes index 23) (storageKeyByte bytes index 8) (storageKeyByte bytes index 9) (storageKeyByte bytes index 10) (storageKeyByte bytes index 11) (storageKeyByte bytes index 12) (storageKeyByte bytes index 13) (storageKeyByte bytes index 14) (storageKeyByte bytes index 15)
    (blobUpperWordsFrame row count base bytes index P))) with "[HlowerEntry]" as "Hupper".
  { iApply (instr_pre_wand 0x15508 0x15508 false false with "HlowerEntry"); [done | reflexivity |].
    iApply blob_upper_to_lower_words. }
  iPoseProof (blob_upper_words_correct (storageKeyByte bytes index 16) (storageKeyByte bytes index 17) (storageKeyByte bytes index 18) (storageKeyByte bytes index 19) (storageKeyByte bytes index 20) (storageKeyByte bytes index 21) (storageKeyByte bytes index 22) (storageKeyByte bytes index 23) (storageKeyByte bytes index 8) (storageKeyByte bytes index 9) (storageKeyByte bytes index 10) (storageKeyByte bytes index 11) (storageKeyByte bytes index 12) (storageKeyByte bytes index 13) (storageKeyByte bytes index 14) (storageKeyByte bytes index 15)
    (blobUpperWordsFrame row count base bytes index P) with "[] Hupper") as "HupperEntry".
  { iApply (big_sepL_submseteq with "H69").
    change (take 4 (drop 1 (take 17 IslaTraces.write_success_69.instrs.instr_map)) ⊆+ take 17 IslaTraces.write_success_69.instrs.instr_map).
    etransitivity; apply sublist_submseteq; [apply sublist_take | apply sublist_drop]. }
  iApply (blob_low_pairs_correct (storageKeyByte bytes index 0) (storageKeyByte bytes index 1) (storageKeyByte bytes index 2) (storageKeyByte bytes index 3) (storageKeyByte bytes index 4) (storageKeyByte bytes index 5) (storageKeyByte bytes index 6) (storageKeyByte bytes index 7) (storageKeyByte bytes index 14) (storageKeyByte bytes index 15) (storageKeyByte bytes index 24) (storageKeyByte bytes index 25) (storageKeyByte bytes index 26) (storageKeyByte bytes index 27) (storageKeyByte bytes index 28) (storageKeyByte bytes index 29) (storageKeyByte bytes index 30) (storageKeyByte bytes index 31)
    (blobLowPairsFrame row count base bytes index P) with "[]").
  { rewrite big_sepL_app. iSplit; first iExact "H68".
    iApply (big_sepL_submseteq with "H69").
    change (take 1 (take 17 IslaTraces.write_success_69.instrs.instr_map) ⊆+ take 17 IslaTraces.write_success_69.instrs.instr_map).
    apply sublist_submseteq, sublist_take. }
  iApply (instr_pre_wand 0x154f8 0x154f8 false false with "HupperEntry"); [done | reflexivity |].
  iApply blob_low_pairs_to_upper_words.
Qed.
Print Assumptions blob_word_assembly_correct.
