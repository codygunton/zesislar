Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactStorageKeysPairHandoff.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactBlobHashesPairs8 WriteSuccessExactBlobHashesPairs8Handoff
  WriteSuccessExactBlobHashesLoads0 WriteSuccessExactBlobHashesPairs8Load0
  WriteSuccessExactBlobHashesWide WriteSuccessExactBlobHashesShiftAssembly.

Lemma blob_pair_assembly_correct `{!islaG Sigma} `{!threadG}
    row count base bytes index (P : iProp Sigma) :
  ([∗ list] instruction ∈ drop 12 IslaTraces.write_success_67.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_68.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ take 17 IslaTraces.write_success_69.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15538 (blobWidePost row count base bytes index P) -∗
  instr_body 0x15464 (blobPairs8Entry (storageKeyByte bytes index 8) (storageKeyByte bytes index 9) (storageKeyByte bytes index 10) (storageKeyByte bytes index 11) (storageKeyByte bytes index 12) (storageKeyByte bytes index 13) (storageKeyByte bytes index 22) (storageKeyByte bytes index 23)
    (blobPairs8Frame row count base bytes index P)).
Proof.
  iStartProof. iIntros "#H67 #H68 #H69 Hnext".
  iPoseProof (blob_shift_assembly_correct row count base bytes index P
    with "[] H69 Hnext") as "Hshifts".
  { iApply (big_sepL_submseteq with "H68"). apply sublist_submseteq, sublist_drop. }
  iPoseProof (blob_loads0_correct row base bytes index
    (blobPairs8Carry count bytes index P) with "[] Hshifts") as "Hloads".
  { rewrite big_sepL_app. iSplit.
    - iApply (big_sepL_submseteq with "H67").
      change (drop 10 (drop 12 IslaTraces.write_success_67.instrs.instr_map) ⊆+ drop 12 IslaTraces.write_success_67.instrs.instr_map).
      apply sublist_submseteq, sublist_drop.
    - iApply (big_sepL_submseteq with "H68"). apply sublist_submseteq, sublist_take. }
  iAssert (instr_body 0x1548c (blobPairs8Post (storageKeyByte bytes index 8) (storageKeyByte bytes index 9) (storageKeyByte bytes index 10) (storageKeyByte bytes index 11) (storageKeyByte bytes index 12) (storageKeyByte bytes index 13) (storageKeyByte bytes index 22) (storageKeyByte bytes index 23)
    (blobPairs8Frame row count base bytes index P))) with "[Hloads]" as "Hhandoff".
  { iApply (instr_pre_wand 0x1548c 0x1548c false false with "Hloads"); [done | reflexivity |].
    iApply blob_pairs8_to_load0. }
  iApply (blob_pairs8_correct (storageKeyByte bytes index 8) (storageKeyByte bytes index 9) (storageKeyByte bytes index 10) (storageKeyByte bytes index 11) (storageKeyByte bytes index 12) (storageKeyByte bytes index 13) (storageKeyByte bytes index 22) (storageKeyByte bytes index 23)
    (blobPairs8Frame row count base bytes index P) with "[] Hhandoff").
  iApply (big_sepL_submseteq with "H67"). apply sublist_submseteq, sublist_take.
Qed.
Print Assumptions blob_pair_assembly_correct.
