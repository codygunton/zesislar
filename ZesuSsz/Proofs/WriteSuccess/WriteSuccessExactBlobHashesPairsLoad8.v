Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactStorageKeysPairHandoff.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactBlobHashesPairsLoad16 WriteSuccessExactBlobHashesPairHandoff
  WriteSuccessExactBlobHashesLoads8 WriteSuccessExactBlobHashesPairsLoad8Resources.

Lemma blob_pairs16_load8_correct `{!islaG Sigma} `{!threadG}
    row count base bytes index (old26 : bv 64) (P : iProp Sigma) :
  ([∗ list] instruction ∈ take 12 IslaTraces.write_success_67.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15464 (blobLoads8Post row base bytes index
    (blobPairs16Carry count bytes index P)) -∗
  instr_body 0x15434 (blobPairs16Entry (storageKeyByte bytes index 16) (storageKeyByte bytes index 17) (storageKeyByte bytes index 18) (storageKeyByte bytes index 19) (storageKeyByte bytes index 20) (storageKeyByte bytes index 21)
    (blobByte15EntryFrame row base bytes index
      (blobPairs16RemainingFrame count bytes index
        (⌜(index + 32 <= length bytes)%nat⌝ ∗ "x26" ↦ᵣ RVal_Bits old26 ∗ P ∗ True)%I))).
Proof.
  iStartProof. iIntros "#H67 Hnext".
  iPoseProof (blob_loads8_correct row base bytes index
    (blobPairs16Carry count bytes index P) with "[] Hnext") as "Hloads".
  { iApply (big_sepL_submseteq with "H67").
    change (drop 8 (take 12 IslaTraces.write_success_67.instrs.instr_map) ⊆+ take 12 IslaTraces.write_success_67.instrs.instr_map).
    apply sublist_submseteq, sublist_drop. }
  iAssert (instr_body 0x15454 (blobPairs16Post (storageKeyByte bytes index 16) (storageKeyByte bytes index 17) (storageKeyByte bytes index 18) (storageKeyByte bytes index 19) (storageKeyByte bytes index 20) (storageKeyByte bytes index 21)
    (blobByte15PostFrame row base bytes index
      (blobPairs16RemainingFrame count bytes index
        (⌜(index + 32 <= length bytes)%nat⌝ ∗ "x26" ↦ᵣ RVal_Bits old26 ∗ P ∗ True)%I))))
    with "[Hloads]" as "Hhandoff".
  { iApply (instr_pre_wand 0x15454 0x15454 false false with "Hloads"); [done | reflexivity |].
    iApply (blob_pairs16_to_load8 row count base bytes index old26 P). }
  iApply (blob_pairs_load16_correct (storageKeyByte bytes index 16) (storageKeyByte bytes index 17) (storageKeyByte bytes index 18) (storageKeyByte bytes index 19) (storageKeyByte bytes index 20) (storageKeyByte bytes index 21) row base bytes index
    (blobPairs16RemainingFrame count bytes index
      (⌜(index + 32 <= length bytes)%nat⌝ ∗ "x26" ↦ᵣ RVal_Bits old26 ∗ P ∗ True)%I)
    with "[] Hhandoff").
  iApply (big_sepL_submseteq with "H67").
  change (take 8 (take 12 IslaTraces.write_success_67.instrs.instr_map) ⊆+ take 12 IslaTraces.write_success_67.instrs.instr_map).
  apply sublist_submseteq, sublist_take.
Qed.
Print Assumptions blob_pairs16_load8_correct.
