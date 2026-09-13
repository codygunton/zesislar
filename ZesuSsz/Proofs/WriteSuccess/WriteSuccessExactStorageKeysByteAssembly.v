Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactStorageKeysLoads16 WriteSuccessExactStorageKeysLoads0
  WriteSuccessExactStorageKeysLoads12 WriteSuccessExactStorageKeysPairs8
  WriteSuccessExactStorageKeysLoadHandoff WriteSuccessExactStorageKeysUpperLoadHandoff
  WriteSuccessExactStorageKeysInitialLoads WriteSuccessExactStorageKeysPairHandoff
  WriteSuccessExactStorageKeysPairs8Load0 WriteSuccessExactStorageKeysRemainingShifts
  WriteSuccessExactStorageKeysShiftsHandoff WriteSuccessExactStorageKeysPrefix.

Lemma storage_keys_byte_assembly_correct `{!islaG Sigma} `{!threadG}
    row base bytes index (old21 : bv 64) (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_58.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_59.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ take 15 IslaTraces.write_success_60.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15324 (storageKeysRemainingShiftsPost
    (storageKeyByte bytes index 14) (storageKeyByte bytes index 15)
    (storageKeyByte bytes index 1) (storageKeyByte bytes index 2) (storageKeyByte bytes index 3)
    (storageKeyByte bytes index 5) (storageKeyByte bytes index 6) (storageKeyByte bytes index 7)
    (storageKeyByte bytes index 25) (storageKeyByte bytes index 26) (storageKeyByte bytes index 27)
    (storageKeyByte bytes index 29) (storageKeyByte bytes index 30) (storageKeyByte bytes index 31)
    (storageKeysShiftsFrame row base bytes index P)) -∗
  instr_body 0x15228 (storageKeysLoads16Entry row base bytes index
    (storageKeysLoad20Frame bytes index (storageKeysUpperLoadFrame bytes index
      (⌜(index + 32 <= length bytes)%nat⌝ ∗ ("x21" ↦ᵣ RVal_Bits old21 ∗ P ∗ True) ∗ True)%I))).
Proof.
  iStartProof. iIntros "#H58 #H59 #H60 Hnext".
  iPoseProof (storage_keys_remaining_shifts_correct
    (storageKeyByte bytes index 14) (storageKeyByte bytes index 15)
    (storageKeyByte bytes index 1) (storageKeyByte bytes index 2) (storageKeyByte bytes index 3)
    (storageKeyByte bytes index 5) (storageKeyByte bytes index 6) (storageKeyByte bytes index 7)
    (storageKeyByte bytes index 25) (storageKeyByte bytes index 26) (storageKeyByte bytes index 27)
    (storageKeyByte bytes index 29) (storageKeyByte bytes index 30) (storageKeyByte bytes index 31)
    (storageKeysShiftsFrame row base bytes index P) with "[] Hnext") as "Hshifts".
  { iApply (big_sepL_submseteq with "H60").
    change (drop 1 (take 15 IslaTraces.write_success_60.instrs.instr_map)
      ⊆+ take 15 IslaTraces.write_success_60.instrs.instr_map).
    apply sublist_submseteq, sublist_drop. }
  iAssert (instr_body 0x152ec (storageKeysLoads0Post row base bytes index
    (storageKeysPairs8Carry bytes index P))) with "[Hshifts]" as "Hhandoff".
  { iApply (instr_pre_wand 0x152ec 0x152ec false false with "Hshifts");
      [done | reflexivity |]. iApply storage_keys_load0_to_shifts. }
  iPoseProof (storage_keys_loads0_correct row base bytes index
    (storageKeysPairs8Carry bytes index P) with "[] Hhandoff") as "Hlow".
  { rewrite big_sepL_app. iSplit.
    - iApply (big_sepL_submseteq with "H59").
      etransitivity; apply sublist_submseteq; [apply sublist_take | apply sublist_drop].
    - iApply (big_sepL_submseteq with "H60").
      change (take 1 (take 15 IslaTraces.write_success_60.instrs.instr_map)
        ⊆+ take 15 IslaTraces.write_success_60.instrs.instr_map).
      apply sublist_submseteq, sublist_take. }
  iApply (storage_keys_prefix_correct row base bytes index old21 P with "H58 []").
  { iApply (big_sepL_submseteq with "H59"). apply sublist_submseteq, sublist_take. }
  iApply (instr_pre_wand 0x152dc 0x152dc false false with "Hlow");
    [done | reflexivity |]. iApply storage_keys_pairs8_to_load0.
Qed.
Print Assumptions storage_keys_byte_assembly_correct.
