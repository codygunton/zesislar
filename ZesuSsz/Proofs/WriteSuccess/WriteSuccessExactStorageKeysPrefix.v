Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactStorageKeysLoads16 WriteSuccessExactStorageKeysLoads8
  WriteSuccessExactStorageKeysLoads12 WriteSuccessExactStorageKeysPairs8
  WriteSuccessExactStorageKeysLoadHandoff WriteSuccessExactStorageKeysUpperLoadHandoff
  WriteSuccessExactStorageKeysLowerLoadHandoff WriteSuccessExactStorageKeysInitialLoads
  WriteSuccessExactStorageKeysPairHandoff WriteSuccessExactStorageKeysPairsLoad8Resources
  WriteSuccessExactStorageKeysPairsLoad8 WriteSuccessExactStorageKeysPairs8Handoff.

Lemma storage_keys_prefix_correct `{!islaG Sigma} `{!threadG}
    row base bytes index (old21 : bv 64) (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_58.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ take 21 IslaTraces.write_success_59.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x152dc (storageKeysPairs8Post
    (storageKeyByte bytes index 8) (storageKeyByte bytes index 9)
    (storageKeyByte bytes index 10) (storageKeyByte bytes index 11)
    (storageKeyByte bytes index 12) (storageKeyByte bytes index 13)
    (storageKeyByte bytes index 22) (storageKeyByte bytes index 23)
    (storageKeysPairs8Frame row base bytes index P)) -∗
  instr_body 0x15228 (storageKeysLoads16Entry row base bytes index
    (storageKeysLoad20Frame bytes index (storageKeysUpperLoadFrame bytes index
      (⌜(index + 32 <= length bytes)%nat⌝ ∗ ("x21" ↦ᵣ RVal_Bits old21 ∗ P ∗ True) ∗ True)%I))).
Proof.
  iStartProof. iIntros "#H58 #H59 Hnext".
  iAssert (instr_body 0x152b4 (storageKeysLoads8Post row base bytes index
    (storageKeysPairs16Carry bytes index P))) with "[Hnext]" as "Hloads".
  { iPoseProof (storage_keys_pairs8_correct
      (storageKeyByte bytes index 8) (storageKeyByte bytes index 9)
      (storageKeyByte bytes index 10) (storageKeyByte bytes index 11)
      (storageKeyByte bytes index 12) (storageKeyByte bytes index 13)
      (storageKeyByte bytes index 22) (storageKeyByte bytes index 23)
      (storageKeysPairs8Frame row base bytes index P) with "[] Hnext") as "Hpairs".
    { iApply (big_sepL_submseteq with "H59").
      change (drop 11 (take 21 IslaTraces.write_success_59.instrs.instr_map)
        ⊆+ take 21 IslaTraces.write_success_59.instrs.instr_map).
      apply sublist_submseteq, sublist_drop. }
    iApply (instr_pre_wand 0x152b4 0x152b4 false false with "Hpairs");
      [done | reflexivity |]. iApply storage_keys_load8_to_pairs8. }
  iPoseProof (storage_keys_pairs16_load8_correct row base bytes index old21 P
    with "[] [] Hloads") as "Hmiddle".
  { iApply (big_sepL_submseteq with "H59").
    change (take 7 (take 21 IslaTraces.write_success_59.instrs.instr_map)
      ⊆+ take 21 IslaTraces.write_success_59.instrs.instr_map).
    apply sublist_submseteq, sublist_take. }
  { iApply (big_sepL_submseteq with "H59").
    change (take 4 (drop 7 (take 21 IslaTraces.write_success_59.instrs.instr_map))
      ⊆+ take 21 IslaTraces.write_success_59.instrs.instr_map).
    etransitivity; apply sublist_submseteq; [apply sublist_take | apply sublist_drop]. }
  iApply (storage_keys_initial_loads_correct row base bytes index
    (⌜(index + 32 <= length bytes)%nat⌝ ∗ ("x21" ↦ᵣ RVal_Bits old21 ∗ P ∗ True) ∗ True)%I
    with "[] [] [] [] [] []").
  1-6: iApply (big_sepL_submseteq with "H58");
    first [apply sublist_submseteq, sublist_take |
      etransitivity; apply sublist_submseteq; [apply sublist_take | apply sublist_drop]].
  iApply (instr_pre_wand 0x15288 0x15288 false false with "Hmiddle");
    [done | reflexivity |].
  iApply (storage_keys_initial_loads_to_pairs16 row base bytes index
    ("x21" ↦ᵣ RVal_Bits old21 ∗ P ∗ True)%I).
Qed.
Print Assumptions storage_keys_prefix_correct.
