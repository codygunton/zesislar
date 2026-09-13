Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsFlagLoads WriteSuccessExactStorageKeysPairs16
  WriteSuccessExactStorageKeysPairHandoff WriteSuccessExactStorageKeysLoads8
  WriteSuccessExactStorageKeysLoadHandoff WriteSuccessExactStorageKeysUpperLoadHandoff
  WriteSuccessExactStorageKeysLowerLoadHandoff WriteSuccessExactStorageKeysInitialLoads.

Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactStorageKeysPairsLoad8Resources.

Lemma storage_keys_pairs16_load8_correct `{!islaG Sigma} `{!threadG}
    row base bytes index (old21 : bv 64) (P : iProp Sigma) :
  ([∗ list] instruction ∈ take 7 IslaTraces.write_success_59.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ take 4 (drop 7 IslaTraces.write_success_59.instrs.instr_map),
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x152b4 (storageKeysLoads8Post row base bytes index
    (storageKeysPairs16Carry bytes index P)) -∗
  instr_body 0x15288 (storageKeysPairs16Entry
    (storageKeyByte bytes index 16) (storageKeyByte bytes index 17)
    (storageKeyByte bytes index 18) (storageKeyByte bytes index 19)
    (storageKeyByte bytes index 20) (storageKeyByte bytes index 21)
    (storageKeysPairs16Frame row base bytes index ("x21" ↦ᵣ RVal_Bits old21 ∗ P ∗ True)%I)).
Proof.
  iStartProof. iIntros "#Hpairs #Hloads Hnext".
  iPoseProof (storage_keys_loads8_correct row base bytes index
    (storageKeysPairs16Carry bytes index P) with "Hloads Hnext") as "Hmid".
  iApply (storage_keys_pairs16_correct
    (storageKeyByte bytes index 16) (storageKeyByte bytes index 17)
    (storageKeyByte bytes index 18) (storageKeyByte bytes index 19)
    (storageKeyByte bytes index 20) (storageKeyByte bytes index 21)
    (storageKeysPairs16Frame row base bytes index ("x21" ↦ᵣ RVal_Bits old21 ∗ P ∗ True)%I)
    with "Hpairs").
  iApply (instr_pre_wand 0x152a4 0x152a4 false false with "Hmid");
    [done | reflexivity |]. iApply (storage_keys_pairs16_to_load8 row base bytes index old21 P).
Qed.
Print Assumptions storage_keys_pairs16_load8_correct.
