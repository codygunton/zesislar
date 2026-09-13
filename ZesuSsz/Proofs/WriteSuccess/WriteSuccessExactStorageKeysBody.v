Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessOutput WriteSuccessExactStorageKeysLoads16 WriteSuccessExactStorageKeysWords
  WriteSuccessExactStorageKeysLoadHandoff WriteSuccessExactStorageKeysUpperLoadHandoff
  WriteSuccessExactStorageKeysByteAssembly WriteSuccessExactStorageKeysPairHandoff
  WriteSuccessExactStorageKeysEmit WriteSuccessExactStorageKeysEmitHandoff
  WriteSuccessExactStorageKeysOutputComposition WriteSuccessExactStorageKeysInitialLoads.

Lemma storage_keys_body_correct `{!islaG Sigma} `{!threadG}
    row base bytes index (old21 : bv 64) sp a b c d tail (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_58.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_59.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_60.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_61.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x10190 (writeOutputTraceSpec (sp + BV 64 1712)%bv (BV 64 32)
    (BV 64 0x153a8) (take 32 (drop index bytes)) tail
    (storageKeysEmitFrame sp (take 32 (drop index bytes))
      (storageKeysEmitCallerFrame row base bytes index P))) -∗
  instr_body 0x153a8 (storageKeysEmitPost sp (take 32 (drop index bytes)) tail
    (storageKeysEmitCallerFrame row base bytes index P)) -∗
  instr_body 0x15228 (storageKeysLoads16Entry row base bytes index
    (storageKeysLoad20Frame bytes index (storageKeysUpperLoadFrame bytes index
      (⌜(index + 32 <= length bytes)%nat⌝ ∗
        ("x21" ↦ᵣ RVal_Bits old21 ∗
          storageKeysOutputResources sp a b c d (take 32 (drop index bytes)) tail P ∗ True) ∗ True)%I))).
Proof.
  iStartProof. iIntros "#H58 #H59 #H60 #H61 #Houtput Hnext".
  iPoseProof (storage_keys_output_composed_correct row base bytes index sp a b c d tail P
    with "[] [] Houtput Hnext") as "Hcall".
  1-2: iApply (big_sepL_submseteq with "H61");
    etransitivity; apply sublist_submseteq; [apply sublist_take | apply sublist_drop].
  iPoseProof (storage_keys_words_correct row base bytes index
    (storageKeysOutputResources sp a b c d (take 32 (drop index bytes)) tail P)
    with "[] Hcall") as "Hwords".
  { rewrite big_sepL_app. iSplit.
    - iApply (big_sepL_submseteq with "H60"). apply sublist_submseteq, sublist_drop.
    - iApply (big_sepL_submseteq with "H61"). apply sublist_submseteq, sublist_take. }
  iApply (storage_keys_byte_assembly_correct row base bytes index old21
    (storageKeysOutputResources sp a b c d (take 32 (drop index bytes)) tail P)
    with "H58 H59 [] Hwords").
  iApply (big_sepL_submseteq with "H60"). apply sublist_submseteq, sublist_take.
Qed.
Print Assumptions storage_keys_body_correct.
