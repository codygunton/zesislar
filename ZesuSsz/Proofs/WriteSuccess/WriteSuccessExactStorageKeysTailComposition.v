Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactStorageKeysTailGuard WriteSuccessExactStorageKeysTail
  WriteSuccessExactStorageKeysLoopReturn WriteSuccessExactStorageKeysSpec
  WriteSuccessExactStorageKeysTailPositive WriteSuccessExactStorageKeysTailZero
  WriteSuccessStorageKeysSpec.

Lemma storage_keys_tail_composed_correct `{!islaG Sigma} `{!threadG}
    (x19 sp pointer : bv 64) base total processed remaining bytes tail (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_62.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15228 (writeSuccessExactStorageKeysLoopSpec x19 P) -∗
  instr_pre 0x153b4 (writeSuccessStorageKeysLoopExit x19 sp base total bytes tail P) -∗
  instr_body 0x153a8 (storageKeysTailState pointer
    (Z_to_bv 64 (Z.of_nat (S remaining)))
    (storageKeysTailFrame x19 sp pointer base total processed remaining bytes tail P)).
Proof.
  iStartProof. iIntros "#Hcode #IH Hexit".
  iApply (storage_keys_tail_pre_correct with "Hcode [] [Hexit]").
  - iApply (instr_pre_wand 0x15228 0x15228 true true with "IH"); [done|reflexivity|].
    iIntros "Hstate". iApply (storage_keys_tail_positive with "Hstate").
  - iApply (instr_pre_wand 0x153b4 0x153b4 true true with "Hexit"); [done|reflexivity|].
    iIntros "Hstate".
    iDestruct (storage_keys_tail_zero with "Hstate") as "(Hresources & _ & _)".
    iExact "Hresources".
Qed.
Print Assumptions storage_keys_tail_composed_correct.
