Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactStorageKeysNativeEntry.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactStorageKeysLoopClosed.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactStorageKeysLoopBody.
Require Import isla.riscv64.riscv64.

Lemma storage_keys_exact_native_correct `{!islaG Sigma} `{!threadG}
    x19 sp pointer remaining bytes tail (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_58.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_59.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_60.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_61.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_62.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15228 (storageKeysExactEntry x19 sp pointer remaining bytes tail P).
Proof.
  iStartProof. iIntros "#H58 #H59 #H60 #H61 #H62 #Houtput".
  iPoseProof (storage_keys_loop_closed x19 P
    with "H58 H59 H60 H61 H62 Houtput") as "#Hloop".
  iPoseProof (storage_keys_loop_body x19 P
    with "H58 H59 H60 H61 H62 Houtput Hloop") as "Hbody".
  iApply (instr_pre_wand 0x15228 0x15228 false false with "Hbody");
    [done | reflexivity |].
  iApply storage_keys_exact_entry_resources.
Qed.
Print Assumptions storage_keys_exact_native_correct.
