Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactStorageKeysSpec WriteSuccessExactStorageKeysLoopBody.

Lemma storage_keys_loop_closed `{!islaG Sigma} `{!threadG}
    (x19 : bv 64) (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_58.instrs.instr_map, instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_59.instrs.instr_map, instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_60.instrs.instr_map, instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_61.instrs.instr_map, instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_62.instrs.instr_map, instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map, instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15228 (writeSuccessExactStorageKeysLoopSpec x19 P).
Proof.
  iStartProof. iIntros "#H58 #H59 #H60 #H61 #H62 #Houtput".
  iLöb as "IH".
  iModIntro. iApply instr_pre_to_body. iNext.
  iApply (storage_keys_loop_body with "H58 H59 H60 H61 H62 Houtput IH").
Qed.
Print Assumptions storage_keys_loop_closed.
