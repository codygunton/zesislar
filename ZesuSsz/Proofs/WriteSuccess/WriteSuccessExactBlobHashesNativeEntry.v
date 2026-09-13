Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactBlobHashesHeader WriteSuccessExactBlobHashesLoopClosed.

Lemma blob_native_entry_correct `{!islaG Sigma} `{!threadG}
    sp pointer base total bytes tail (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_65.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_66.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_67.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_68.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_69.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_70.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_71.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x153d0 (blobHeaderEntry sp pointer base total bytes tail P).
Proof.
  iStartProof. iIntros "#H65 #H66 #H67 #H68 #H69 #H70 #H71 #Houtput".
  iApply (blob_header_correct with "H65 []").
  iApply (blob_loop_closed with "H66 H67 H68 H69 H70 H71 Houtput").
Qed.
Print Assumptions blob_native_entry_correct.
