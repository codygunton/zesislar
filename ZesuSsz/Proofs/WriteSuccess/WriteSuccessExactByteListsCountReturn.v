Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.Alignment.
Require Import ZesuSsz.Automation.Resources.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactByteListsDispatchSpec.
From IslaTraces.write_success_05 Require Import instrs.
Local Existing Instance subsume_instr_pre_guard_inst.
Lemma byte_lists_exact_count_return_correct `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_05.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15c38 (byteListsExactDispatchSpec P) -∗
  instr_body 0x15c34 (byteListsExactCountReturnSpec P).
Proof.
  iStartProof. iIntros "#Hcode Hnext". iEval (simpl) in "Hcode".
  zesu_open_resource_groups. zesu_run. Unshelve.
  all: try zesu_pack
    (tail, done, itemBase, pointer, savedS1, savedS0, savedRa, sp, tt)ₗ.
  all: zesu_run. Unshelve.
Qed.
Print Assumptions byte_lists_exact_count_return_correct.

