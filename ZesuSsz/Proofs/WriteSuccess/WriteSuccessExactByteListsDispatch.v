Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.Alignment.
Require Import ZesuSsz.Automation.ByteListResources.
Require Import ZesuSsz.Automation.Resources.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactByteListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactByteListsDispatchSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessByteLists.
From IslaTraces.write_success_05 Require Import instrs.
Lemma byte_lists_exact_dispatch_correct `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_05.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15c3c (byteListsExactLoopSpec P) -∗
  instr_body 0x15c38 (byteListsExactDispatchSpec P).
Proof.
  iStartProof. iIntros "#Hcode #Hloop". iEval (simpl) in "Hcode".
  zesu_open_resource_groups. zesu_run. Unshelve.
  all: destruct items as [|item rest].
  all: try (unfold byteListEndPointer; bv_solve).
  all: try match goal with
  | Hbound : _ < 2 ^ 64, Heq : _ = 0%bv |- _ =>
      exfalso; cbn in Hbound, Heq; contradict Heq; bv_solve
  end.
  all: try match goal with
  | Hneq : _ <> 0%bv |- _ => exfalso; apply Hneq; bv_solve
  end.
  all: try zesu_pack
    (tail, rest, item, done, itemBase, pointer, savedS1, savedS0, savedRa, sp, tt)ₗ.
  all: zesu_open_resource_groups. all: zesu_run. Unshelve.
  all: zesu_open_processed_resources. all: zesu_run. Unshelve.
Qed.
Print Assumptions byte_lists_exact_dispatch_correct.

