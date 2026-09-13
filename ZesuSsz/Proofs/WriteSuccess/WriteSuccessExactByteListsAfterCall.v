Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.Alignment.
Require Import ZesuSsz.Automation.ByteListResources.
Require Import ZesuSsz.Automation.Resources.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactByteListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessByteLists.
From IslaTraces.write_success_05 Require Import instrs.

Lemma byte_lists_exact_after_call_correct `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_05.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15c4c (byteListsExactAfterCallSpec P).
Proof.
  iStartProof. iIntros "#Hcode". iEval (simpl) in "Hcode".
  repeat iDestruct select (instr _ _ ∗ _)%I as "(? & ?)".
  zesu_run. Unshelve. all: try zesu_alignment.
  all: destruct rest as [|next more].
  all: try (unfold byteListEndPointer; bv_solve).
  all: try match goal with
  | Hbound : _ < 2 ^ 64, Heq : _ = 0%bv |- _ =>
      exfalso; cbn in Hbound, Heq; contradict Heq; bv_solve
  end.
  all: try match goal with
  | Hneq : _ <> 0%bv |- _ => exfalso; apply Hneq; bv_solve
  end.
  all: try zesu_pack
    (tail, more, next, done ++ [item], itemBase,
      (pointer + BV 64 16)%bv, savedS1, savedS0, savedRa, sp, tt)ₗ.
  all: zesu_open_resource_groups.
  all: zesu_run. Unshelve. all: try zesu_alignment.
  all: zesu_open_resource_groups.
  all: try zesu_normalize_resource_addresses.
  all: zesu_run. Unshelve. all: try zesu_alignment.
  all: try (rewrite app_length; cbn; lia).
  all: try match goal with
  | Hbound : context[length (?head :: ?rest)] |- _ => cbn in Hbound; lia
  end.
Qed.
Print Assumptions byte_lists_exact_after_call_correct.

