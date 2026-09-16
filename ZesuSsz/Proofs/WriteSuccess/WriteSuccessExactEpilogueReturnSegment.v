Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.CallReturnFrames.
Require Import ZesuSsz.Automation.Resources.
From iris.proofmode Require Import environments.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_126 Require Import instrs.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEpilogueBlock.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeContract.
Require Import ZesuSsz.Proofs.WriteSuccess.Interfaces.

Lemma write_success_exact_epilogue_return_segment
    `{!islaG Sigma} `{!threadG} {Decoded}
    (witness : writeSuccessNativeWitness Decoded) :
  ([∗ list] instruction ∈ drop 13 IslaTraces.write_success_126.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15a0c
    (writeSuccessExactEpilogueAddSpSpec
      (writeSuccessExactEpilogueExit witness)).
Proof.
  iStartProof.
  zesu_expose_code_lists.
  repeat first [progress iIntros (?) | progress iIntros "#?" |
    progress iIntros "?"].
  zesu_reduce_introduced_code_lists.
  repeat iDestruct select (_ ∗ _)%I as "[? ?]".
  zesu_run_until ltac:(fun _ => lazymatch goal with
    | |- envs_entails _ (writeSuccessExactEpilogueAddSpSpec _ -∗ _)%I => idtac
    end).
  iIntros "Hentry".
  iEval (unfold writeSuccessExactEpilogueAddSpSpec) in "Hentry".
  iDestruct "Hentry" as (sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
    "Hentry".
  repeat iDestruct select (_ ∗ _)%I as "[? ?]".
  zesu_open_resource_groups.
  iRename select (instr_pre _ _)%I into "Hreturn".
  have HreturnPc :
      bv_unsigned (bv_or (bv_and (ra + 0)%bv
        (BV 64 18446744073709551614)) (BV 64 0)) = bv_unsigned ra.
  { apply zesu_mask_return_even. assumption. }
  iEval (rewrite HreturnPc) in "Hreturn".
  zesu_run.
  iFrame.
Qed.

Print Assumptions write_success_exact_epilogue_return_segment.
