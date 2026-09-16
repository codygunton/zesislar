Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.CallReturnFrames.
Require Import ZesuSsz.Automation.Resources.
From iris.proofmode Require Import environments.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_126 Require Import instrs.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEpilogueBlock.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeContract.
Require Import ZesuSsz.Proofs.WriteSuccess.Interfaces.

Lemma write_success_exact_epilogue_prefix
    `{!islaG Sigma} `{!threadG} {Decoded}
    (witness : writeSuccessNativeWitness Decoded) :
  ([∗ list] instruction ∈ take 13 IslaTraces.write_success_126.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15a0c
    (writeSuccessExactEpilogueAddSpSpec
      (writeSuccessExactEpilogueExit witness)) -∗
  instr_body 0x159d8
    (writeSuccessEpilogueSpec
      (writeSuccessExactEpilogueExit witness)).
Proof.
  iStartProof.
  zesu_expose_code_lists.
  repeat first [progress iIntros (?) | progress iIntros "#?" |
    progress iIntros "?"].
  zesu_reduce_introduced_code_lists.
  repeat iDestruct select (_ ∗ _)%I as "[? ?]".
  zesu_run_until ltac:(fun _ =>
    lazymatch goal with
    | |- envs_entails _ (writeSuccessEpilogueSpec _ -∗ _)%I => idtac
    end).
  iIntros "Hentry".
  iEval (rewrite /writeSuccessEpilogueSpec) in "Hentry".
  iDestruct "Hentry" as (sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
    "Hentry".
  iEval (rewrite !reg_mapsto_pred_eq /reg_mapsto_pred_def) in "Hentry".
  repeat first [
    let value := fresh "registerValue" in
    iDestruct select (∃ _, _)%I as (value) "?" |
    progress iDestruct select (_ ∗ _)%I as "[? ?]"].
  zesu_open_resource_groups.
  iRename select (writeSuccessEpilogueSavedSlots _ _ _ _ _ _ _ _ _ _ _ _ _ _)%I
    into "Hslots".
  iEval (unfold writeSuccessEpilogueSavedSlots) in "Hslots".
  zesu_open_resource_groups.
  iRename select (instr_pre _ _)%I into "Hreturn".
  zesu_run.
Qed.

Print Assumptions write_success_exact_epilogue_prefix.
