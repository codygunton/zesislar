Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.read_input Require Import instrs.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Generated.Level1.
Require Import ZesuSsz.Contracts.Endpoints.

Import ListNotations.

Require Export ZesuSsz.Proofs.ReadInput.Model.

Lemma readInputTermination :
  InstructionPathCertificate readInputInstructionStep
    (PcInRanges readInputExecutionPcRanges)
    (PcInList readInputExitPcs) 0x10140 8.
Proof.
  exists readInputPath. split; first reflexivity. split.
  - unfold readInputPath.
    solve_instruction_path ltac:(
      cbn [readInputInstructionStep readInputControlFlow];
      repeat first [left; reflexivity | right]).
  - split.
    + apply Forall_forall. intros pc Hpc.
      unfold PcInRanges. eexists 0x10140, 0x10190. split.
      * cbn. auto.
      * unfold readInputPath in Hpc. cbn in Hpc.
        apply elem_of_list_In in Hpc. cbn in Hpc. lia.
    + split.
      * eexists 0x14ccc. split; [reflexivity | cbn; auto].
      * split; [reflexivity | lia].
Qed.

