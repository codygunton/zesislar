Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.read_input Require Import instrs.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Generated.Level1.
Require Import ZesuSsz.Contracts.Endpoints.

Import ListNotations.

Require Export ZesuSsz.Proofs.ReadInput.Resources.
Require Export ZesuSsz.Proofs.ReadInput.State.
Require Export ZesuSsz.Proofs.ReadInput.Model.
Require Export ZesuSsz.Proofs.ReadInput.Termination.

Theorem level1ReadInput :
  exists bound : nat, Nat.lt bound level1ContractFuel /\
    NativeContractAssumption readInputCorrectness
      readInputInstructionStep
      (PcInRanges readInputExecutionPcRanges)
      (PcInList readInputExitPcs)
      ZesuSsz.Generated.Level1.readInputEntry bound.
Proof.
  exists 8%nat. split.
  - unfold level1ContractFuel.
    apply (Nat.lt_trans _ 160 _); [lia |].
    apply Nat.pow_gt_lin_r. lia.
  - apply nativeContractBridge.
    + intros Sigma HG HT. apply read_input_state_correct.
    + exact readInputTermination.
Qed.
