Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.read_input Require Import instrs.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Generated.Level1.
Require Import ZesuSsz.Contracts.Endpoints.

Import ListNotations.

Require Export ZesuSsz.Proofs.ReadInput.Resources.

Definition readInputControlFlow : list (Z * Z) := [
  (0x10140, 0x10144); (0x10144, 0x10148);
  (0x10148, 0x1014c); (0x1014c, 0x10150);
  (0x10150, 0x10154); (0x10154, 0x10158);
  (0x10158, 0x1015c); (0x1015c, 0x14ccc)
].

Definition readInputInstructionStep (fromPc toPc : Z) : Prop :=
  List.In (fromPc, toPc) readInputControlFlow.

Definition readInputModel :
    IslarisContractModel ReadInputArgs ReadInputOutcome := {|
  islarisContractAllows := readInputAllows;
  islarisContractStep := readInputInstructionStep;
  islarisContractResources := fun Sigma HG HT =>
    @read_input_resources Sigma HG HT
|}.

Definition readInputCorrectness : Prop :=
  IslarisContractCorrect 0x10140 0x14ccc readInputModel.

Definition readInputPath : list Z := [
  0x10140; 0x10144; 0x10148; 0x1014c; 0x10150;
  0x10154; 0x10158; 0x1015c; 0x14ccc
].

