From Coq Require Import Arith.PeanoNat ZArith.ZArith Lia.

Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Contracts.Machine.
Require Import ZesuSsz.Generated.Level1.
Require Import ZesuSsz.Generated.WriteSuccessCertificate.
Require Import ZesuSsz.Experiments.WriteSuccessNativeContract.

Open Scope Z_scope.

Definition writeSuccessGeneratedNativeCorrectness {State Decoded}
    (model : Level1MachineModel State Decoded)
    (outputRelation : WriteSuccessOutputRelation Decoded) : Prop :=
  IslarisContractCorrect 0x14d30 0x14d10
    (writeSuccessNativeModel model outputRelation
      writeSuccessGeneratedInstructionStep).

(** The generated certificate discharges the complete control-flow side of
    the native Level 1 assumption.  The machine proof supplies only the
    correctness proposition. *)
Theorem writeSuccessGeneratedNativeAssumption {State Decoded}
    (model : Level1MachineModel State Decoded)
    (outputRelation : WriteSuccessOutputRelation Decoded) :
  writeSuccessGeneratedNativeCorrectness model outputRelation ->
  exists bound : nat,
    Nat.lt bound level1ContractFuel /\
    NativeContractAssumption
      (writeSuccessGeneratedNativeCorrectness model outputRelation)
      writeSuccessGeneratedInstructionStep
      (PcInRanges writeSuccessExecutionPcRanges)
      (PcInList writeSuccessExitPcs) writeSuccessEntry bound.
Proof.
  intros Hcorrect. exists 225%nat. split.
  - unfold level1ContractFuel.
    apply Nat.lt_le_trans with (m := Nat.pow 2 8).
    + cbn. lia.
    + apply Nat.pow_le_mono_r; lia.
  - exact (writeSuccessGeneratedBridge
      (writeSuccessGeneratedNativeCorrectness model outputRelation) Hcorrect).
Qed.
