Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Generated.Level1.
Require Import ZesuSsz.Export.Executor.
Require Import ZesuSsz.Proofs.Termination.ControlExecutor.
Require Import ZesuSsz.Proofs.Termination.ContractExecutor.

(** The generated return PC equals the native contract return PC. *)
Definition writeSuccessContractHalt (regs : reg_map)
    (_ : seq_global_state) : bool :=
  executor_option_valu_eqb (regs !! "PC")
    (Some (RVal_Bits (Z_to_bv 64 (machinePc 0x4bf0)))).

Lemma writeSuccess_contract_halt_return regs sigma :
  writeSuccessContractHalt regs sigma = true <->
  regs !! "PC" = Some (RVal_Bits (BV 64 0x14d10)).
Proof.
  unfold writeSuccessContractHalt.
  rewrite executor_option_valu_eqb_reflect.
  assert (Hpc : Z_to_bv 64 (machinePc 0x4bf0) = BV 64 0x14d10).
  { apply bv_eq. vm_compute. reflexivity. }
  rewrite Hpc. reflexivity.
Qed.

Theorem writeSuccess_contract_executor_sound fuel trace regs sigma result :
  exec_program_until writeSuccessContractHalt fuel trace regs sigma = Some result ->
  ExecutorConditions result.(programResultConditions) ->
  exists instructions,
    (instructions <= fuel)%nat /\
    CompletedInstructionRun instructions (instruction_boundary trace regs) sigma
      result.(programResultLabels) result.(programResultLocal)
      result.(programResultGlobal) /\
    seq_regs result.(programResultLocal) !! "PC" =
      Some (RVal_Bits (BV 64 0x14d10)).
Proof.
  intros Hexec Hconditions.
  destruct (exec_program_until_sound _ _ _ _ _ _ Hexec Hconditions)
    as [instructions [Hbound [Hrun Hhalt]]].
  exists instructions. split; [exact Hbound|]. split; [exact Hrun|].
  exact (proj1 (writeSuccess_contract_halt_return _ _) Hhalt).
Qed.

Print Assumptions writeSuccess_contract_halt_return.
Print Assumptions writeSuccess_contract_executor_sound.
