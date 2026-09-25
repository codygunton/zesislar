Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Export.Executor.
Require Import ZesuSsz.Export.Determinism.
Require Import ZesuSsz.Generated.Level1.

Definition writeSuccessControlPc (pc : Z) : Prop :=
  PcInRanges writeSuccessExecutionPcRanges pc.

Definition writeSuccessInstructionAt (pc : Z) (trace : isla_trace)
    (regs : reg_map) (sigma : seq_global_state) : Prop :=
  writeSuccessControlPc pc /\
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 pc)) /\
  seq_instrs sigma !! Z_to_bv 64 pc = Some trace.

Lemma write_success_exec_instr_sound pc trace regs sigma regs' sigma'
    labels conditions :
  writeSuccessInstructionAt pc trace regs sigma ->
  exec_instr trace regs sigma = Some (regs', sigma', labels, conditions) ->
  ExecutorConditions conditions ->
  exists theta,
    seq_regs theta = regs' /\
    CompletedInstructionSegment (instruction_boundary trace regs) sigma
      labels theta sigma'.
Proof.
  intros _ Hexec Hconditions.
  eapply exec_instr_sound; eauto.
Qed.

Lemma write_success_exec_instr_deterministic pc trace regs sigma labels
    theta sigma' :
  writeSuccessInstructionAt pc trace regs sigma ->
  executor_deterministicb trace regs sigma = true ->
  CompletedInstructionSegment (instruction_boundary trace regs) sigma
    labels theta sigma' ->
  exists conditions,
    exec_instr trace regs sigma =
      Some (seq_regs theta, sigma', labels, conditions) /\
    ExecutorConditions conditions.
Proof.
  intros _ Hdet Hrun.
  eapply exec_instr_deterministic; eauto.
Qed.

(* The control proof must show that its path fits this cap. *)
Definition writeSuccessFuelOfInput (size : nat) : nat :=
  S (writeSuccessExecutionInstructionCount *
    Nat.pow (S size) 5).

Definition writeSuccessFuelBound : nat :=
  writeSuccessFuelOfInput maxSszInputSize.

Lemma write_success_fuel_mono (size : nat) :
  (size <= maxSszInputSize)%nat ->
  (writeSuccessFuelOfInput size <= writeSuccessFuelBound)%nat.
Proof.
  intros Hsize.
  unfold writeSuccessFuelBound, writeSuccessFuelOfInput.
  apply (proj1 (Nat.succ_le_mono _ _)).
  apply Nat.mul_le_mono_l.
  apply Nat.pow_le_mono_l.
  exact (proj1 (Nat.succ_le_mono _ _) Hsize).
Qed.

Lemma write_success_fuel_bound_positive : (0 < writeSuccessFuelBound)%nat.
Proof. unfold writeSuccessFuelBound, writeSuccessFuelOfInput. lia. Qed.

Lemma write_success_fuel_bound_level1 :
  (writeSuccessFuelBound < level1ContractFuel)%nat.
Proof.
  apply Nat2Z.inj_lt.
  unfold writeSuccessFuelBound, writeSuccessFuelOfInput,
    writeSuccessExecutionInstructionCount, level1ContractFuel,
    maxSszInputSize.
  rewrite Nat2Z.inj_succ Nat2Z.inj_mul.
  rewrite !Nat2Z.inj_pow.
  rewrite Nat2Z.inj_succ.
  rewrite !Nat2Z.inj_mul.
  vm_compute. lia.
Qed.

Lemma write_success_input_fuel_bounded :
  InputIndexedBound writeSuccessFuelOfInput.
Proof.
  intros size Hsize.
  eapply Nat.le_lt_trans.
  - apply write_success_fuel_mono. exact Hsize.
  - exact write_success_fuel_bound_level1.
Qed.

Print Assumptions write_success_exec_instr_sound.
Print Assumptions write_success_exec_instr_deterministic.
Print Assumptions write_success_fuel_bound_level1.
Print Assumptions write_success_input_fuel_bounded.
