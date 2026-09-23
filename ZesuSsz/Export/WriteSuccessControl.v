Require Import ZesuSsz.Automation.All.
From Coq Require Import ZArith.ZArith Lia.
Require Import ZesuSsz.Export.Executor.
Require Import ZesuSsz.Export.Determinism.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Generated.Level1.
Require Import isla.opsem.

Open Scope nat_scope.

(** This boundary uses the execution range, which includes callees. *)
Definition writeSuccessControlBoundary (pc : Z) (trace : isla_trace)
    (regs : reg_map) (sigma : seq_global_state) : Prop :=
  PcInRanges writeSuccessExecutionPcRanges pc /\
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 pc)) /\
  seq_instrs sigma !! Z_to_bv 64 pc = Some trace.

Lemma writeSuccess_executor_sound pc trace regs sigma regs' sigma' labels conditions :
  writeSuccessControlBoundary pc trace regs sigma ->
  exec_instr trace regs sigma = Some (regs', sigma', labels, conditions) ->
  ExecutorConditions conditions ->
  exists theta,
    seq_regs theta = regs' /\
    CompletedInstructionSegment (instruction_boundary trace regs) sigma
      labels theta sigma'.
Proof.
  intros _ Hexec Hconditions.
  eapply exec_instr_sound; eassumption.
Qed.

Lemma writeSuccess_executor_complete pc trace regs sigma labels theta sigma' :
  writeSuccessControlBoundary pc trace regs sigma ->
  executor_deterministicb trace regs sigma = true ->
  CompletedInstructionSegment (instruction_boundary trace regs) sigma
    labels theta sigma' ->
  exists conditions,
    exec_instr trace regs sigma =
      Some (seq_regs theta, sigma', labels, conditions) /\
    ExecutorConditions conditions.
Proof.
  intros _ Hdet Hrun.
  eapply exec_instr_deterministic; eassumption.
Qed.

Lemma writeSuccess_completed_successor_unique pc trace regs sigma
    labels1 theta1 sigma1 labels2 theta2 sigma2 :
  writeSuccessControlBoundary pc trace regs sigma ->
  executor_deterministicb trace regs sigma = true ->
  CompletedInstructionSegment (instruction_boundary trace regs) sigma
    labels1 theta1 sigma1 ->
  CompletedInstructionSegment (instruction_boundary trace regs) sigma
    labels2 theta2 sigma2 ->
  seq_regs theta1 = seq_regs theta2 /\
  sigma1 = sigma2 /\ labels1 = labels2.
Proof.
  intros Hboundary Hdet Hfirst Hsecond.
  destruct (writeSuccess_executor_complete _ _ _ _ _ _ _ Hboundary Hdet Hfirst)
    as [conditions1 [Hexec1 _]].
  destruct (writeSuccess_executor_complete _ _ _ _ _ _ _ Hboundary Hdet Hsecond)
    as [conditions2 [Hexec2 _]].
  rewrite Hexec1 in Hexec2. inversion Hexec2. auto.
Qed.

(** The generated execution count counts distinct addresses.  It is not
    a dynamic instruction bound. *)
Lemma writeSuccess_execution_count_within_fuel :
  Nat.lt writeSuccessExecutionInstructionCount level1ContractFuel.
Proof.
  unfold writeSuccessExecutionInstructionCount, level1ContractFuel.
  assert (Hsmall : 950 < Nat.pow 2 10) by (vm_compute; lia).
  assert (Hlarge : 150 < Nat.pow 2 150).
  { apply Nat.pow_gt_lin_r. lia. }
  replace 160 with (10 + 150)%nat by reflexivity.
  rewrite Nat.pow_add_r. nia.
Qed.

(** This is a candidate numeric budget indexed by input size.
    The open rank invariant must prove that it bounds dynamic execution. *)
Definition writeSuccessFuelBound (inputSize : nat) : nat :=
  S (writeSuccessExecutionInstructionCount * S inputSize).

Lemma writeSuccess_fuel_bound_within_level1 inputSize :
  Nat.le inputSize maxSszInputSize ->
  Nat.lt (writeSuccessFuelBound inputSize) level1ContractFuel.
Proof.
  intros Hsize.
  unfold writeSuccessFuelBound, writeSuccessExecutionInstructionCount,
    maxSszInputSize, level1ContractFuel in *.
  assert (Hsmall : Nat.pow 2 8 = 256) by (vm_compute; reflexivity).
  assert (Hlarge : Nat.lt 128 (Nat.pow 2 128)).
  { apply Nat.pow_gt_lin_r. lia. }
  replace 160 with (8 + 8 + 8 + 8 + 128)%nat by reflexivity.
  repeat rewrite Nat.pow_add_r.
  rewrite Hsmall. nia.
Qed.

Lemma writeSuccess_fuel_input_indexed :
  InputIndexedBound writeSuccessFuelBound.
Proof.
  intros inputSize Hsize.
  pose proof (writeSuccess_fuel_bound_within_level1 inputSize ltac:(lia)) as Hbound.
  lia.
Qed.

(** A control state carries the PC, sp, and ra values at an instruction
    boundary.  The rank proof must extract active loop counters from
    registers or stack slots. *)
Definition WriteSuccessControlFacts (theta : seq_local_state) : Prop :=
  exists pc sp ra,
    PcInRanges writeSuccessExecutionPcRanges pc /\
    seq_regs theta !! "PC" = Some (RVal_Bits (Z_to_bv 64 pc)) /\
    seq_regs theta !! "x2" = Some (RVal_Bits sp) /\
    seq_regs theta !! "x1" = Some (RVal_Bits ra).

(** This is the outstanding Phase 5.3 obligation.  The caller supplies
    [remaining] by reading machine counters.  The rank must decrease on
    every completed instruction that stays in the execution range. *)
Definition WriteSuccessFuelInvariant
    (inputSize : nat)
    (control : seq_local_state -> seq_global_state -> Prop)
    (remaining : seq_local_state -> seq_global_state -> option (nat * nat * nat * nat))
    (rank : seq_local_state -> seq_global_state -> nat) : Prop :=
  (forall theta sigma,
    control theta sigma ->
    WriteSuccessControlFacts theta /\
    exists transactions withdrawals headers bytes,
      remaining theta sigma = Some (transactions, withdrawals, headers, bytes) /\
      transactions + withdrawals + headers + bytes <= inputSize /\
      rank theta sigma < writeSuccessFuelBound inputSize) /\
  (forall theta sigma,
    control theta sigma ->
    exists labels theta' sigma',
      CompletedInstructionSegment theta sigma labels theta' sigma') /\
  (forall theta sigma labels theta' sigma',
    control theta sigma ->
    CompletedInstructionSegment theta sigma labels theta' sigma' ->
    control theta' sigma' \/
      exists pc, seq_regs theta' !! "PC" = Some (RVal_Bits (Z_to_bv 64 pc)) /\
        PcInList writeSuccessExitPcs pc) /\
  (forall theta sigma labels theta' sigma',
    control theta sigma -> control theta' sigma' ->
    CompletedInstructionSegment theta sigma labels theta' sigma' ->
    rank theta' sigma' < rank theta sigma).

Print Assumptions writeSuccess_executor_sound.
Print Assumptions writeSuccess_executor_complete.
Print Assumptions writeSuccess_completed_successor_unique.
Print Assumptions writeSuccess_execution_count_within_fuel.
Print Assumptions writeSuccess_fuel_bound_within_level1.
Print Assumptions writeSuccess_fuel_input_indexed.
