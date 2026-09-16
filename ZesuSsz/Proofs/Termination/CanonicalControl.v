Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.DecodeTermination.
Require Import ZesuSsz.Export.Executor.
Require Import ZesuSsz.Export.TerminationResources.
Require Import ZesuSsz.Generated.Level1.
Require Import ZesuSsz.Proofs.Termination.ControlExecutor.
Require Import ZesuSsz.Proofs.Termination.Program.

Import ListNotations.

Definition canonicalControlEntries : list Z :=
  [mainEntry; machinePc 0x4bdc;
   readInputEntry; allocatorGetEntry; writeSuccessEntry;
   writeFailureEntry; zkvmExitEntry].

Definition canonicalControlRegisters (pc : Z) (regs : reg_map) : reg_map :=
  <["PC" := RVal_Bits (Z_to_bv 64 pc)]> regs.

Definition canonicalControlGlobal (memory : mem_map) : seq_global_state := {|
  seq_instrs := zesuTerminationProgram;
  seq_mem := memory
|}.

Definition exec_canonical_control (fuel : nat) (pc : Z)
    (regs : reg_map) (memory : mem_map) : option ProgramExecutorResult :=
  trace ← zesuTerminationProgram !! Z_to_bv 64 pc;
  exec_program fuel trace (canonicalControlRegisters pc regs)
    (canonicalControlGlobal memory).

Lemma canonical_control_entry_lookup pc :
  In pc canonicalControlEntries ->
  exists trace, zesuTerminationProgram !! Z_to_bv 64 pc = Some trace.
Proof.
  intros Hentry.
  repeat (destruct Hentry as [<-|Hentry];
    [vm_compute; eexists; reflexivity|]).
  contradiction.
Qed.

Lemma canonical_control_decoder_absent :
  zesuTerminationProgram !! Z_to_bv 64 decodeInputEntry = None.
Proof. vm_compute. reflexivity. Qed.

Lemma canonical_control_start_boundary pc regs memory trace :
  zesuTerminationProgram !! Z_to_bv 64 pc = Some trace ->
  physicalInstructionBoundary pc
    (instruction_boundary trace (canonicalControlRegisters pc regs))
    (canonicalControlGlobal memory).
Proof.
  intros Htrace. repeat split; try reflexivity.
  - unfold physicalRegister64, canonicalControlRegisters.
    apply lookup_insert.
  - exact Htrace.
Qed.

Theorem exec_canonical_control_sound fuel pc regs memory result :
  exec_canonical_control fuel pc regs memory = Some result ->
  ExecutorConditions result.(programResultConditions) ->
  exists trace instructions steps,
    zesuTerminationProgram !! Z_to_bv 64 pc = Some trace /\
    physicalInstructionBoundary pc
      (instruction_boundary trace (canonicalControlRegisters pc regs))
      (canonicalControlGlobal memory) /\
    CompletedInstructionRun instructions
      (instruction_boundary trace (canonicalControlRegisters pc regs))
      (canonicalControlGlobal memory)
      result.(programResultLabels) result.(programResultLocal)
      result.(programResultGlobal) /\
    @nsteps isla_lang steps
      ([instruction_boundary trace (canonicalControlRegisters pc regs)],
        canonicalControlGlobal memory)
      result.(programResultLabels)
      ([result.(programResultLocal)], result.(programResultGlobal)) /\
    result.(programResultLocal).(seq_nb_state) = true.
Proof.
  unfold exec_canonical_control.
  destruct (zesuTerminationProgram !! Z_to_bv 64 pc) as [trace|] eqn:Htrace;
    [|discriminate].
  intros Hexec Hconditions.
  destruct (exec_program_sound _ _ _ _ _ Hexec Hconditions)
    as [instructions [Hrun Hterminal]].
  destruct (completed_run_nsteps _ _ _ _ _ _ Hrun) as [steps Hsteps].
  exists trace, instructions, steps.
  split; [reflexivity|].
  split; [apply canonical_control_start_boundary; exact Htrace|].
  split; [exact Hrun|].
  split; assumption.
Qed.

Print Assumptions canonical_control_entry_lookup.
Print Assumptions canonical_control_decoder_absent.
Print Assumptions canonical_control_start_boundary.
Print Assumptions exec_canonical_control_sound.
