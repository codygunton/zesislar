Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Compliance.DecodeItemUnfoldRegistrations.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Export.Adequacy.
Require Import ZesuSsz.Export.Executor.
Require Import ZesuSsz.Export.Determinism.
Require Import ZesuSsz.Generated.TestTraces.EntryAddi.

From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Import ListNotations.

(** This fixture executes the selected decodeItem entry instruction.
    It checks the executor and its determinism checker, not a decoder contract. *)
Definition stockEntryRegisters : reg_map :=
  <["PC" := RVal_Bits (BV 64 0x800d6960)]>
    (<["x2" := RVal_Bits (BV 64 0xa0400000)]>
      (machine_ram_sys_regs_map stockZiskMap (BV 64 0) (BV 64 0)
        (BV 64 0x40000008) (BV 64 0))).
Definition stockEntryMemory : seq_global_state := {|
  seq_instrs := <[(BV 64 0x800d6964) := tnil]> ∅;
  seq_mem := ∅
|}.

Definition stock_entry_result_ok : bool :=
  match exec_instr trace_entry_addi stockEntryRegisters stockEntryMemory with
  | Some (registers, memory, labels, _) =>
      executor_option_valu_eqb (registers !! "x2")
        (Some (RVal_Bits (BV 64 0xa03ffff0))) &&
      executor_option_valu_eqb (registers !! "PC")
        (Some (RVal_Bits (BV 64 0x800d6964))) &&
      Nat.eqb (length labels) 0 &&
      bool_decide (seq_mem memory = seq_mem stockEntryMemory)
  | None => false
  end.

Lemma stock_entry_executes : stock_entry_result_ok = true.
Proof. vm_compute. reflexivity. Qed.

Lemma stock_entry_deterministic :
  executor_deterministicb trace_entry_addi stockEntryRegisters stockEntryMemory = true.
Proof. vm_compute. reflexivity. Qed.

Lemma stock_entry_completion_is_unique labels returned memory :
  CompletedInstructionSegment (instruction_boundary trace_entry_addi stockEntryRegisters)
    stockEntryMemory labels returned memory ->
  exists conditions,
    exec_instr trace_entry_addi stockEntryRegisters stockEntryMemory =
      Some (seq_regs returned, memory, labels, conditions) /\
    ExecutorConditions conditions.
Proof.
  apply exec_instr_deterministic. exact stock_entry_deterministic.
Qed.

Print Assumptions stock_entry_executes.
Print Assumptions stock_entry_deterministic.
Print Assumptions stock_entry_completion_is_unique.
