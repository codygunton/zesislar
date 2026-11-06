Require Import ZesuSsz.Automation.SwitchDispatch.
Require Import ZesuSsz.Automation.BitvectorFacts.
Require Import ZesuSsz.Automation.Hooks.
Require Import ZesuSsz.Automation.VmClosed.
Require Import ZesuSsz.Automation.RewriteBoundGuards.
From Coq Require Import Bool.Bool ZArith.ZArith.
From stdpp Require Import bitvector.definitions decidable.

Class ZesuStepSourceFaultProof : Prop := {}.

(* Closed offset bounds use the checked evaluator. Symbolic bounds retain
   the existing solver path. A false closed bound never enters that path. *)
Ltac zesu_source_fault_offset_bound :=
  lazymatch goal with |- ?bound =>
    tryif VmClosed.zesu_vm_closed bound
    then RewriteBoundGuards.a3n_closed_bound
    else bv_solve
  end.

(* Check offsets before the existing integer-address parser evaluates them. *)
Ltac zesu_source_fault_closed_offsets pointer :=
  lazymatch pointer with
  | bv_add (bv_add (Z_to_bv 64 _) ?first) ?second =>
      MemoryAddress.zesu_stack_closed_term first;
      MemoryAddress.zesu_stack_closed_term second
  | bv_add (Z_to_bv 64 _) ?offset => MemoryAddress.zesu_stack_closed_term offset
  | bv_sub (Z_to_bv 64 _) ?offset => MemoryAddress.zesu_stack_closed_term offset
  | Z_to_bv 64 _ => idtac
  end.

(* The caller projects its existing source predicate; no premise is added. *)
Ltac zesu_source_fault_proof project leaf :=
  SwitchDispatch.zesu_switch_enabled constr:(ZesuStepSourceFaultProof);
  lazymatch goal with |- False => idtac end;
  solve [
    project;
    repeat match goal with Hpair : _ /\ _ |- _ => destruct Hpair end;
    apply Bool.negb_true_iff in leaf;
    apply bool_decide_eq_false_1 in leaf;
    repeat match goal with
    | Hbound : _ |- _ => progress (MemoryAddress.zesu_stack_normalize_hypothesis Hbound)
    end;
    Hooks.zesu_normalize_machine_map;
    lazymatch type of leaf with
    | context [bv_zero_extend 128 ?pointer] =>
        zesu_source_fault_closed_offsets pointer;
        let integer := MemoryAddress.zesu_stack_integer_address pointer in
        let Heq := fresh "HsourcePointer" in
        assert (Heq : bv_unsigned pointer = integer) by MemoryAddress.zesu_stack_arithmetic;
        repeat lazymatch type of leaf with
        | context [bv_signed (bv_zero_extend 128 ?value + ?offset)] =>
            rewrite (BitvectorFacts.zesu_signed_zero_extend_add_64_128 value offset) in leaf;
              last zesu_source_fault_offset_bound
        | context [bv_signed (bv_zero_extend 128 ?value)] =>
            rewrite (BitvectorFacts.zesu_signed_zero_extend_64_128 value) in leaf
        end;
        rewrite Heq in leaf;
        MemoryAddress.zesu_stack_normalize_hypothesis leaf;
        lia
    end ].
