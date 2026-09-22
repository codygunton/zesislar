(* The two goals the post-withdrawals hand draft answers by hand, twice.

   The block loads the word at `sp + 1136`, which is index 13 of the
   value array based at `sp + 1032`. Islaris reads through an array on
   its own; what it cannot do is prove the address is inside one, and
   the draft spends three `have` blocks on the facts that decide it.

   These are the same goals, closed by the rule. *)

Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.PureFacts.
Require Import ZesuSsz.Automation.StackArrayLookup.
Require Import isla.riscv64.riscv64.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Contracts.Endpoints.
From Coq Require Import Lists.List ZArith.ZArith.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessNativeContract WriteSuccessRepresentation
  WriteSuccessExactPrefixStackFacts.

Section stack_array_lookup.
  Set Default Proof Using "Type*".
  Context {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}.
  Context (args : WriteSuccessArgs Decoded).
  Context (witness : writeSuccessNativeWitness Decoded).
  Context (Hwf : writeSuccessWitnessWellFormed args witness).

  (* The frame pointer is eight-aligned at the loaded offset. *)
  Lemma test_stack_array_alignment :
    bv_extract 0 3 (writeSuccessFrameSp witness + BV 64 1136) = BV 3 0.
  Proof. zesu_witness_arith. Qed.

  (* The loaded address stays inside the machine's RAM. *)
  Lemma test_stack_array_upper :
    bv_unsigned (writeSuccessFrameSp witness + BV 64 1136) <=
      bv_unsigned (BV 64 (machineRamEnd defaultMap) - BV 64 8).
  Proof. zesu_witness_arith. Qed.

  (* The index the read computes is inside the array. This is the goal
     Islaris's `MKArray` branch raises, and the one the draft answers
     with `rewrite Haddress; rewrite length_take; … lia`. *)
  Lemma test_stack_array_index :
    (Z.to_nat ((bv_unsigned (writeSuccessFrameSp witness + BV 64 1136) -
       (bv_unsigned (writeSuccessFrameSp witness) + 1032)) `div` 8)
     < length (take 69 (writeSuccessValues witness)))%nat.
  Proof. zesu_witness_arith. Qed.

  (* The selection side condition itself: the hint that picks the array
     out of a context holding twenty of them. *)
  Lemma test_stack_array_range :
    (bv_unsigned (writeSuccessFrameSp witness) + 1032 <=
       bv_unsigned (writeSuccessFrameSp witness + BV 64 1136) <
       bv_unsigned (writeSuccessFrameSp witness) + 1032 +
         length (take 69 (writeSuccessValues witness)) * Z.of_N (64 `div` 8))
    \/ bv_unsigned (writeSuccessFrameSp witness) + 1032 =
       bv_unsigned (writeSuccessFrameSp witness + BV 64 1136).
  Proof. zesu_stack_array_range. Qed.

End stack_array_lookup.

Print Assumptions test_stack_array_alignment.
Print Assumptions test_stack_array_index.
Print Assumptions test_stack_array_range.
