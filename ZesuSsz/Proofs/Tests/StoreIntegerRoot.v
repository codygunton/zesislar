Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* A store whose pointer is a closed offset on an integer root under
   `Z_to_bv`, into an uninitialised region on the same root: the address is
   the integer `z - 8` and Lithium's own lookup splits the region. *)
Lemma store_integer_root `{!islaG Sigma} `{!threadG} (z : Z) :
  4096 <= z < 4294967296 ->
  (z - 16) ↦ₘ? 16 -∗
  find_in_context (FindMemMapsTo (bv_unsigned (Z_to_bv 64 z + BV 64 18446744073709551608)))
    (fun _ => True)%I.
Proof.
  intros Hz. iIntros "Hregion".
  progress ZesuSsz.Automation2.StoreMemoryLookup.zesu_store_memory_lookup.
  repeat liStep.
Qed.

(* The stack pointer register holds a word on another root: the step fires. *)
Lemma store_integer_root_other_stack `{!islaG Sigma} `{!threadG} (z sp : Z) :
  4096 <= z < 4294967296 ->
  "x2" ↦ᵣ RVal_Bits (Z_to_bv 64 sp) -∗
  (z - 16) ↦ₘ? 16 -∗
  find_in_context (FindMemMapsTo (bv_unsigned (Z_to_bv 64 z + BV 64 18446744073709551608)))
    (fun _ => True)%I.
Proof.
  intros Hz. iIntros "Hsp Hregion".
  progress ZesuSsz.Automation2.StoreMemoryLookup.zesu_store_memory_lookup.
  repeat liStep.
Qed.

(* The root is the stack pointer's root: frame accesses belong to the
   stack-address steps, the step refuses. *)
Lemma store_integer_root_refuses_stack `{!islaG Sigma} `{!threadG} (z : Z) :
  4096 <= z < 4294967296 ->
  "x2" ↦ᵣ RVal_Bits (bv_add (Z_to_bv 64 z) (BV 64 18446744073709551520)) -∗
  (z - 16) ↦ₘ? 16 -∗
  find_in_context (FindMemMapsTo (bv_unsigned (Z_to_bv 64 z + BV 64 18446744073709551608)))
    (fun _ => True)%I.
Proof.
  intros Hz. iIntros "Hsp Hregion".
  assert_fails ZesuSsz.Automation2.StoreMemoryLookup.zesu_store_memory_lookup.
  idtac "STACK_ROOT_REFUSAL_EXECUTED".
Abort.

(* No region or cell on the root owns the address: the step refuses. *)
Lemma store_integer_root_refuses_outside `{!islaG Sigma} `{!threadG} (z : Z) :
  4096 <= z < 4294967296 ->
  (z - 32) ↦ₘ? 16 -∗
  find_in_context (FindMemMapsTo (bv_unsigned (Z_to_bv 64 z + BV 64 18446744073709551608)))
    (fun _ => True)%I.
Proof.
  intros Hz. iIntros "Hregion".
  assert_fails ZesuSsz.Automation2.StoreMemoryLookup.zesu_store_memory_lookup.
  idtac "OUTSIDE_REFUSAL_EXECUTED".
Abort.

Print Assumptions store_integer_root.
Print Assumptions store_integer_root_other_stack.
