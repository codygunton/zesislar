Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.ByteArrayAssemblyCodec.
Require Import ZesuSsz.Automation.MemoryTupleConsumer.
Require Import isla.riscv64.riscv64.
From iris.base_logic.lib Require Import iprop.
From iris.proofmode Require Import tactics.
From Coq Require Import List ZArith.
From stdpp Require Import list bitvector.definitions.
Require Import ZesuSsz.Automation.All.
Local Open Scope Z_scope.

Section Controls.
Context (Sigma : gFunctors) (G : islaG Sigma) `{!threadG}.
#[local] Existing Instance G.

Lemma affine_array_named (address : Z) (fraction : dfrac)
    (before : list (bv 8)) (value base : bv 64)
    (Hlength : length before = 16%nat) :
  ⊢ (address ↦ₘ{fraction}∗
       (take (Z.to_nat (address + 0 - address)) before ++
        bv_to_little_endian 8 8 (bv_unsigned value) ++ drop 8 before) -∗
     mem_mapsto_array_def address fraction
       (bv_to_little_endian 8 8 (bv_unsigned (bv_sub (bv_add value base) base)) ++
        drop 8 before))%I.
Proof.
  iIntros "Hbytes". rewrite <- mem_mapsto_array_eq.
  MemoryTupleConsumer.zesu_memory_array_assemble.
Qed.

Lemma affine_array_anonymous (address : Z) (fraction : dfrac)
    (before : list (bv 8)) (value base : bv 64)
    (Hlength : length before = 16%nat) :
  ⊢ (address ↦ₘ{fraction}∗
       (take (Z.to_nat (address + 0 - address)) before ++
        bv_to_little_endian 8 8 (bv_unsigned value) ++ drop 8 before) -∗
     mem_mapsto_array_def address fraction
       (bv_to_little_endian 8 8 (bv_unsigned (bv_sub (bv_add value base) base)) ++
        drop 8 before))%I.
Proof.
  iIntros "?". rewrite <- mem_mapsto_array_eq.
  MemoryTupleConsumer.zesu_memory_array_assemble.
Qed.

Lemma affine_array_fraction_refuses (address : Z)
    (before : list (bv 8)) (value base : bv 64)
    (Hlength : length before = 16%nat) : True.
Proof.
  assert_fails ltac:(assert (Hbad :
    ⊢ (address ↦ₘ{DfracDiscarded}∗
         (take (Z.to_nat (address + 0 - address)) before ++
          bv_to_little_endian 8 8 (bv_unsigned value) ++ drop 8 before) -∗
       mem_mapsto_array_def address (DfracOwn 1)
         (bv_to_little_endian 8 8 (bv_unsigned (bv_sub (bv_add value base) base)) ++
          drop 8 before))%I) by
    (iIntros "Hbytes"; rewrite <- mem_mapsto_array_eq;
     solve [MemoryTupleConsumer.zesu_memory_array_assemble])).
  exact I.
Qed.
End Controls.
