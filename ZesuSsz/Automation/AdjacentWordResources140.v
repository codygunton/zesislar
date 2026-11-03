Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import isla.riscv64.riscv64.
Require Import stdpp.bitvector.definitions.
From iris.algebra Require Import dfrac.
From iris.proofmode Require Import tactics.
From Coq Require Import List NArith ZArith Lia.
Set Default Proof Mode "Classic".
Lemma adjacent_words_to_bytes140 : forall (Sigma : gFunctors) (islaG0 : islaG Sigma)
    (q : dfrac) (base next : Z) (n m : nat)
    (low : bv (8 * N.of_nat n)) (high : bv (8 * N.of_nat m)),
  next = (base + Z.of_nat n)%Z ->
  (⊢ ((base ↦ₘ{q} low) -∗ (next ↦ₘ{q} high) -∗
    base ↦ₘ{q}∗ (bv_to_little_endian (Z.of_nat n) 8 (bv_unsigned low) ++
      bv_to_little_endian (Z.of_nat m) 8 (bv_unsigned high))))%I.
Proof.
  intros Sigma islaG0 q base next n m low high Hadjacent. subst next.
  iIntros "Hlow Hhigh".
  iDestruct (mem_mapsto_mapsto_to_byte_array_len n base q low with "Hlow") as "Hlow".
  iDestruct (mem_mapsto_mapsto_to_byte_array_len m (base + Z.of_nat n)%Z q high
    with "Hhigh") as "Hhigh".
  iApply (mem_mapsto_array_app_combine_at 8%N base q
    (bv_to_little_endian (Z.of_nat n) 8 (bv_unsigned low))
    (bv_to_little_endian (Z.of_nat m) 8 (bv_unsigned high)) n with "Hlow").
  { rewrite length_bv_to_little_endian; [rewrite Nat2Z.id; reflexivity|lia]. }
  rewrite /= Z.mul_1_l.
  iExact "Hhigh".
Qed.
