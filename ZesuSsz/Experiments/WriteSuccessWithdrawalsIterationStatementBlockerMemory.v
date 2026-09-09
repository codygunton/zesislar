From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslaMemoryOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRepresentationBlockerData.

Open Scope Z_scope.

Definition writeSuccessBlockerOutsideMmio (address : addr) : Prop :=
  ~ (0x2401a0c0 <= bv_unsigned address < 0x2401a0d0).

Lemma writeSuccessBlockerOutsideMmioWrite memory address bytes :
  0 <= address ->
  address + Z.of_nat (length bytes) <= 0x2401a0c0 ->
  set_Forall writeSuccessBlockerOutsideMmio (dom memory) ->
  set_Forall writeSuccessBlockerOutsideMmio
    (dom (write_mem_list memory (Z_to_bv 64 address) bytes)).
Proof.
  revert memory address.
  induction bytes as [|byte bytes IH]; intros memory address Hlower Hupper Hmemory.
  - exact Hmemory.
  - cbn [write_mem_list].
    rewrite islaMemoryBvSucc.
    + apply IH; [lia|cbn in Hupper; lia|].
      rewrite dom_insert_L. apply set_Forall_union.
      2: exact Hmemory.
      apply (proj2 (set_Forall_singleton writeSuccessBlockerOutsideMmio
        (Z_to_bv 64 address))).
      unfold writeSuccessBlockerOutsideMmio.
      rewrite Z_to_bv_unsigned.
      rewrite bv_wrap_small; [cbn in Hupper; lia|].
      unfold bv_modulus. cbn in Hupper. cbn. lia.
    + unfold islaMemoryRange. cbn in Hupper. cbn. lia.
Qed.

Lemma writeSuccessBlockerNoMmioMemory :
  set_Forall writeSuccessBlockerOutsideMmio
    (dom writeSuccessBlockerRepresentedMemory).
Proof.
  unfold writeSuccessBlockerRepresentedMemory, writeSuccessBlockerMemory,
    writeSuccessBlockerZeroMemory.
  repeat apply writeSuccessBlockerOutsideMmioWrite;
    try (unfold writeSuccessBlockerOwner, writeSuccessBlockerScratch,
      writeSuccessBlockerAllBytes, writeSuccessBlockerCurrent,
      writeSuccessBlockerNext, writeSuccessBlockerIntegerBytes;
      rewrite ?map_length ?writeSuccessLayoutLeLength;
      cbn; lia).
  intros address Hempty. apply elem_of_dom in Hempty.
  destruct Hempty as [value Hlookup]. rewrite lookup_empty in Hlookup.
  discriminate.
Qed.

Print Assumptions writeSuccessBlockerOutsideMmioWrite.
Print Assumptions writeSuccessBlockerNoMmioMemory.
