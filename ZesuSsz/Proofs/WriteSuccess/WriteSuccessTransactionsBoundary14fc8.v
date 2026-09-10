From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary14f1c.

Import ListNotations.

Lemma write_success_recombine_three_u64 `{!islaG Sigma}
    (a : Z) (values : list (bv 8)) :
  a ↦ₘ∗ take 48 values -∗
  (a + 48) ↦ₘ
    Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop 48 values))) -∗
  (a + 56) ↦ₘ∗ take 0 (drop 56 values) -∗
  (a + 56) ↦ₘ Z_to_bv 64
    (little_endian_to_bv 8 (take 8 (drop 0 (drop 56 values)))) -∗
  (a + 64) ↦ₘ∗ take 0 (drop 8 (drop 56 values)) -∗
  (a + 64) ↦ₘ Z_to_bv 64
    (little_endian_to_bv 8
      (take 8 (drop 0 (drop 8 (drop 56 values))))) -∗
  (a + 72) ↦ₘ∗ drop 8 (drop 8 (drop 56 values)) -∗
  ⌜72 <= length values⌝ -∗
  a ↦ₘ∗ values.
Proof.
  iIntros "Hprefix0 Hword0 Hprefix1 Hword1 Hprefix2 Hword2 Hsuffix3"
    (Hlength).
  iPoseProof (mem_mapsto_array_recombine_u64_read _ _ _ _ _ with
    "Hprefix2 Hsuffix3 Hword2 [] [] []") as "Hrest2".
  - iPureIntro. cbn. lia.
  - iPureIntro. cbn. lia.
  - iPureIntro. cbn. rewrite !length_drop. lia.
  - iPoseProof (mem_mapsto_array_recombine_u64_read _ _ _ _ _ with
      "Hprefix1 Hrest2 Hword1 [] [] []") as "Hrest1".
    + iPureIntro. cbn. lia.
    + iPureIntro. cbn. lia.
    + iPureIntro. cbn. rewrite !length_drop. lia.
    + iPoseProof (mem_mapsto_array_recombine_u64_read _ _ _ _ _ with
        "Hprefix0 Hrest1 Hword0 [] [] []") as "Hvalues".
      * iPureIntro. cbn. lia.
      * iPureIntro. cbn. lia.
      * iPureIntro. cbn. lia.
      * iExact "Hvalues".
Qed.

Lemma write_success_recombine_three_u64_reads `{!islaG Sigma}
    (a : Z) (values : list (bv 8)) (start0 start1 start2 : nat)
    (word0 word1 word2 : Z) :
  a ↦ₘ∗ take start0 values -∗
  word0 ↦ₘ Z_to_bv 64
    (little_endian_to_bv 8 (take 8 (drop start0 values))) -∗
  (a + (start0 + 8)%nat) ↦ₘ∗
    take start1 (drop (start0 + 8) values) -∗
  word1 ↦ₘ Z_to_bv 64
    (little_endian_to_bv 8
      (take 8 (drop start1 (drop (start0 + 8) values)))) -∗
  (a + (start0 + 8)%nat + (start1 + 8)%nat) ↦ₘ∗
    take start2 (drop (start1 + 8) (drop (start0 + 8) values)) -∗
  word2 ↦ₘ Z_to_bv 64
    (little_endian_to_bv 8
      (take 8
        (drop start2 (drop (start1 + 8) (drop (start0 + 8) values))))) -∗
  (a + (start0 + 8)%nat + (start1 + 8)%nat +
    (start2 + 8)%nat) ↦ₘ∗
    drop (start2 + 8) (drop (start1 + 8) (drop (start0 + 8) values)) -∗
  ⌜word0 = (a + Z.of_nat start0)%Z⌝ -∗
  ⌜word1 = (a + Z.of_nat (start0 + 8) + Z.of_nat start1)%Z⌝ -∗
  ⌜word2 = (a + Z.of_nat (start0 + 8) + Z.of_nat (start1 + 8) +
    Z.of_nat start2)%Z⌝ -∗
  ⌜(start0 + 8 <= length values)%nat⌝ -∗
  ⌜(start1 + 8 <= length (drop (start0 + 8) values))%nat⌝ -∗
  ⌜(start2 + 8 <=
    length (drop (start1 + 8) (drop (start0 + 8) values)))%nat⌝ -∗
  a ↦ₘ∗ values.
Proof.
  iIntros "Hprefix0 Hword0 Hprefix1 Hword1 Hprefix2 Hword2 Hsuffix3"
    (Hword0 Hword1 Hword2 Hbound0 Hbound1 Hbound2).
  iPoseProof (mem_mapsto_array_recombine_u64_read _ _ _ _ _ with
    "Hprefix2 Hsuffix3 Hword2 [] [] []") as "Hrest2".
  - iPureIntro. reflexivity.
  - iPureIntro.
    change (word2 =
      a + Z.of_nat (start0 + 8) + Z.of_nat (start1 + 8) +
        1 * Z.of_nat start2)%Z.
    rewrite Hword2. lia.
  - iPureIntro. exact Hbound2.
  - iPoseProof (mem_mapsto_array_recombine_u64_read _ _ _ _ _ with
      "Hprefix1 Hrest2 Hword1 [] [] []") as "Hrest1".
    + iPureIntro. reflexivity.
    + iPureIntro.
      change (word1 =
        a + Z.of_nat (start0 + 8) + 1 * Z.of_nat start1)%Z.
      rewrite Hword1. lia.
    + iPureIntro. exact Hbound1.
    + iPoseProof (mem_mapsto_array_recombine_u64_read _ _ _ _ _ with
        "Hprefix0 Hrest1 Hword0 [] [] []") as "Hvalues".
      * iPureIntro. reflexivity.
      * iPureIntro.
        change (word0 = a + 1 * Z.of_nat start0)%Z.
        rewrite Hword0. lia.
      * iPureIntro. exact Hbound0.
      * iExact "Hvalues".
Qed.

Definition writeSuccessTransactions14fc8OtherRegisters : list string :=
  ["x1"; "x3"; "x4"; "x21"; "x22"; "x27"].

Definition writeSuccessTransactions14fc8OtherRegShapes :
    list (reg_kind * valu_shape) :=
  (fun register => (KindReg register, BitsShape 64))
    <$> writeSuccessTransactions14fc8OtherRegisters.

Definition writeSuccessTransactionsScratch14fc8 `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (transactions processed :
      list writeSuccessTransaction) (transaction : writeSuccessTransaction) :
    iProp Sigma :=
  ((bv_unsigned sp - 48) ↦ₘ? 152 ∗
   (bv_unsigned sp + 104) ↦ₘ Z_to_bv 64 base ∗
   (bv_unsigned sp + 112) ↦ₘ
     Z_to_bv 64 (Z.of_nat (length transactions)) ∗
   (bv_unsigned sp + 120) ↦ₘ
     bv_zero_extend 64 (writeSuccessTransactionByte transaction 285) ∗
   (bv_unsigned sp + 128) ↦ₘ? 96 ∗
   (bv_unsigned sp + 224) ↦ₘ writeSuccessTransactionWord transaction 152 ∗
   (bv_unsigned sp + 232) ↦ₘ writeSuccessTransactionWord transaction 144 ∗
   (bv_unsigned sp + 240) ↦ₘ writeSuccessTransactionWord transaction 136 ∗
   (bv_unsigned sp + 248) ↦ₘ
     Z_to_bv 64 (Z.of_nat (length processed)) ∗
   (bv_unsigned sp + 256) ↦ₘ? 16 ∗
   (bv_unsigned sp + 272) ↦ₘ writeSuccessTransactionWord transaction 176 ∗
   (bv_unsigned sp + 280) ↦ₘ? 1384 ∗
   (bv_unsigned sp + 1664) ↦ₘ writeSuccessTransactionWord transaction 160 ∗
   (bv_unsigned sp + 1672) ↦ₘ writeSuccessTransactionWord transaction 168 ∗
   (bv_unsigned sp + 1680) ↦ₘ? 216 ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsScratch14fc8) := I.

Definition writeSuccessTransactionsMachine14fc8 `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (transactions processed :
      list writeSuccessTransaction) (transaction : writeSuccessTransaction) :
    iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col writeSuccessTransactions14fc8OtherRegShapes ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   "x5" ↦ᵣ RVal_Bits
     (bv_zero_extend 64 (writeSuccessTransactionByte transaction 272)) ∗
   "x6" ↦ᵣ RVal_Bits
     (bv_zero_extend 64 (writeSuccessTransactionByte transaction 273)) ∗
   "x7" ↦ᵣ RVal_Bits
     (bv_shiftl
       (bv_zero_extend 64 (writeSuccessTransactionByte transaction 274))
       (BV 64 8)) ∗
   "x8" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 192) ∗
   "x9" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 16) ∗
   "x10" ↦ᵣ RVal_Bits
     (Z_to_bv 64 (base + 288 * Z.of_nat (length processed))) ∗
   "x11" ↦ᵣ RVal_Bits
     (bv_zero_extend 64 (writeSuccessTransactionByte transaction 264)) ∗
   "x12" ↦ᵣ RVal_Bits
     (bv_zero_extend 64 (writeSuccessTransactionByte transaction 265)) ∗
   "x13" ↦ᵣ RVal_Bits
     (bv_zero_extend 64 (writeSuccessTransactionByte transaction 280)) ∗
   "x14" ↦ᵣ RVal_Bits
     (bv_or
       (bv_shiftl
         (bv_zero_extend 64 (writeSuccessTransactionByte transaction 282))
         (BV 64 8))
       (bv_zero_extend 64 (writeSuccessTransactionByte transaction 281))) ∗
   "x15" ↦ᵣ RVal_Bits
     (bv_zero_extend 64 (writeSuccessTransactionByte transaction 285)) ∗
   "x16" ↦ᵣ RVal_Bits
     (bv_shiftl
       (bv_zero_extend 64 (writeSuccessTransactionByte transaction 283))
       (BV 64 16)) ∗
   "x17" ↦ᵣ RVal_Bits
     (bv_shiftl
       (bv_zero_extend 64 (writeSuccessTransactionByte transaction 284))
       (BV 64 24)) ∗
   "x18" ↦ᵣ RVal_Bits
     (bv_zero_extend 64 (writeSuccessTransactionByte transaction 279)) ∗
   "x19" ↦ᵣ RVal_Bits
     (bv_zero_extend 64 (writeSuccessTransactionByte transaction 266)) ∗
   "x20" ↦ᵣ RVal_Bits
     (bv_zero_extend 64 (writeSuccessTransactionByte transaction 267)) ∗
   "x23" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 24) ∗
   "x24" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 8) ∗
   "x25" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 0) ∗
   "x26" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 184) ∗
   "x28" ↦ᵣ RVal_Bits
     (bv_shiftl
       (bv_zero_extend 64 (writeSuccessTransactionByte transaction 275))
       (BV 64 16)) ∗
   "x29" ↦ᵣ RVal_Bits
     (bv_zero_extend 64 (writeSuccessTransactionByte transaction 276)) ∗
   "x30" ↦ᵣ RVal_Bits
     (bv_zero_extend 64 (writeSuccessTransactionByte transaction 277)) ∗
   "x31" ↦ᵣ RVal_Bits
     (bv_zero_extend 64 (writeSuccessTransactionByte transaction 278)) ∗
   writeSuccessTransactionsScratch14fc8
     sp base transactions processed transaction ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsMachine14fc8) := I.

Definition writeSuccessTransactionsAt14fc8Spec `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
      (transactions processed remaining : list writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec),
    writeSuccessTransactionsMachine14fc8
      sp base transactions processed transaction ∗
    (base + 288 * Z.of_nat (length processed)) ↦ₘ∗
      writeSuccessTransactionBytes transaction ∗
    writeSuccessTransactionsCurrentPhaseFrame P sp base transaction
      transactions processed remaining bytes prefix suffix tail ∗
    writeSuccessTransactionsLoadFacts
      sp base transaction processed bytes ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsAt14fc8Spec) := I.
