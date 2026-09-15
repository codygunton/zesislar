Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Specs.
Require Import ZesuSsz.Contracts.IslarisCode.
From IslaTraces.write_success_32 Require Import
  a15078_spec a1507c_spec a15080_spec a15084_spec.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary14f1c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15028.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15078.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15088.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.
#[local] Typeclasses Opaque writeSuccessTransactionsCurrentPhaseFrame.

Lemma write_success_15078_current_unsigned (current : Z) :
  (0 <= current)%Z ->
  (current < 2 ^ 64)%Z ->
  bv_unsigned (Z_to_bv 64 current) = current.
Proof. intros. bv_solve. Qed.

#[local] Hint Rewrite write_success_15078_current_unsigned using lia :
  lithium_rewrite.

Definition writeSuccessTransactionsScratch15080 `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (transactions processed :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction) :
    iProp Sigma :=
  ((bv_unsigned sp - 48) ↦ₘ? 152 ∗
   (bv_unsigned sp + 104) ↦ₘ Z_to_bv 64 base ∗
   (bv_unsigned sp + 112) ↦ₘ
     Z_to_bv 64 (Z.of_nat (length transactions)) ∗
   (bv_unsigned sp + 120) ↦ₘ
     bv_zero_extend 64
       (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
         transaction 285) ∗
   (bv_unsigned sp + 128) ↦ₘ
     WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 64 ∗
   (bv_unsigned sp + 136) ↦ₘ? 8 ∗
   (bv_unsigned sp + 144) ↦ₘ
     WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 88 ∗
   (bv_unsigned sp + 152) ↦ₘ
     WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 80 ∗
   (bv_unsigned sp + 160) ↦ₘ? 40 ∗
   (bv_unsigned sp + 200) ↦ₘ
     WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 104 ∗
   (bv_unsigned sp + 208) ↦ₘ? 8 ∗
   (bv_unsigned sp + 216) ↦ₘ
     WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 96 ∗
   (bv_unsigned sp + 224) ↦ₘ
     WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 152 ∗
   (bv_unsigned sp + 232) ↦ₘ
     WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 144 ∗
   (bv_unsigned sp + 240) ↦ₘ
     WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 136 ∗
   (bv_unsigned sp + 248) ↦ₘ
     Z_to_bv 64 (Z.of_nat (length processed)) ∗
   (bv_unsigned sp + 256) ↦ₘ? 16 ∗
   (bv_unsigned sp + 272) ↦ₘ
     WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 176 ∗
   (bv_unsigned sp + 280) ↦ₘ? 1384 ∗
   (bv_unsigned sp + 1664) ↦ₘ
     WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 160 ∗
   (bv_unsigned sp + 1672) ↦ₘ
     WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 168 ∗
   (bv_unsigned sp + 1680) ↦ₘ? 216 ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsScratch15080) := I.

Definition writeSuccessTransactionsMachine15078WithX15AndScratch
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (transactions processed :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (x15 : bv 64) (scratch : iProp Sigma) :
    iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col (delete 3%nat writeSuccessTransactions15028OtherRegShapes) ∗
   "x21" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
       transaction 72) ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   "x5" ↦ᵣ RVal_Bits
     (bv_or
       (bv_shiftl
         (bv_zero_extend 64
           (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
             transaction 272))
         (BV 64 24))
       (bv_shiftl
         (bv_zero_extend 64
           (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
             transaction 271))
         (BV 64 16))) ∗
   "x6" ↦ᵣ RVal_Bits
     (bv_or
       (bv_shiftl
         (bv_zero_extend 64
           (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
             transaction 278))
         (BV 64 8))
       (bv_zero_extend 64
         (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
           transaction 277))) ∗
   "x7" ↦ᵣ RVal_Bits
     (bv_or
       (bv_shiftl
         (bv_zero_extend 64
           (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
             transaction 268))
         (BV 64 24))
       (bv_shiftl
         (bv_zero_extend 64
           (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
             transaction 267))
         (BV 64 16))) ∗
   "x8" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
       transaction 192) ∗
   "x9" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
       transaction 16) ∗
   "x10" ↦ᵣ RVal_Bits
     (Z_to_bv 64 (base + 288 * Z.of_nat (length processed))) ∗
   "x11" ↦ᵣ RVal_Bits
     (bv_zero_extend 64
       (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
         transaction 264)) ∗
   "x12" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
       transaction 265) ∗
   "x13" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
       transaction 273) ∗
   "x14" ↦ᵣ RVal_Bits
     (bv_or
       (bv_or
         (bv_shiftl
           (bv_zero_extend 64
             (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
               transaction 284))
           (BV 64 24))
         (bv_shiftl
           (bv_zero_extend 64
             (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
               transaction 283))
           (BV 64 16)))
       (bv_or
         (bv_shiftl
           (bv_zero_extend 64
             (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
               transaction 282))
           (BV 64 8))
         (bv_zero_extend 64
           (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
             transaction 281)))) ∗
   "x15" ↦ᵣ RVal_Bits x15 ∗
   "x16" ↦ᵣ RVal_Bits
     (bv_shiftl
       (bv_or
         (bv_or
           (bv_shiftl
             (bv_zero_extend 64
               (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
                 transaction 272))
             (BV 64 24))
           (bv_shiftl
             (bv_zero_extend 64
               (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
                 transaction 271))
             (BV 64 16)))
         (bv_or
           (bv_shiftl
             (bv_zero_extend 64
               (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
                 transaction 270))
             (BV 64 8))
           (bv_zero_extend 64
             (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
               transaction 269))))
       (BV 64 32)) ∗
   "x17" ↦ᵣ RVal_Bits
     (bv_or
       (bv_shiftl
         (bv_zero_extend 64
           (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
             transaction 276))
         (BV 64 24))
       (bv_shiftl
         (bv_zero_extend 64
           (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
             transaction 275))
         (BV 64 16))) ∗
   "x18" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 48) ∗
   "x19" ↦ᵣ RVal_Bits
     (bv_shiftl
       (bv_zero_extend 64
         (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
           transaction 266))
       (BV 64 8)) ∗
   "x20" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 56) ∗
   "x23" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 24) ∗
   "x24" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 8) ∗
   "x25" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 0) ∗
   "x26" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
       transaction 184) ∗
   "x27" ↦ᵣ RVal_Bits
     (bv_zero_extend 64
       (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
         transaction 32)) ∗
   "x28" ↦ᵣ RVal_Bits
     (bv_or
       (bv_shiftl
         (bv_zero_extend 64
           (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
             transaction 270))
         (BV 64 8))
       (bv_zero_extend 64
         (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
           transaction 269))) ∗
   "x29" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 64) ∗
   "x30" ↦ᵣ RVal_Bits
     (bv_shiftl
       (bv_zero_extend 64
         (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
           transaction 271))
       (BV 64 16)) ∗
   "x31" ↦ᵣ RVal_Bits
     (bv_shiftl
       (bv_zero_extend 64
         (WriteSuccessTransactionsSpec.writeSuccessTransactionByte
           transaction 278))
       (BV 64 8)) ∗
   scratch ∗ True)%I.

Global Instance : LithiumUnfold
  (@writeSuccessTransactionsMachine15078WithX15AndScratch) := I.

Definition writeSuccessTransactionsMachine1507c `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (transactions processed :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction) :
    iProp Sigma :=
  writeSuccessTransactionsMachine15078WithX15AndScratch
    sp base transactions processed transaction
    (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
      transaction 104)
    (writeSuccessTransactionsScratch15078
      sp base transactions processed transaction).

Global Instance : LithiumUnfold (@writeSuccessTransactionsMachine1507c) := I.

Definition writeSuccessTransactionsMachine15080 `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (transactions processed :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction) :
    iProp Sigma :=
  writeSuccessTransactionsMachine15078WithX15AndScratch
    sp base transactions processed transaction
    (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
      transaction 104)
    (writeSuccessTransactionsScratch15080
      sp base transactions processed transaction).

Global Instance : LithiumUnfold (@writeSuccessTransactionsMachine15080) := I.

Definition writeSuccessTransactionsMachine15084 `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (transactions processed :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction) :
    iProp Sigma :=
  writeSuccessTransactionsMachine15078WithX15AndScratch
    sp base transactions processed transaction
    (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
      transaction 112)
    (writeSuccessTransactionsScratch15080
      sp base transactions processed transaction).

Global Instance : LithiumUnfold (@writeSuccessTransactionsMachine15084) := I.

Definition writeSuccessTransactionsAt1507cSpec `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z)
      (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
      (transactions processed remaining :
        list WriteSuccessTransactionsSpec.writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec),
    writeSuccessTransactionsMachine1507c
      sp base transactions processed transaction ∗
    (base + 288 * Z.of_nat (length processed)) ↦ₘ∗
      WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction ∗
    writeSuccessTransactionsCurrentPhaseFrame P sp base transaction
      transactions processed remaining bytes prefix suffix tail ∗
    writeSuccessTransactionsLoadFacts
      sp base transaction processed bytes ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsAt1507cSpec) := I.

Definition writeSuccessTransactionsAt15080Spec `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z)
      (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
      (transactions processed remaining :
        list WriteSuccessTransactionsSpec.writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec),
    writeSuccessTransactionsMachine15080
      sp base transactions processed transaction ∗
    (base + 288 * Z.of_nat (length processed)) ↦ₘ∗
      WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction ∗
    writeSuccessTransactionsCurrentPhaseFrame P sp base transaction
      transactions processed remaining bytes prefix suffix tail ∗
    writeSuccessTransactionsLoadFacts
      sp base transaction processed bytes ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsAt15080Spec) := I.

Definition writeSuccessTransactionsAt15084Spec `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z)
      (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
      (transactions processed remaining :
        list WriteSuccessTransactionsSpec.writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec),
    writeSuccessTransactionsMachine15084
      sp base transactions processed transaction ∗
    (base + 288 * Z.of_nat (length processed)) ↦ₘ∗
      WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction ∗
    writeSuccessTransactionsCurrentPhaseFrame P sp base transaction
      transactions processed remaining bytes prefix suffix tail ∗
    writeSuccessTransactionsLoadFacts
      sp base transaction processed bytes ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsAt15084Spec) := I.

Definition writeSuccessTransactionsAt15078Block
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
    iProp Sigma :=
  (writeSuccessTransactionsMachine15078
     sp base transactions processed transaction ∗
   (base + 288 * Z.of_nat (length processed)) ↦ₘ∗
     WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction ∗
   writeSuccessTransactionsCurrentPhaseFrame P sp base transaction
     transactions processed remaining bytes prefix suffix tail ∗
   writeSuccessTransactionsLoadFacts
     sp base transaction processed bytes ∗
   ⌜bv_unsigned
      (Z_to_bv 64 (base + 288 * Z.of_nat (length processed))) =
     (base + 288 * Z.of_nat (length processed))%Z⌝ ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsAt15078Block) := I.

Definition writeSuccessTransactionsAt1507cBlock
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
    iProp Sigma :=
  (writeSuccessTransactionsMachine1507c
     sp base transactions processed transaction ∗
   (base + 288 * Z.of_nat (length processed)) ↦ₘ∗
     WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction ∗
   writeSuccessTransactionsCurrentPhaseFrame P sp base transaction
     transactions processed remaining bytes prefix suffix tail ∗
   writeSuccessTransactionsLoadFacts
     sp base transaction processed bytes ∗
   ⌜bv_unsigned
      (Z_to_bv 64 (base + 288 * Z.of_nat (length processed))) =
     (base + 288 * Z.of_nat (length processed))%Z⌝ ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsAt1507cBlock) := I.

Definition writeSuccessTransactionsAt15080Block
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
    iProp Sigma :=
  (writeSuccessTransactionsMachine15080
     sp base transactions processed transaction ∗
   (base + 288 * Z.of_nat (length processed)) ↦ₘ∗
     WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction ∗
   writeSuccessTransactionsCurrentPhaseFrame P sp base transaction
     transactions processed remaining bytes prefix suffix tail ∗
   writeSuccessTransactionsLoadFacts
     sp base transaction processed bytes ∗
   ⌜bv_unsigned
      (Z_to_bv 64 (base + 288 * Z.of_nat (length processed))) =
     (base + 288 * Z.of_nat (length processed))%Z⌝ ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsAt15080Block) := I.

Definition writeSuccessTransactionsAt15084Block
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
    iProp Sigma :=
  (writeSuccessTransactionsMachine15084
     sp base transactions processed transaction ∗
   (base + 288 * Z.of_nat (length processed)) ↦ₘ∗
     WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction ∗
   writeSuccessTransactionsCurrentPhaseFrame P sp base transaction
     transactions processed remaining bytes prefix suffix tail ∗
   writeSuccessTransactionsLoadFacts
     sp base transaction processed bytes ∗
   ⌜bv_unsigned
      (Z_to_bv 64 (base + 288 * Z.of_nat (length processed))) =
     (base + 288 * Z.of_nat (length processed))%Z⌝ ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsAt15084Block) := I.

Lemma write_success_transactions_chunk_15080_load_block
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
  instr_body 0x15080
    (zesu_ld_byte_array_at_spec 0x15080 "x15" "x10" 112 0 112) -∗
  instr_body 0x15084 (writeSuccessTransactionsAt15084Spec P) -∗
  instr_body 0x15080 (writeSuccessTransactionsAt15080Block P sp base
    transaction transactions processed remaining bytes prefix suffix tail).
Proof.
  move => *.
  iStartProof.
  iIntros "Hnext".
  liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: rewrite ?write_success_15078_current_unsigned; try lia.
  all: iExists
    (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction,
      tt)ₗ.
  all: try prepare_sidecond.
  all: try assumption.
  all: rewrite ?write_success_15078_current_unsigned; try lia.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try solve_zesu_ld_array_at.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve. all: repeat iIntros "?"; liARun.
  Unshelve.
  iExists
    (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction,
      tt)ₗ.
  iIntros "Hprefix112 Hsuffix120".
  cbn.
  have Hstart :
    Z.to_nat
      (bv_unsigned (Z_to_bv 64
        (base + 288 * Z.of_nat (length processed))) + 112 -
       (base + 288 * Z.of_nat (length processed))) = 112%nat.
  { rewrite write_success_15078_current_unsigned; lia. }
  iEval (rewrite Hstart) in "Hprefix112 Hsuffix120".
  rewrite ?Hstart ?write_success_15078_current_unsigned ?Z.add_0_r; try lia.
  iFrame "Hprefix112 Hsuffix120".
  repeat iSplit; try iPureIntro; try lia; try done.
  liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve.
  iRename select
    ((_ ↦ₘ∗ take 112
      (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
        transaction))%I) into "HprefixFinal".
  iRename select
    ((_ ↦ₘ Z_to_bv 64
      (little_endian_to_bv 8
        (take 8 (drop (Z.to_nat _)
          (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
            transaction)))))%I) into "HwordFinal". iEval (rewrite (zesu_integer_array_byte_equality (base + 288 * Z.of_nat (length processed)) 112 (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction))) in "HwordFinal".
  iRename select
    ((_ ↦ₘ∗ drop 120
      (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
        transaction))%I) into "HsuffixFinal".
  iPoseProof (mem_mapsto_array_recombine_u64_read
    (base + 288 * Z.of_nat (length processed))
    (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction)
    112 _ _ with
    "HprefixFinal HsuffixFinal HwordFinal [] [] []") as "HarrayFinal".
  { iPureIntro. cbn. lia. }
  { iPureIntro. cbn. lia. }
  { iPureIntro. rewrite H0. lia. }
  iRename select
    (writeSuccessTransactionsCurrentPhaseFrame P sp base transaction
      transactions processed remaining bytes prefix suffix tail)%I
    into "HframeFinal".
  iRename select
    (((∃ vact : valu,
        ⌜valu_has_shape vact (BitsShape 64)⌝ ∗ "x1" ↦ᵣ vact) ∗ _)%I)
    into "HotherExpanded".
  iDestruct "HotherExpanded" as "(Hx1 & Hx3 & Hx4 & Hx22 & _)".
  iAssert (reg_col
    (delete 3%nat writeSuccessTransactions15028OtherRegShapes))%I
    with "[Hx1 Hx3 Hx4 Hx22]" as "HotherFinal".
  { rewrite !reg_col_cons reg_col_nil. iFrame. }
  iRename select ("rv_enable_pmp" ↦ᵣ _)%I into "Hs0".
  iRename select ("rv_enable_misaligned_access" ↦ᵣ _)%I into "Hs1".
  iRename select ("rv_ram_base" ↦ᵣ _)%I into "Hs2".
  iRename select ("rv_ram_size" ↦ᵣ _)%I into "Hs3".
  iRename select ("rv_rom_base" ↦ᵣ _)%I into "Hs4".
  iRename select ("rv_rom_size" ↦ᵣ _)%I into "Hs5".
  iRename select ("rv_clint_base" ↦ᵣ _)%I into "Hs6".
  iRename select ("rv_clint_size" ↦ᵣ _)%I into "Hs7".
  iRename select ("rv_htif_tohost" ↦ᵣ _)%I into "Hs8".
  iRename select ("cur_privilege" ↦ᵣ _)%I into "Hs9".
  iRename select ("misa" ↦ᵣ _)%I into "Hs10".
  iRename select ("mtvec" ↦ᵣ _)%I into "Hs11".
  iRename select ("mstatus" ↦ᵣ _)%I into "Hs12".
  iRename select ("satp" ↦ᵣ _)%I into "Hs13".
  iAssert (reg_col zesu_ram_sys_regs)%I
    with "[Hs0 Hs1 Hs2 Hs3 Hs4 Hs5 Hs6 Hs7 Hs8 Hs9 Hs10 Hs11 Hs12 Hs13]"
    as "HsysFinal".
  { rewrite !reg_col_cons reg_col_nil. iFrame.
    repeat iSplit; iPureIntro; done. }
  iAssert (writeSuccessTransactionsMachine15084 sp base transactions
    processed transaction) with "[-HarrayFinal HframeFinal]"
    as "HmachineFinal".
  { rewrite /writeSuccessTransactionsMachine15084
      /writeSuccessTransactionsMachine15078WithX15AndScratch.
    iFrame "HsysFinal HotherFinal". liARun.
    Unshelve. all: prepare_sidecond.
    all: try assumption. all: try bv_solve. all: try reflexivity. }
  iExists (tail, suffix, prefix, bytes, remaining, processed,
    transactions, transaction, base, sp, tt)ₗ.
  iFrame "HmachineFinal HarrayFinal HframeFinal".
  rewrite /writeSuccessTransactionsLoadFacts.
  repeat iSplit; try iPureIntro; try assumption; try done.
  Unshelve. all: prepare_sidecond.
  all: try assumption. all: try bv_solve. all: try reflexivity.
Qed.

Lemma write_success_transactions_chunk_15080_load
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr 0x15080 (Some IslaTraces.write_success_32.a15080.a15080) -∗
  instr_body 0x15084 (writeSuccessTransactionsAt15084Spec P) -∗
  instr_body 0x15080 (writeSuccessTransactionsAt15080Spec P).
Proof.
  iIntros "#Hinstr Hnext".
  iPoseProof
    (IslaTraces.write_success_32.a15080_spec.a15080_spec 0x15080 with
      "Hinstr") as "Hld".
  rewrite instr_pre'_eq. iIntros "Hentry".
  rewrite /writeSuccessTransactionsAt15080Spec.
  iDestruct "Hentry" as
    (sp base transaction transactions processed remaining
      bytes prefix suffix tail)
    "(Hmachine & Harray & Hframe & Hfacts & _)".
  iPoseProof "Hfacts" as "#HfactsCopy".
  iDestruct "HfactsCopy" as
    "(%Hlength & %HcurrentAlign & %HcurrentLower & %HcurrentUpper &
      %HspAlign & %HspLower & %HspUpper & _)".
  iPoseProof (write_success_transactions_chunk_15080_load_block P sp base
    transaction transactions processed remaining bytes prefix suffix tail)
    as "Hbody".
  iEval (rewrite instr_pre'_eq) in "Hbody".
  iSpecialize ("Hbody" with "Hld Hnext").
  iApply "Hbody".
  rewrite /writeSuccessTransactionsAt15080Block.
  iFrame.
  iPureIntro.
  repeat split; try assumption.
  apply write_success_15078_current_unsigned; lia.
Qed.

Lemma write_success_transactions_chunk_15084_block
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
  instr_body 0x15084 (zesu_sd_spec 0x15084 "x15" "x2" 192) -∗
  instr_body 0x15088 (writeSuccessTransactionsAt15088Spec P) -∗
  instr_body 0x15084 (writeSuccessTransactionsAt15084Block P sp base
    transaction transactions processed remaining bytes prefix suffix tail).
Proof.
  iIntros "Hsd Hnext".
  rewrite instr_pre'_eq. iIntros "Hentry".
  iEval (rewrite /writeSuccessTransactionsAt15084Block) in "Hentry".
  iDestruct "Hentry" as
    "(Hmachine & Harray & Hframe & Hfacts & %Hcurrent & _)".
  iPoseProof "Hfacts" as "#HfactsCopy".
  iDestruct "HfactsCopy" as
    "(%Hlength & %HcurrentAlign & %HcurrentLower & %HcurrentUpper &
      %HspAlign & %HspLower & %HspUpper & _)".
  iEval (rewrite /writeSuccessTransactionsMachine15084
    /writeSuccessTransactionsMachine15078WithX15AndScratch
    /writeSuccessTransactionsScratch15080) in "Hmachine".
  iDestruct "Hmachine" as
    "(Hsys & Hother & Hx21 & Hx2 & Hx5 & Hx6 & Hx7 & Hx8 & Hx9 &
      Hx10 & Hx11 & Hx12 & Hx13 & Hx14 & Hx15 & Hx16 & Hx17 & Hx18 &
      Hx19 & Hx20 & Hx23 & Hx24 & Hx25 & Hx26 & Hx27 & Hx28 & Hx29 &
      Hx30 & Hx31 & Hscratch & _)".
  iDestruct "Hscratch" as
    "(Hlower & H104 & H112 & H120 & H128 & Hscratch136 & H144 & H152 &
      Hscratch160_40 & H200 & Hscratch208 & H216 & H224 & H232 & H240 &
      H248 & H256 & H272 & H280 & H1664 & H1672 & H1680 & _)".
  iDestruct (mem_mapsto_uninit_split 32 with "Hscratch160_40") as
    "[Hscratch160 Hscratch192]".
  { lia. }
  have Hscratch192Address :
    (bv_unsigned sp + 160 + 32 = bv_unsigned sp + 192)%Z by lia.
  iEval (rewrite Hscratch192Address) in "Hscratch192".
  iAssert (writeSuccessTransactionsLoadFacts
    sp base transaction processed bytes)%I as "HfactsRebuilt".
  { rewrite /writeSuccessTransactionsLoadFacts.
    repeat iSplit; try iPureIntro; try assumption; done. }
  iApply ("Hsd" with "[-]").
  rewrite /zesu_sd_spec /rv64_sd_spec.
  iExists
    (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 112),
    sp.
  iFrame "Hsys Hx15 Hx2 Hscratch192".
  iSplit.
  { iPureIntro. exact HspAlign. }
  iSplit.
  { iPureIntro. lia. }
  rewrite instr_pre'_eq.
  iNext. iIntros "Hpost".
  iDestruct "Hpost" as "(HsysPost & Hx15Post & Hx2Post & Hscratch192Post & _)".
  iAssert (writeSuccessTransactionsMachine15088
    sp base transactions processed transaction) with
    "[-Harray Hframe Hnext]"
    as "HmachineFinal".
  { rewrite /writeSuccessTransactionsMachine15088
      /writeSuccessTransactionsScratch15088.
    iFrame "HsysPost Hother Hx2Post Hx5 Hx6 Hx7 Hx8 Hx9 Hx10 Hx11
      Hx12 Hx13 Hx14 Hx15Post Hx16 Hx17 Hx18 Hx19 Hx20 Hx21 Hx23 Hx24
      Hx25 Hx26 Hx27 Hx28 Hx29 Hx30 Hx31 Hlower H104 H112 H120 H128
      Hscratch136 H144 H152 Hscratch160 Hscratch192Post H200 Hscratch208
      H216 H224 H232 H240 H248 H256 H272 H280 H1664 H1672 H1680". }
  iAssert (writeSuccessTransactionsLoadFacts
    sp base transaction processed bytes)%I as "HfactsFinal".
  { rewrite /writeSuccessTransactionsLoadFacts.
    repeat iSplit; try iPureIntro; try assumption; done. }
  iApply "Hnext".
  rewrite /writeSuccessTransactionsAt15088Spec.
  iExists sp, base, transaction, transactions, processed, remaining,
    bytes, prefix, suffix, tail.
  iFrame "HmachineFinal Harray Hframe HfactsFinal".
Qed.

Lemma write_success_transactions_chunk_15084
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr 0x15084 (Some IslaTraces.write_success_32.a15084.a15084) -∗
  instr_body 0x15088 (writeSuccessTransactionsAt15088Spec P) -∗
  instr_body 0x15084 (writeSuccessTransactionsAt15084Spec P).
Proof.
  iIntros "#Hinstr Hnext".
  iPoseProof
    (IslaTraces.write_success_32.a15084_spec.a15084_spec 0x15084 with
      "Hinstr") as "Hsd".
  rewrite instr_pre'_eq. iIntros "Hentry".
  rewrite /writeSuccessTransactionsAt15084Spec.
  iDestruct "Hentry" as
    (sp base transaction transactions processed remaining
      bytes prefix suffix tail)
    "(Hmachine & Harray & Hframe & Hfacts & _)".
  iPoseProof "Hfacts" as "#HfactsCopy".
  iDestruct "HfactsCopy" as
    "(%Hlength & %HcurrentAlign & %HcurrentLower & %HcurrentUpper &
      %HspAlign & %HspLower & %HspUpper & _)".
  iPoseProof (write_success_transactions_chunk_15084_block P sp base
    transaction transactions processed remaining bytes prefix suffix tail)
    as "Hbody".
  iEval (rewrite instr_pre'_eq) in "Hbody".
  iSpecialize ("Hbody" with "Hsd Hnext").
  iApply "Hbody".
  rewrite /writeSuccessTransactionsAt15084Block.
  iFrame.
  iPureIntro.
  repeat split; try assumption.
  apply write_success_15078_current_unsigned; lia.
Qed.

Lemma write_success_transactions_chunk_1507c_block
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
  instr_body 0x1507c (zesu_sd_spec 0x1507c "x15" "x2" 200) -∗
  instr_body 0x15080 (writeSuccessTransactionsAt15080Spec P) -∗
  instr_body 0x1507c (writeSuccessTransactionsAt1507cBlock P sp base
    transaction transactions processed remaining bytes prefix suffix tail).
Proof.
  iIntros "Hsd Hnext".
  rewrite instr_pre'_eq. iIntros "Hentry".
  iEval (rewrite /writeSuccessTransactionsAt1507cBlock) in "Hentry".
  iDestruct "Hentry" as
    "(Hmachine & Harray & Hframe & Hfacts & %Hcurrent & _)".
  iPoseProof "Hfacts" as "#HfactsCopy".
  iDestruct "HfactsCopy" as
    "(%Hlength & %HcurrentAlign & %HcurrentLower & %HcurrentUpper &
      %HspAlign & %HspLower & %HspUpper & _)".
  iEval (rewrite /writeSuccessTransactionsMachine1507c
    /writeSuccessTransactionsMachine15078WithX15AndScratch
    /writeSuccessTransactionsScratch15078) in "Hmachine".
  iDestruct "Hmachine" as
    "(Hsys & Hother & Hx21 & Hx2 & Hx5 & Hx6 & Hx7 & Hx8 & Hx9 &
      Hx10 & Hx11 & Hx12 & Hx13 & Hx14 & Hx15 & Hx16 & Hx17 & Hx18 &
      Hx19 & Hx20 & Hx23 & Hx24 & Hx25 & Hx26 & Hx27 & Hx28 & Hx29 &
      Hx30 & Hx31 & Hscratch & _)".
  iDestruct "Hscratch" as
    "(Hlower & H104 & H112 & H120 & H128 & Hscratch136 & H144 & H152 &
      Hscratch160_56 & H216 & H224 & H232 & H240 & H248 & H256 & H272 &
      H280 & H1664 & H1672 & H1680 & _)".
  iDestruct (mem_mapsto_uninit_split 40 with "Hscratch160_56") as
    "[Hscratch160 Hscratch200_16]".
  { lia. }
  have Hscratch200Address :
    (bv_unsigned sp + 160 + 40 = bv_unsigned sp + 200)%Z by lia.
  iEval (rewrite Hscratch200Address) in "Hscratch200_16".
  iDestruct (mem_mapsto_uninit_split 8 with "Hscratch200_16") as
    "[Hscratch200 Hscratch208]".
  { lia. }
  have Hscratch208Address :
    (bv_unsigned sp + 200 + 8 = bv_unsigned sp + 208)%Z by lia.
  iEval (rewrite Hscratch208Address) in "Hscratch208".
  iAssert (writeSuccessTransactionsLoadFacts
    sp base transaction processed bytes)%I as "HfactsRebuilt".
  { rewrite /writeSuccessTransactionsLoadFacts.
    repeat iSplit; try iPureIntro; try assumption; done. }
  iApply ("Hsd" with "[-]").
  rewrite /zesu_sd_spec /rv64_sd_spec.
  iExists
    (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 104),
    sp.
  iFrame "Hsys Hx15 Hx2 Hscratch200".
  iSplit.
  { iPureIntro. exact HspAlign. }
  iSplit.
  { iPureIntro. lia. }
  rewrite instr_pre'_eq.
  iNext. iIntros "Hpost".
  iDestruct "Hpost" as "(HsysPost & Hx15Post & Hx2Post & Hscratch200Post & _)".
  iAssert (writeSuccessTransactionsMachine15080
    sp base transactions processed transaction) with
    "[-Harray Hframe Hnext]"
    as "HmachineFinal".
  { rewrite /writeSuccessTransactionsMachine15080
      /writeSuccessTransactionsMachine15078WithX15AndScratch
      /writeSuccessTransactionsScratch15080.
    iFrame "HsysPost Hother Hx21 Hx2Post Hx5 Hx6 Hx7 Hx8 Hx9 Hx10 Hx11
      Hx12 Hx13 Hx14 Hx15Post Hx16 Hx17 Hx18 Hx19 Hx20 Hx23 Hx24 Hx25
      Hx26 Hx27 Hx28 Hx29 Hx30 Hx31 Hlower H104 H112 H120 H128
      Hscratch136 H144 H152 Hscratch160 Hscratch200Post Hscratch208 H216
      H224 H232 H240 H248 H256 H272 H280 H1664 H1672 H1680". }
  iAssert (writeSuccessTransactionsLoadFacts
    sp base transaction processed bytes)%I as "HfactsFinal".
  { rewrite /writeSuccessTransactionsLoadFacts.
    repeat iSplit; try iPureIntro; try assumption; done. }
  iApply "Hnext".
  rewrite /writeSuccessTransactionsAt15080Spec.
  iExists sp, base, transaction, transactions, processed, remaining,
    bytes, prefix, suffix, tail.
  iFrame "HmachineFinal Harray Hframe HfactsFinal".
Qed.

Lemma write_success_transactions_chunk_1507c
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr 0x1507c (Some IslaTraces.write_success_32.a1507c.a1507c) -∗
  instr_body 0x15080 (writeSuccessTransactionsAt15080Spec P) -∗
  instr_body 0x1507c (writeSuccessTransactionsAt1507cSpec P).
Proof.
  iIntros "#Hinstr Hnext".
  iPoseProof
    (IslaTraces.write_success_32.a1507c_spec.a1507c_spec 0x1507c with
      "Hinstr") as "Hsd".
  rewrite instr_pre'_eq. iIntros "Hentry".
  rewrite /writeSuccessTransactionsAt1507cSpec.
  iDestruct "Hentry" as
    (sp base transaction transactions processed remaining
      bytes prefix suffix tail)
    "(Hmachine & Harray & Hframe & Hfacts & _)".
  iPoseProof "Hfacts" as "#HfactsCopy".
  iDestruct "HfactsCopy" as
    "(%Hlength & %HcurrentAlign & %HcurrentLower & %HcurrentUpper &
      %HspAlign & %HspLower & %HspUpper & _)".
  iPoseProof (write_success_transactions_chunk_1507c_block P sp base
    transaction transactions processed remaining bytes prefix suffix tail)
    as "Hbody".
  iEval (rewrite instr_pre'_eq) in "Hbody".
  iSpecialize ("Hbody" with "Hsd Hnext").
  iApply "Hbody".
  rewrite /writeSuccessTransactionsAt1507cBlock.
  iFrame.
  iPureIntro.
  repeat split; try assumption.
  apply write_success_15078_current_unsigned; lia.
Qed.

Lemma write_success_transactions_chunk_15078_load_block
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
  instr_body 0x15078
    (zesu_ld_byte_array_at_spec 0x15078 "x15" "x10" 104 0 104) -∗
  instr_body 0x1507c (writeSuccessTransactionsAt1507cSpec P) -∗
  instr_body 0x15078 (writeSuccessTransactionsAt15078Block P sp base
    transaction transactions processed remaining bytes prefix suffix tail).
Proof.
  move => *.
  iStartProof.
  iIntros "Hnext".
  liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: rewrite ?write_success_15078_current_unsigned; try lia.
  all: iExists
    (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction,
      tt)ₗ.
  all: try prepare_sidecond.
  all: try assumption.
  all: rewrite ?write_success_15078_current_unsigned; try lia.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try solve_zesu_ld_array_at.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve. all: repeat iIntros "?"; liARun.
  Unshelve.
  iExists
    (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction,
      tt)ₗ.
  iIntros "Hprefix104 Hsuffix112".
  cbn.
  have Hstart :
    Z.to_nat
      (bv_unsigned (Z_to_bv 64
        (base + 288 * Z.of_nat (length processed))) + 104 -
       (base + 288 * Z.of_nat (length processed))) = 104%nat.
  { rewrite write_success_15078_current_unsigned; lia. }
  iEval (rewrite Hstart) in "Hprefix104 Hsuffix112".
  rewrite ?Hstart ?write_success_15078_current_unsigned ?Z.add_0_r; try lia.
  iFrame "Hprefix104 Hsuffix112".
  repeat iSplit; try iPureIntro; try lia; try done.
  liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve.
  iRename select
    ((_ ↦ₘ∗ take 104
      (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
        transaction))%I) into "HprefixFinal".
  iRename select
    ((_ ↦ₘ Z_to_bv 64
      (little_endian_to_bv 8
        (take 8 (drop (Z.to_nat _)
          (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
            transaction)))))%I) into "HwordFinal". iEval (rewrite (zesu_integer_array_byte_equality (base + 288 * Z.of_nat (length processed)) 104 (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction))) in "HwordFinal".
  iRename select
    ((_ ↦ₘ∗ drop 112
      (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
        transaction))%I) into "HsuffixFinal".
  iPoseProof (mem_mapsto_array_recombine_u64_read
    (base + 288 * Z.of_nat (length processed))
    (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction)
    104 _ _ with
    "HprefixFinal HsuffixFinal HwordFinal [] [] []") as "HarrayFinal".
  { iPureIntro. cbn. lia. }
  { iPureIntro. cbn. lia. }
  { iPureIntro. rewrite H0. lia. }
  iRename select
    (writeSuccessTransactionsCurrentPhaseFrame P sp base transaction
      transactions processed remaining bytes prefix suffix tail)%I
    into "HframeFinal".
  iRename select
    (((∃ vact : valu,
        ⌜valu_has_shape vact (BitsShape 64)⌝ ∗ "x1" ↦ᵣ vact) ∗ _)%I)
    into "HotherExpanded".
  iDestruct "HotherExpanded" as "(Hx1 & Hx3 & Hx4 & Hx22 & _)".
  iAssert (reg_col
    (delete 3%nat writeSuccessTransactions15028OtherRegShapes))%I
    with "[Hx1 Hx3 Hx4 Hx22]" as "HotherFinal".
  { rewrite !reg_col_cons reg_col_nil. iFrame. }
  iRename select ("rv_enable_pmp" ↦ᵣ _)%I into "Hs0".
  iRename select ("rv_enable_misaligned_access" ↦ᵣ _)%I into "Hs1".
  iRename select ("rv_ram_base" ↦ᵣ _)%I into "Hs2".
  iRename select ("rv_ram_size" ↦ᵣ _)%I into "Hs3".
  iRename select ("rv_rom_base" ↦ᵣ _)%I into "Hs4".
  iRename select ("rv_rom_size" ↦ᵣ _)%I into "Hs5".
  iRename select ("rv_clint_base" ↦ᵣ _)%I into "Hs6".
  iRename select ("rv_clint_size" ↦ᵣ _)%I into "Hs7".
  iRename select ("rv_htif_tohost" ↦ᵣ _)%I into "Hs8".
  iRename select ("cur_privilege" ↦ᵣ _)%I into "Hs9".
  iRename select ("misa" ↦ᵣ _)%I into "Hs10".
  iRename select ("mtvec" ↦ᵣ _)%I into "Hs11".
  iRename select ("mstatus" ↦ᵣ _)%I into "Hs12".
  iRename select ("satp" ↦ᵣ _)%I into "Hs13".
  iAssert (reg_col zesu_ram_sys_regs)%I
    with "[Hs0 Hs1 Hs2 Hs3 Hs4 Hs5 Hs6 Hs7 Hs8 Hs9 Hs10 Hs11 Hs12 Hs13]"
    as "HsysFinal".
  { rewrite !reg_col_cons reg_col_nil. iFrame.
    repeat iSplit; iPureIntro; done. }
  iAssert (writeSuccessTransactionsMachine1507c sp base transactions
    processed transaction) with "[-HarrayFinal HframeFinal]"
    as "HmachineFinal".
  { rewrite /writeSuccessTransactionsMachine1507c
      /writeSuccessTransactionsMachine15078WithX15AndScratch.
    iFrame "HsysFinal HotherFinal". liARun.
    Unshelve. all: prepare_sidecond.
    all: try assumption. all: try bv_solve. all: try reflexivity. }
  iExists (tail, suffix, prefix, bytes, remaining, processed,
    transactions, transaction, base, sp, tt)ₗ.
  iFrame "HmachineFinal HarrayFinal HframeFinal".
  rewrite /writeSuccessTransactionsLoadFacts.
  repeat iSplit; try iPureIntro; try assumption; try done.
  Unshelve. all: prepare_sidecond.
  all: try assumption. all: try bv_solve. all: try reflexivity.
Qed.

Lemma write_success_transactions_chunk_15078_load
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr 0x15078 (Some IslaTraces.write_success_32.a15078.a15078) -∗
  instr_body 0x1507c (writeSuccessTransactionsAt1507cSpec P) -∗
  instr_body 0x15078 (writeSuccessTransactionsAt15078Spec P).
Proof.
  iIntros "#Hinstr Hnext".
  iPoseProof
    (IslaTraces.write_success_32.a15078_spec.a15078_spec 0x15078 with
      "Hinstr") as "Hld".
  rewrite instr_pre'_eq. iIntros "Hentry".
  rewrite /writeSuccessTransactionsAt15078Spec.
  iDestruct "Hentry" as
    (sp base transaction transactions processed remaining
      bytes prefix suffix tail)
    "(Hmachine & Harray & Hframe & Hfacts & _)".
  iPoseProof "Hfacts" as "#HfactsCopy".
  iDestruct "HfactsCopy" as
    "(%Hlength & %HcurrentAlign & %HcurrentLower & %HcurrentUpper &
      %HspAlign & %HspLower & %HspUpper & _)".
  iPoseProof (write_success_transactions_chunk_15078_load_block P sp base
    transaction transactions processed remaining bytes prefix suffix tail)
    as "Hbody".
  iEval (rewrite instr_pre'_eq) in "Hbody".
  iSpecialize ("Hbody" with "Hld Hnext").
  iApply "Hbody".
  rewrite /writeSuccessTransactionsAt15078Block.
  iFrame.
  iPureIntro.
  repeat split; try assumption.
  apply write_success_15078_current_unsigned; lia.
Qed.

Lemma write_success_transactions_chunk_15078
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x15088 (writeSuccessTransactionsAt15088Spec P) -∗
  instr_body 0x15078 (writeSuccessTransactionsAt15078Spec P).
Proof.
  iIntros "#Hlookup _ Hnext".
  iPoseProof "Hlookup" as "#Hlookup78".
  iEval (rewrite /instr_lookup_resources) in "Hlookup78".
  iPoseProof ("Hlookup78" $! 0x15084) as "Hinstr84".
  iSpecialize ("Hinstr84" with "[]").
  { iPureIntro. rewrite Index.lookup_a15084. done. }
  iEval (rewrite Index.lookup_a15084) in "Hinstr84".
  iPoseProof (write_success_transactions_chunk_15084 P with
    "Hinstr84 Hnext") as "H84".
  iPoseProof ("Hlookup78" $! 0x15080) as "Hinstr80".
  iSpecialize ("Hinstr80" with "[]").
  { iPureIntro. rewrite Index.lookup_a15080. done. }
  iEval (rewrite Index.lookup_a15080) in "Hinstr80".
  iPoseProof (write_success_transactions_chunk_15080_load P with
    "Hinstr80 H84") as "H80".
  iPoseProof ("Hlookup78" $! 0x1507c) as "Hinstr7c".
  iSpecialize ("Hinstr7c" with "[]").
  { iPureIntro. rewrite Index.lookup_a1507c. done. }
  iEval (rewrite Index.lookup_a1507c) in "Hinstr7c".
  iPoseProof (write_success_transactions_chunk_1507c P with
    "Hinstr7c H80") as "H7c".
  iPoseProof ("Hlookup78" $! 0x15078) as "Hinstr78".
  iSpecialize ("Hinstr78" with "[]").
  { iPureIntro. rewrite Index.lookup_a15078. done. }
  iEval (rewrite Index.lookup_a15078) in "Hinstr78".
  iApply (write_success_transactions_chunk_15078_load P with
    "Hinstr78 H7c").
Qed.
