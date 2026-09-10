Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Specs.
Require Import ZesuSsz.Contracts.IslarisCode.
From IslaTraces.write_success_32 Require Import
  a15048_spec a1504c_spec a15050_spec a15054_spec a15058_spec.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary14f1c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15028.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15044.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15048.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary1505c.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.
#[local] Typeclasses Opaque writeSuccessTransactionsCurrentPhaseFrame.

Lemma write_success_15048_current_unsigned (current : Z) :
  (0 <= current)%Z ->
  (current < 2 ^ 64)%Z ->
  bv_unsigned (Z_to_bv 64 current) = current.
Proof. intros. bv_solve. Qed.

#[local] Hint Rewrite write_success_15048_current_unsigned using lia :
  lithium_rewrite.

Definition writeSuccessTransactionsScratch15050 `{!islaG Sigma} `{!threadG}
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
   (bv_unsigned sp + 136) ↦ₘ? 16 ∗
   (bv_unsigned sp + 152) ↦ₘ
     WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 80 ∗
   (bv_unsigned sp + 160) ↦ₘ? 64 ∗
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

Global Instance : LithiumUnfold (@writeSuccessTransactionsScratch15050) := I.

Definition writeSuccessTransactionsMachine1504c `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (transactions processed :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction) :
    iProp Sigma :=
  writeSuccessTransactionsMachine15048WithX16AndScratch
    sp base transactions processed transaction
    (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
      transaction 80)
    (writeSuccessTransactionsScratch15044
      sp base transactions processed transaction).

Global Instance : LithiumUnfold (@writeSuccessTransactionsMachine1504c) := I.

Definition writeSuccessTransactionsMachine15050 `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (transactions processed :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction) :
    iProp Sigma :=
  writeSuccessTransactionsMachine15048WithX16AndScratch
    sp base transactions processed transaction
    (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
      transaction 80)
    (writeSuccessTransactionsScratch15050
      sp base transactions processed transaction).

Global Instance : LithiumUnfold (@writeSuccessTransactionsMachine15050) := I.

Definition writeSuccessTransactionsMachine15054 `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (transactions processed :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction) :
    iProp Sigma :=
  writeSuccessTransactionsMachine15048WithX16AndScratch
    sp base transactions processed transaction
    (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
      transaction 88)
    (writeSuccessTransactionsScratch15050
      sp base transactions processed transaction).

Global Instance : LithiumUnfold (@writeSuccessTransactionsMachine15054) := I.

Definition writeSuccessTransactionsMachine15058 `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (transactions processed :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction) :
    iProp Sigma :=
  writeSuccessTransactionsMachine15048WithX16AndScratch
    sp base transactions processed transaction
    (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
      transaction 88)
    (writeSuccessTransactionsScratch1505c
      sp base transactions processed transaction).

Global Instance : LithiumUnfold (@writeSuccessTransactionsMachine15058) := I.

Definition writeSuccessTransactionsAt1504cSpec `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z)
      (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
      (transactions processed remaining :
        list WriteSuccessTransactionsSpec.writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec),
    writeSuccessTransactionsMachine1504c
      sp base transactions processed transaction ∗
    (base + 288 * Z.of_nat (length processed)) ↦ₘ∗
      WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction ∗
    writeSuccessTransactionsCurrentPhaseFrame P sp base transaction
      transactions processed remaining bytes prefix suffix tail ∗
    writeSuccessTransactionsLoadFacts
      sp base transaction processed bytes ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsAt1504cSpec) := I.

Definition writeSuccessTransactionsAt15050Spec `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z)
      (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
      (transactions processed remaining :
        list WriteSuccessTransactionsSpec.writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec),
    writeSuccessTransactionsMachine15050
      sp base transactions processed transaction ∗
    (base + 288 * Z.of_nat (length processed)) ↦ₘ∗
      WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction ∗
    writeSuccessTransactionsCurrentPhaseFrame P sp base transaction
      transactions processed remaining bytes prefix suffix tail ∗
    writeSuccessTransactionsLoadFacts
      sp base transaction processed bytes ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsAt15050Spec) := I.

Definition writeSuccessTransactionsAt15054Spec `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z)
      (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
      (transactions processed remaining :
        list WriteSuccessTransactionsSpec.writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec),
    writeSuccessTransactionsMachine15054
      sp base transactions processed transaction ∗
    (base + 288 * Z.of_nat (length processed)) ↦ₘ∗
      WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction ∗
    writeSuccessTransactionsCurrentPhaseFrame P sp base transaction
      transactions processed remaining bytes prefix suffix tail ∗
    writeSuccessTransactionsLoadFacts
      sp base transaction processed bytes ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsAt15054Spec) := I.

Definition writeSuccessTransactionsAt15058Spec `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z)
      (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
      (transactions processed remaining :
        list WriteSuccessTransactionsSpec.writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec),
    writeSuccessTransactionsMachine15058
      sp base transactions processed transaction ∗
    (base + 288 * Z.of_nat (length processed)) ↦ₘ∗
      WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction ∗
    writeSuccessTransactionsCurrentPhaseFrame P sp base transaction
      transactions processed remaining bytes prefix suffix tail ∗
    writeSuccessTransactionsLoadFacts
      sp base transaction processed bytes ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsAt15058Spec) := I.

Definition writeSuccessTransactionsAt15048Block
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
    iProp Sigma :=
  (writeSuccessTransactionsMachine15048
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

Global Instance : LithiumUnfold (@writeSuccessTransactionsAt15048Block) := I.

Definition writeSuccessTransactionsAt1504cBlock
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
    iProp Sigma :=
  (writeSuccessTransactionsMachine1504c
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

Global Instance : LithiumUnfold (@writeSuccessTransactionsAt1504cBlock) := I.

Definition writeSuccessTransactionsAt15050Block
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
    iProp Sigma :=
  (writeSuccessTransactionsMachine15050
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

Global Instance : LithiumUnfold (@writeSuccessTransactionsAt15050Block) := I.

Definition writeSuccessTransactionsAt15054Block
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
    iProp Sigma :=
  (writeSuccessTransactionsMachine15054
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

Global Instance : LithiumUnfold (@writeSuccessTransactionsAt15054Block) := I.

Definition writeSuccessTransactionsAt15058Block
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
    iProp Sigma :=
  (writeSuccessTransactionsMachine15058
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

Global Instance : LithiumUnfold (@writeSuccessTransactionsAt15058Block) := I.

Lemma write_success_transactions_chunk_15058_load_block
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
  instr_body 0x15058
    (zesu_ld_byte_array_at_spec 0x15058 "x16" "x10" 96 0 96) -∗
  instr_body 0x1505c (writeSuccessTransactionsAt1505cSpec P) -∗
  instr_body 0x15058 (writeSuccessTransactionsAt15058Block P sp base
    transaction transactions processed remaining bytes prefix suffix tail).
Proof.
  move => *.
  iStartProof.
  iIntros "Hnext".
  liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: rewrite ?write_success_15048_current_unsigned; try lia.
  all: iExists
    (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction,
      tt)ₗ.
  all: try prepare_sidecond.
  all: try assumption.
  all: rewrite ?write_success_15048_current_unsigned; try lia.
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
  iIntros "Hprefix96 Hsuffix104".
  cbn.
  have Hstart :
    Z.to_nat
      (bv_unsigned (Z_to_bv 64
        (base + 288 * Z.of_nat (length processed))) + 96 -
       (base + 288 * Z.of_nat (length processed))) = 96%nat.
  { rewrite H7. lia. }
  iEval (rewrite Hstart) in "Hprefix96 Hsuffix104".
  rewrite Hstart H7 !Z.add_0_r.
  iFrame "Hprefix96 Hsuffix104".
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
    ((_ ↦ₘ∗ take 96
      (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
        transaction))%I) into "HprefixFinal".
  iRename select
    ((_ ↦ₘ Z_to_bv 64
      (little_endian_to_bv 8
        (take 8 (drop 96
          (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
            transaction)))))%I) into "HwordFinal".
  iRename select
    ((_ ↦ₘ∗ drop 104
      (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
        transaction))%I) into "HsuffixFinal".
  iPoseProof (mem_mapsto_array_recombine_u64_read
    (base + 288 * Z.of_nat (length processed))
    (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction)
    96 _ _ with
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
  iAssert (writeSuccessTransactionsMachine1505c sp base transactions
    processed transaction) with "[-HarrayFinal HframeFinal]"
    as "HmachineFinal".
  { rewrite /writeSuccessTransactionsMachine1505c
      /writeSuccessTransactionsMachine15048WithX16AndScratch.
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

Lemma write_success_transactions_chunk_15058_load
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr 0x15058 (Some IslaTraces.write_success_32.a15058.a15058) -∗
  instr_body 0x1505c (writeSuccessTransactionsAt1505cSpec P) -∗
  instr_body 0x15058 (writeSuccessTransactionsAt15058Spec P).
Proof.
  iIntros "#Hinstr Hnext".
  iPoseProof
    (IslaTraces.write_success_32.a15058_spec.a15058_spec 0x15058 with
      "Hinstr") as "Hld".
  rewrite instr_pre'_eq. iIntros "Hentry".
  rewrite /writeSuccessTransactionsAt15058Spec.
  iDestruct "Hentry" as
    (sp base transaction transactions processed remaining
      bytes prefix suffix tail)
    "(Hmachine & Harray & Hframe & Hfacts & _)".
  iPoseProof "Hfacts" as "#HfactsCopy".
  iDestruct "HfactsCopy" as
    "(%Hlength & %HcurrentAlign & %HcurrentLower & %HcurrentUpper &
      %HspAlign & %HspLower & %HspUpper & _)".
  iPoseProof (write_success_transactions_chunk_15058_load_block P sp base
    transaction transactions processed remaining bytes prefix suffix tail)
    as "Hbody".
  iEval (rewrite instr_pre'_eq) in "Hbody".
  iSpecialize ("Hbody" with "Hld Hnext").
  iApply "Hbody".
  rewrite /writeSuccessTransactionsAt15058Block.
  iFrame.
  iPureIntro.
  repeat split; try assumption.
  apply write_success_15048_current_unsigned; lia.
Qed.

Lemma write_success_transactions_chunk_15054_block
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
  instr_body 0x15054 (zesu_sd_spec 0x15054 "x16" "x2" 144) -∗
  instr_body 0x15058 (writeSuccessTransactionsAt15058Spec P) -∗
  instr_body 0x15054 (writeSuccessTransactionsAt15054Block P sp base
    transaction transactions processed remaining bytes prefix suffix tail).
Proof.
  iIntros "Hsd Hnext".
  rewrite instr_pre'_eq. iIntros "Hentry".
  iEval (rewrite /writeSuccessTransactionsAt15054Block) in "Hentry".
  iDestruct "Hentry" as
    "(Hmachine & Harray & Hframe & Hfacts & %Hcurrent & _)".
  iPoseProof "Hfacts" as "#HfactsCopy".
  iDestruct "HfactsCopy" as
    "(%Hlength & %HcurrentAlign & %HcurrentLower & %HcurrentUpper &
      %HspAlign & %HspLower & %HspUpper & _)".
  iEval (rewrite /writeSuccessTransactionsMachine15054
    /writeSuccessTransactionsMachine15048WithX16AndScratch
    /writeSuccessTransactionsScratch15050) in "Hmachine".
  iDestruct "Hmachine" as
    "(Hsys & Hother & Hx21 & Hx2 & Hx5 & Hx6 & Hx7 & Hx8 & Hx9 &
      Hx10 & Hx11 & Hx12 & Hx13 & Hx14 & Hx15 & Hx16 & Hx17 & Hx18 &
      Hx19 & Hx20 & Hx23 & Hx24 & Hx25 & Hx26 & Hx27 & Hx28 & Hx29 &
      Hx30 & Hx31 & Hscratch & _)".
  iDestruct "Hscratch" as
    "(Hlower & H104 & H112 & H120 & H128 & Hscratch136_16 & H152 &
      H160 & H224 & H232 & H240 & H248 & H256 & H272 & H280 & H1664 &
      H1672 & H1680 & _)".
  iDestruct (mem_mapsto_uninit_split 8 with "Hscratch136_16") as
    "[Hscratch136 Hscratch144]".
  { lia. }
  have Hscratch144Address :
    (bv_unsigned sp + 136 + 8 = bv_unsigned sp + 144)%Z by lia.
  iEval (rewrite Hscratch144Address) in "Hscratch144".
  iAssert (writeSuccessTransactionsLoadFacts
    sp base transaction processed bytes)%I as "HfactsRebuilt".
  { rewrite /writeSuccessTransactionsLoadFacts.
    repeat iSplit; try iPureIntro; try assumption; done. }
  iApply ("Hsd" with "[-]").
  rewrite /zesu_sd_spec /rv64_sd_spec.
  iExists
    (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 88),
    sp.
  iFrame "Hsys Hx16 Hx2 Hscratch144".
  iSplit.
  { iPureIntro. exact HspAlign. }
  iSplit.
  { iPureIntro. lia. }
  rewrite instr_pre'_eq.
  iNext. iIntros "Hpost".
  iDestruct "Hpost" as "(HsysPost & Hx16Post & Hx2Post & Hscratch144Post & _)".
  iAssert (writeSuccessTransactionsMachine15058
    sp base transactions processed transaction) with
    "[-Harray Hframe Hnext]"
    as "HmachineFinal".
  { rewrite /writeSuccessTransactionsMachine15058
      /writeSuccessTransactionsMachine15048WithX16AndScratch
      /writeSuccessTransactionsScratch1505c.
    iFrame "HsysPost Hother Hx21 Hx2Post Hx5 Hx6 Hx7 Hx8 Hx9 Hx10 Hx11
      Hx12 Hx13 Hx14 Hx15 Hx16Post Hx17 Hx18 Hx19 Hx20 Hx23 Hx24 Hx25
      Hx26 Hx27 Hx28 Hx29 Hx30 Hx31 Hlower H104 H112 H120 H128
      Hscratch136 Hscratch144Post H152 H160 H224 H232 H240 H248 H256
      H272 H280 H1664 H1672 H1680". }
  iAssert (writeSuccessTransactionsLoadFacts
    sp base transaction processed bytes)%I as "HfactsFinal".
  { rewrite /writeSuccessTransactionsLoadFacts.
    repeat iSplit; try iPureIntro; try assumption; done. }
  iApply "Hnext".
  rewrite /writeSuccessTransactionsAt15058Spec.
  iExists sp, base, transaction, transactions, processed, remaining,
    bytes, prefix, suffix, tail.
  iFrame "HmachineFinal Harray Hframe HfactsFinal".
Qed.

Lemma write_success_transactions_chunk_15054
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr 0x15054 (Some IslaTraces.write_success_32.a15054.a15054) -∗
  instr_body 0x15058 (writeSuccessTransactionsAt15058Spec P) -∗
  instr_body 0x15054 (writeSuccessTransactionsAt15054Spec P).
Proof.
  iIntros "#Hinstr Hnext".
  iPoseProof
    (IslaTraces.write_success_32.a15054_spec.a15054_spec 0x15054 with
      "Hinstr") as "Hsd".
  rewrite instr_pre'_eq. iIntros "Hentry".
  rewrite /writeSuccessTransactionsAt15054Spec.
  iDestruct "Hentry" as
    (sp base transaction transactions processed remaining
      bytes prefix suffix tail)
    "(Hmachine & Harray & Hframe & Hfacts & _)".
  iPoseProof "Hfacts" as "#HfactsCopy".
  iDestruct "HfactsCopy" as
    "(%Hlength & %HcurrentAlign & %HcurrentLower & %HcurrentUpper &
      %HspAlign & %HspLower & %HspUpper & _)".
  iPoseProof (write_success_transactions_chunk_15054_block P sp base
    transaction transactions processed remaining bytes prefix suffix tail)
    as "Hbody".
  iEval (rewrite instr_pre'_eq) in "Hbody".
  iSpecialize ("Hbody" with "Hsd Hnext").
  iApply "Hbody".
  rewrite /writeSuccessTransactionsAt15054Block.
  iFrame.
  iPureIntro.
  repeat split; try assumption.
  apply write_success_15048_current_unsigned; lia.
Qed.

Lemma write_success_transactions_chunk_15050_load_block
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
  instr_body 0x15050
    (zesu_ld_byte_array_at_spec 0x15050 "x16" "x10" 88 0 88) -∗
  instr_body 0x15054 (writeSuccessTransactionsAt15054Spec P) -∗
  instr_body 0x15050 (writeSuccessTransactionsAt15050Block P sp base
    transaction transactions processed remaining bytes prefix suffix tail).
Proof.
  move => *.
  iStartProof.
  iIntros "Hnext".
  liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: rewrite ?write_success_15048_current_unsigned; try lia.
  all: iExists
    (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction,
      tt)ₗ.
  all: try prepare_sidecond.
  all: try assumption.
  all: rewrite ?write_success_15048_current_unsigned; try lia.
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
  iIntros "Hprefix88 Hsuffix96".
  cbn.
  have Hstart :
    Z.to_nat
      (bv_unsigned (Z_to_bv 64
        (base + 288 * Z.of_nat (length processed))) + 88 -
       (base + 288 * Z.of_nat (length processed))) = 88%nat.
  { rewrite H7. lia. }
  iEval (rewrite Hstart) in "Hprefix88 Hsuffix96".
  rewrite Hstart H7 !Z.add_0_r.
  iFrame "Hprefix88 Hsuffix96".
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
    ((_ ↦ₘ∗ take 88
      (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
        transaction))%I) into "HprefixFinal".
  iRename select
    ((_ ↦ₘ Z_to_bv 64
      (little_endian_to_bv 8
        (take 8 (drop 88
          (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
            transaction)))))%I) into "HwordFinal".
  iRename select
    ((_ ↦ₘ∗ drop 96
      (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
        transaction))%I) into "HsuffixFinal".
  iPoseProof (mem_mapsto_array_recombine_u64_read
    (base + 288 * Z.of_nat (length processed))
    (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction)
    88 _ _ with
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
  iAssert (writeSuccessTransactionsMachine15054 sp base transactions
    processed transaction) with "[-HarrayFinal HframeFinal]"
    as "HmachineFinal".
  { rewrite /writeSuccessTransactionsMachine15054
      /writeSuccessTransactionsMachine15048WithX16AndScratch.
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

Lemma write_success_transactions_chunk_15050_load
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr 0x15050 (Some IslaTraces.write_success_32.a15050.a15050) -∗
  instr_body 0x15054 (writeSuccessTransactionsAt15054Spec P) -∗
  instr_body 0x15050 (writeSuccessTransactionsAt15050Spec P).
Proof.
  iIntros "#Hinstr Hnext".
  iPoseProof
    (IslaTraces.write_success_32.a15050_spec.a15050_spec 0x15050 with
      "Hinstr") as "Hld".
  rewrite instr_pre'_eq. iIntros "Hentry".
  rewrite /writeSuccessTransactionsAt15050Spec.
  iDestruct "Hentry" as
    (sp base transaction transactions processed remaining
      bytes prefix suffix tail)
    "(Hmachine & Harray & Hframe & Hfacts & _)".
  iPoseProof "Hfacts" as "#HfactsCopy".
  iDestruct "HfactsCopy" as
    "(%Hlength & %HcurrentAlign & %HcurrentLower & %HcurrentUpper &
      %HspAlign & %HspLower & %HspUpper & _)".
  iPoseProof (write_success_transactions_chunk_15050_load_block P sp base
    transaction transactions processed remaining bytes prefix suffix tail)
    as "Hbody".
  iEval (rewrite instr_pre'_eq) in "Hbody".
  iSpecialize ("Hbody" with "Hld Hnext").
  iApply "Hbody".
  rewrite /writeSuccessTransactionsAt15050Block.
  iFrame.
  iPureIntro.
  repeat split; try assumption.
  apply write_success_15048_current_unsigned; lia.
Qed.

Lemma write_success_transactions_chunk_1504c_block
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
  instr_body 0x1504c (zesu_sd_spec 0x1504c "x16" "x2" 152) -∗
  instr_body 0x15050 (writeSuccessTransactionsAt15050Spec P) -∗
  instr_body 0x1504c (writeSuccessTransactionsAt1504cBlock P sp base
    transaction transactions processed remaining bytes prefix suffix tail).
Proof.
  iIntros "Hsd Hnext".
  rewrite instr_pre'_eq. iIntros "Hentry".
  iEval (rewrite /writeSuccessTransactionsAt1504cBlock) in "Hentry".
  iDestruct "Hentry" as
    "(Hmachine & Harray & Hframe & Hfacts & %Hcurrent & _)".
  iPoseProof "Hfacts" as "#HfactsCopy".
  iDestruct "HfactsCopy" as
    "(%Hlength & %HcurrentAlign & %HcurrentLower & %HcurrentUpper &
      %HspAlign & %HspLower & %HspUpper & _)".
  iEval (rewrite /writeSuccessTransactionsMachine1504c
    /writeSuccessTransactionsMachine15048WithX16AndScratch
    /writeSuccessTransactionsScratch15044) in "Hmachine".
  iDestruct "Hmachine" as
    "(Hsys & Hother & Hx21 & Hx2 & Hx5 & Hx6 & Hx7 & Hx8 & Hx9 &
      Hx10 & Hx11 & Hx12 & Hx13 & Hx14 & Hx15 & Hx16 & Hx17 & Hx18 &
      Hx19 & Hx20 & Hx23 & Hx24 & Hx25 & Hx26 & Hx27 & Hx28 & Hx29 &
      Hx30 & Hx31 & Hscratch & _)".
  iDestruct "Hscratch" as
    "(Hlower & H104 & H112 & H120 & H128 & Hscratch136_88 & H224 &
      H232 & H240 & H248 & H256 & H272 & H280 & H1664 & H1672 &
      H1680 & _)".
  iDestruct (mem_mapsto_uninit_split 16 with "Hscratch136_88") as
    "[Hscratch136_16 Hscratch152_72]".
  { lia. }
  have Hscratch152Address :
    (bv_unsigned sp + 136 + 16 = bv_unsigned sp + 152)%Z by lia.
  iEval (rewrite Hscratch152Address) in "Hscratch152_72".
  iDestruct (mem_mapsto_uninit_split 8 with "Hscratch152_72") as
    "[Hscratch152 Hscratch160]".
  { lia. }
  have Hscratch160Address :
    (bv_unsigned sp + 152 + 8 = bv_unsigned sp + 160)%Z by lia.
  iEval (rewrite Hscratch160Address) in "Hscratch160".
  iAssert (writeSuccessTransactionsLoadFacts
    sp base transaction processed bytes)%I as "HfactsRebuilt".
  { rewrite /writeSuccessTransactionsLoadFacts.
    repeat iSplit; try iPureIntro; try assumption; done. }
  iApply ("Hsd" with "[-]").
  rewrite /zesu_sd_spec /rv64_sd_spec.
  iExists
    (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 80),
    sp.
  iFrame "Hsys Hx16 Hx2 Hscratch152".
  iSplit.
  { iPureIntro. exact HspAlign. }
  iSplit.
  { iPureIntro. lia. }
  rewrite instr_pre'_eq.
  iNext. iIntros "Hpost".
  iDestruct "Hpost" as "(HsysPost & Hx16Post & Hx2Post & Hscratch152Post & _)".
  iAssert (writeSuccessTransactionsMachine15050
    sp base transactions processed transaction) with
    "[-Harray Hframe Hnext]"
    as "HmachineFinal".
  { rewrite /writeSuccessTransactionsMachine15050
      /writeSuccessTransactionsMachine15048WithX16AndScratch
      /writeSuccessTransactionsScratch15050.
    iFrame "HsysPost Hother Hx21 Hx2Post Hx5 Hx6 Hx7 Hx8 Hx9 Hx10 Hx11
      Hx12 Hx13 Hx14 Hx15 Hx16Post Hx17 Hx18 Hx19 Hx20 Hx23 Hx24 Hx25
      Hx26 Hx27 Hx28 Hx29 Hx30 Hx31 Hlower H104 H112 H120 H128
      Hscratch136_16 Hscratch152Post Hscratch160 H224 H232 H240 H248
      H256 H272 H280 H1664 H1672 H1680". }
  iAssert (writeSuccessTransactionsLoadFacts
    sp base transaction processed bytes)%I as "HfactsFinal".
  { rewrite /writeSuccessTransactionsLoadFacts.
    repeat iSplit; try iPureIntro; try assumption; done. }
  iApply "Hnext".
  rewrite /writeSuccessTransactionsAt15050Spec.
  iExists sp, base, transaction, transactions, processed, remaining,
    bytes, prefix, suffix, tail.
  iFrame "HmachineFinal Harray Hframe HfactsFinal".
Qed.

Lemma write_success_transactions_chunk_1504c
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr 0x1504c (Some IslaTraces.write_success_32.a1504c.a1504c) -∗
  instr_body 0x15050 (writeSuccessTransactionsAt15050Spec P) -∗
  instr_body 0x1504c (writeSuccessTransactionsAt1504cSpec P).
Proof.
  iIntros "#Hinstr Hnext".
  iPoseProof
    (IslaTraces.write_success_32.a1504c_spec.a1504c_spec 0x1504c with
      "Hinstr") as "Hsd".
  rewrite instr_pre'_eq. iIntros "Hentry".
  rewrite /writeSuccessTransactionsAt1504cSpec.
  iDestruct "Hentry" as
    (sp base transaction transactions processed remaining
      bytes prefix suffix tail)
    "(Hmachine & Harray & Hframe & Hfacts & _)".
  iPoseProof "Hfacts" as "#HfactsCopy".
  iDestruct "HfactsCopy" as
    "(%Hlength & %HcurrentAlign & %HcurrentLower & %HcurrentUpper &
      %HspAlign & %HspLower & %HspUpper & _)".
  iPoseProof (write_success_transactions_chunk_1504c_block P sp base
    transaction transactions processed remaining bytes prefix suffix tail)
    as "Hbody".
  iEval (rewrite instr_pre'_eq) in "Hbody".
  iSpecialize ("Hbody" with "Hsd Hnext").
  iApply "Hbody".
  rewrite /writeSuccessTransactionsAt1504cBlock.
  iFrame.
  iPureIntro.
  repeat split; try assumption.
  apply write_success_15048_current_unsigned; lia.
Qed.

Lemma write_success_transactions_chunk_15048_load_block
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
  instr_body 0x15048
    (zesu_ld_byte_array_at_spec 0x15048 "x16" "x10" 80 0 80) -∗
  instr_body 0x1504c (writeSuccessTransactionsAt1504cSpec P) -∗
  instr_body 0x15048 (writeSuccessTransactionsAt15048Block P sp base
    transaction transactions processed remaining bytes prefix suffix tail).
Proof.
  move => *.
  iStartProof.
  iIntros "Hnext".
  liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: rewrite ?write_success_15048_current_unsigned; try lia.
  all: iExists
    (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction,
      tt)ₗ.
  all: try prepare_sidecond.
  all: try assumption.
  all: rewrite ?write_success_15048_current_unsigned; try lia.
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
  iIntros "Hprefix80 Hsuffix88".
  cbn.
  have Hstart :
    Z.to_nat
      (bv_unsigned (Z_to_bv 64
        (base + 288 * Z.of_nat (length processed))) + 80 -
       (base + 288 * Z.of_nat (length processed))) = 80%nat.
  { rewrite H7. lia. }
  iEval (rewrite Hstart) in "Hprefix80 Hsuffix88".
  rewrite Hstart H7 !Z.add_0_r.
  iFrame "Hprefix80 Hsuffix88".
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
    ((_ ↦ₘ∗ take 80
      (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
        transaction))%I) into "HprefixFinal".
  iRename select
    ((_ ↦ₘ Z_to_bv 64
      (little_endian_to_bv 8
        (take 8 (drop 80
          (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
            transaction)))))%I) into "HwordFinal".
  iRename select
    ((_ ↦ₘ∗ drop 88
      (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
        transaction))%I) into "HsuffixFinal".
  iPoseProof (mem_mapsto_array_recombine_u64_read
    (base + 288 * Z.of_nat (length processed))
    (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction)
    80 _ _ with
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
  iAssert (writeSuccessTransactionsMachine1504c sp base transactions
    processed transaction) with "[-HarrayFinal HframeFinal]"
    as "HmachineFinal".
  { rewrite /writeSuccessTransactionsMachine1504c
      /writeSuccessTransactionsMachine15048WithX16AndScratch.
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

Lemma write_success_transactions_chunk_15048_load
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr 0x15048 (Some IslaTraces.write_success_32.a15048.a15048) -∗
  instr_body 0x1504c (writeSuccessTransactionsAt1504cSpec P) -∗
  instr_body 0x15048 (writeSuccessTransactionsAt15048Spec P).
Proof.
  iIntros "#Hinstr Hnext".
  iPoseProof
    (IslaTraces.write_success_32.a15048_spec.a15048_spec 0x15048 with
      "Hinstr") as "Hld".
  rewrite instr_pre'_eq. iIntros "Hentry".
  rewrite /writeSuccessTransactionsAt15048Spec.
  iDestruct "Hentry" as
    (sp base transaction transactions processed remaining
      bytes prefix suffix tail)
    "(Hmachine & Harray & Hframe & Hfacts & _)".
  iPoseProof "Hfacts" as "#HfactsCopy".
  iDestruct "HfactsCopy" as
    "(%Hlength & %HcurrentAlign & %HcurrentLower & %HcurrentUpper &
      %HspAlign & %HspLower & %HspUpper & _)".
  iPoseProof (write_success_transactions_chunk_15048_load_block P sp base
    transaction transactions processed remaining bytes prefix suffix tail)
    as "Hbody".
  iEval (rewrite instr_pre'_eq) in "Hbody".
  iSpecialize ("Hbody" with "Hld Hnext").
  iApply "Hbody".
  rewrite /writeSuccessTransactionsAt15048Block.
  iFrame.
  iPureIntro.
  repeat split; try assumption.
  apply write_success_15048_current_unsigned; lia.
Qed.

Lemma write_success_transactions_chunk_15048
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x1505c (writeSuccessTransactionsAt1505cSpec P) -∗
  instr_body 0x15048 (writeSuccessTransactionsAt15048Spec P).
Proof.
  iIntros "#Hlookup _ Hnext".
  iPoseProof "Hlookup" as "#Hlookup48".
  iEval (rewrite /instr_lookup_resources) in "Hlookup48".
  iPoseProof ("Hlookup48" $! 0x15058) as "Hinstr58".
  iSpecialize ("Hinstr58" with "[]").
  { iPureIntro. rewrite Index.lookup_a15058. done. }
  iEval (rewrite Index.lookup_a15058) in "Hinstr58".
  iPoseProof (write_success_transactions_chunk_15058_load P with
    "Hinstr58 Hnext") as "H58".
  iPoseProof ("Hlookup48" $! 0x15054) as "Hinstr54".
  iSpecialize ("Hinstr54" with "[]").
  { iPureIntro. rewrite Index.lookup_a15054. done. }
  iEval (rewrite Index.lookup_a15054) in "Hinstr54".
  iPoseProof (write_success_transactions_chunk_15054 P with
    "Hinstr54 H58") as "H54".
  iPoseProof ("Hlookup48" $! 0x15050) as "Hinstr50".
  iSpecialize ("Hinstr50" with "[]").
  { iPureIntro. rewrite Index.lookup_a15050. done. }
  iEval (rewrite Index.lookup_a15050) in "Hinstr50".
  iPoseProof (write_success_transactions_chunk_15050_load P with
    "Hinstr50 H54") as "H50".
  iPoseProof ("Hlookup48" $! 0x1504c) as "Hinstr4c".
  iSpecialize ("Hinstr4c" with "[]").
  { iPureIntro. rewrite Index.lookup_a1504c. done. }
  iEval (rewrite Index.lookup_a1504c) in "Hinstr4c".
  iPoseProof (write_success_transactions_chunk_1504c P with
    "Hinstr4c H50") as "H4c".
  iPoseProof ("Hlookup48" $! 0x15048) as "Hinstr48".
  iSpecialize ("Hinstr48" with "[]").
  { iPureIntro. rewrite Index.lookup_a15048. done. }
  iEval (rewrite Index.lookup_a15048) in "Hinstr48".
  iApply (write_success_transactions_chunk_15048_load P with
    "Hinstr48 H4c").
Qed.
