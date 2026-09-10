From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Specs.
From IslaTraces.write_success_blocks Require Import
  Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary14f1c.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary14fc8.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary1501c.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary15028.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.
#[local] Typeclasses Opaque writeSuccessTransactionsCurrentPhaseFrame.

Lemma write_success_1501c_current_unsigned (current : Z) :
  (0 <= current)%Z ->
  (current < 2 ^ 64)%Z ->
  bv_unsigned (Z_to_bv 64 current) = current.
Proof. intros. bv_solve. Qed.

Definition writeSuccessTransactionsAt15020Spec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z)
      (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
      (transactions processed remaining :
        list WriteSuccessTransactionsSpec.writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    "x10" ↦ᵣ RVal_Bits
      (Z_to_bv 64 (base + 288 * Z.of_nat (length processed))) ∗
    "x18" ↦ᵣ RVal_Bits
      (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
        transaction 48) ∗
    "x20" ↦ᵣ: (fun value =>
      ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    "x29" ↦ᵣ: (fun value =>
      ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    (reg_col zesu_ram_sys_regs ∗
     "x10" ↦ᵣ RVal_Bits
       (Z_to_bv 64 (base + 288 * Z.of_nat (length processed))) ∗
     "x18" ↦ᵣ RVal_Bits
       (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
         transaction 48) ∗
     "x20" ↦ᵣ RVal_Bits
       (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
         transaction 56) ∗
     "x29" ↦ᵣ RVal_Bits
       (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
         transaction 64) -∗
     writeSuccessTransactionsMachine15028
       sp base transactions processed transaction) ∗
    (base + 288 * Z.of_nat (length processed)) ↦ₘ∗
      WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction ∗
    writeSuccessTransactionsCurrentPhaseFrame P sp base transaction
      transactions processed remaining bytes prefix suffix tail ∗
    writeSuccessTransactionsLoadFacts
      sp base transaction processed bytes ∗ True)%I.

Definition writeSuccessTransactionsAt15024Spec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z)
      (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
      (transactions processed remaining :
        list WriteSuccessTransactionsSpec.writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    "x10" ↦ᵣ RVal_Bits
      (Z_to_bv 64 (base + 288 * Z.of_nat (length processed))) ∗
    "x18" ↦ᵣ RVal_Bits
      (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
        transaction 48) ∗
    "x20" ↦ᵣ RVal_Bits
      (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
        transaction 56) ∗
    "x29" ↦ᵣ: (fun value =>
      ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    (reg_col zesu_ram_sys_regs ∗
     "x10" ↦ᵣ RVal_Bits
       (Z_to_bv 64 (base + 288 * Z.of_nat (length processed))) ∗
     "x18" ↦ᵣ RVal_Bits
       (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
         transaction 48) ∗
     "x20" ↦ᵣ RVal_Bits
       (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
         transaction 56) ∗
     "x29" ↦ᵣ RVal_Bits
       (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
         transaction 64) -∗
     writeSuccessTransactionsMachine15028
       sp base transactions processed transaction) ∗
    (base + 288 * Z.of_nat (length processed)) ↦ₘ∗
      WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction ∗
    writeSuccessTransactionsCurrentPhaseFrame P sp base transaction
      transactions processed remaining bytes prefix suffix tail ∗
    writeSuccessTransactionsLoadFacts
      sp base transaction processed bytes ∗ True)%I.

Definition writeSuccessTransactionsAt1501cBlock
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x10" ↦ᵣ RVal_Bits
     (Z_to_bv 64 (base + 288 * Z.of_nat (length processed))) ∗
   "x18" ↦ᵣ: (fun value =>
     ⌜valu_has_shape value (BitsShape 64)⌝) ∗
   "x20" ↦ᵣ: (fun value =>
     ⌜valu_has_shape value (BitsShape 64)⌝) ∗
   "x29" ↦ᵣ: (fun value =>
     ⌜valu_has_shape value (BitsShape 64)⌝) ∗
   (reg_col zesu_ram_sys_regs ∗
    "x10" ↦ᵣ RVal_Bits
      (Z_to_bv 64 (base + 288 * Z.of_nat (length processed))) ∗
    "x18" ↦ᵣ RVal_Bits
      (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
        transaction 48) ∗
    "x20" ↦ᵣ RVal_Bits
      (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
        transaction 56) ∗
    "x29" ↦ᵣ RVal_Bits
      (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
        transaction 64) -∗
    writeSuccessTransactionsMachine15028
      sp base transactions processed transaction) ∗
   (base + 288 * Z.of_nat (length processed)) ↦ₘ∗
     WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction ∗
   writeSuccessTransactionsCurrentPhaseFrame P sp base transaction
     transactions processed remaining bytes prefix suffix tail ∗
   writeSuccessTransactionsLoadFacts
     sp base transaction processed bytes ∗
   ⌜bv_unsigned
      (Z_to_bv 64 (base + 288 * Z.of_nat (length processed))) =
     (base + 288 * Z.of_nat (length processed))%Z⌝ ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsAt1501cBlock) := I.

Definition writeSuccessTransactionsAt15020Block
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x10" ↦ᵣ RVal_Bits
     (Z_to_bv 64 (base + 288 * Z.of_nat (length processed))) ∗
   "x18" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
       transaction 48) ∗
   "x20" ↦ᵣ: (fun value =>
     ⌜valu_has_shape value (BitsShape 64)⌝) ∗
   "x29" ↦ᵣ: (fun value =>
     ⌜valu_has_shape value (BitsShape 64)⌝) ∗
   (reg_col zesu_ram_sys_regs ∗
    "x10" ↦ᵣ RVal_Bits
      (Z_to_bv 64 (base + 288 * Z.of_nat (length processed))) ∗
    "x18" ↦ᵣ RVal_Bits
      (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
        transaction 48) ∗
    "x20" ↦ᵣ RVal_Bits
      (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
        transaction 56) ∗
    "x29" ↦ᵣ RVal_Bits
      (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
        transaction 64) -∗
    writeSuccessTransactionsMachine15028
      sp base transactions processed transaction) ∗
   (base + 288 * Z.of_nat (length processed)) ↦ₘ∗
     WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction ∗
   writeSuccessTransactionsCurrentPhaseFrame P sp base transaction
     transactions processed remaining bytes prefix suffix tail ∗
   writeSuccessTransactionsLoadFacts
     sp base transaction processed bytes ∗
   ⌜bv_unsigned
      (Z_to_bv 64 (base + 288 * Z.of_nat (length processed))) =
     (base + 288 * Z.of_nat (length processed))%Z⌝ ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsAt15020Block) := I.

Definition writeSuccessTransactionsAt15024Block
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x10" ↦ᵣ RVal_Bits
     (Z_to_bv 64 (base + 288 * Z.of_nat (length processed))) ∗
   "x18" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
       transaction 48) ∗
   "x20" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
       transaction 56) ∗
   "x29" ↦ᵣ: (fun value =>
     ⌜valu_has_shape value (BitsShape 64)⌝) ∗
   (reg_col zesu_ram_sys_regs ∗
    "x10" ↦ᵣ RVal_Bits
      (Z_to_bv 64 (base + 288 * Z.of_nat (length processed))) ∗
    "x18" ↦ᵣ RVal_Bits
      (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
        transaction 48) ∗
    "x20" ↦ᵣ RVal_Bits
      (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
        transaction 56) ∗
    "x29" ↦ᵣ RVal_Bits
      (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
        transaction 64) -∗
    writeSuccessTransactionsMachine15028
      sp base transactions processed transaction) ∗
   (base + 288 * Z.of_nat (length processed)) ↦ₘ∗
     WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction ∗
   writeSuccessTransactionsCurrentPhaseFrame P sp base transaction
     transactions processed remaining bytes prefix suffix tail ∗
   writeSuccessTransactionsLoadFacts
     sp base transaction processed bytes ∗
   ⌜bv_unsigned
      (Z_to_bv 64 (base + 288 * Z.of_nat (length processed))) =
     (base + 288 * Z.of_nat (length processed))%Z⌝ ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsAt15024Block) := I.

Lemma write_success_transactions_chunk_1501c_block
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x15020 (writeSuccessTransactionsAt15020Spec P) -∗
  instr_body 0x1501c (writeSuccessTransactionsAt1501cBlock P sp base
    transaction transactions processed remaining bytes prefix suffix tail).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode Hnext".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: rewrite ?write_success_1501c_current_unsigned; try lia.
  all: iExists
    (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction,
      tt)ₗ.
  all: try prepare_sidecond.
  all: try assumption.
  all: rewrite ?write_success_1501c_current_unsigned; try lia.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try solve_zesu_ld_array_at.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve. all: try exact inhabitant.
  Unshelve. all: repeat iIntros "?"; liARun.
  Unshelve.
  iExists
    (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction,
      tt)ₗ.
  iIntros "Hprefix48 Hsuffix56".
  cbn.
  have Hstart48 :
      Z.to_nat
        (bv_unsigned (Z_to_bv 64
          (base + 288 * Z.of_nat (length processed))) + 48 -
         (base + 288 * Z.of_nat (length processed))) = 48%nat.
  { rewrite H7. lia. }
  iEval (rewrite Hstart48) in "Hprefix48 Hsuffix56".
  rewrite Hstart48 H7 !Z.add_0_r.
  iFrame "Hprefix48 Hsuffix56".
  repeat iSplit; try iPureIntro; try lia; try done.
  liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve. all: try exact inhabitant.
  all: try (rewrite H7; rewrite length_drop; rewrite H0; lia).
  iRename select
    ((_ ↦ₘ∗ take 48
      (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
        transaction))%I) into "HprefixFinal".
  iRename select
    ((_ ↦ₘ Z_to_bv 64
      (little_endian_to_bv 8
        (take 8 (drop 48
          (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
            transaction)))))%I) into "HwordFinal".
  iRename select
    ((_ ↦ₘ∗ drop 56
      (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
        transaction))%I) into "HsuffixFinal".
  iPoseProof (mem_mapsto_array_recombine_u64_read
    (base + 288 * Z.of_nat (length processed))
    (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction)
    48 _ _ with
    "HprefixFinal HsuffixFinal HwordFinal [] [] []") as "HarrayFinal".
  { iPureIntro. cbn. lia. }
  { iPureIntro. cbn. lia. }
  { iPureIntro. rewrite H0. lia. }
  iRename select
    (writeSuccessTransactionsCurrentPhaseFrame P sp base transaction
      transactions processed remaining bytes prefix suffix tail)%I
    into "HframeFinal".
  iRename select ("x20" ↦ᵣ RVal_Bits _)%I into "Hx20Exact".
  iRename select ("x29" ↦ᵣ RVal_Bits _)%I into "Hx29Exact".
  iAssert ("x20" ↦ᵣ: fun value =>
    ⌜valu_has_shape value (BitsShape 64)⌝)%I
    with "[Hx20Exact]" as "Hx20Shape".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists _. iSplit; first iExact "Hx20Exact".
    iPureIntro. done. }
  iAssert ("x29" ↦ᵣ: fun value =>
    ⌜valu_has_shape value (BitsShape 64)⌝)%I
    with "[Hx29Exact]" as "Hx29Shape".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists _. iSplit; first iExact "Hx29Exact".
    iPureIntro. done. }
  rewrite /writeSuccessTransactionsAt15020Spec.
  iExists sp, base, transaction, transactions, processed, remaining,
    bytes, prefix, suffix, tail.
  cbn.
  iFrame "Hx20Shape Hx29Shape HframeFinal HarrayFinal".
  rewrite /reg_col.
  cbn. iFrame.
  rewrite /writeSuccessTransactionsLoadFacts.
  repeat iSplit; try iPureIntro; try assumption; try done.
Qed.

Lemma write_success_transactions_chunk_15024_block
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x15028 (writeSuccessTransactionsAt15028Spec P) -∗
  instr_body 0x15024 (writeSuccessTransactionsAt15024Block P sp base
    transaction transactions processed remaining bytes prefix suffix tail).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode Hnext".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: rewrite ?write_success_1501c_current_unsigned; try lia.
  all: iExists
    (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction,
      tt)ₗ.
  all: try prepare_sidecond.
  all: try assumption.
  all: rewrite ?write_success_1501c_current_unsigned; try lia.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try solve_zesu_ld_array_at.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve. all: try exact inhabitant.
  Unshelve. all: repeat iIntros "?"; liARun.
  Unshelve.
  iExists
    (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction,
      tt)ₗ.
  iIntros "Hprefix64 Hsuffix72".
  cbn.
  have Hstart64 :
      Z.to_nat
        (bv_unsigned (Z_to_bv 64
          (base + 288 * Z.of_nat (length processed))) + 64 -
         (base + 288 * Z.of_nat (length processed))) = 64%nat.
  { rewrite H7. lia. }
  iEval (rewrite Hstart64) in "Hprefix64 Hsuffix72".
  rewrite Hstart64 H7 !Z.add_0_r.
  iFrame "Hprefix64 Hsuffix72".
  repeat iSplit; try iPureIntro; try lia; try done.
  liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve. all: try exact inhabitant.
  iRename select
    ((_ ↦ₘ∗ take 64
      (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
        transaction))%I) into "HprefixFinal".
  iRename select
    ((_ ↦ₘ Z_to_bv 64
      (little_endian_to_bv 8
        (take 8 (drop 64
          (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
            transaction)))))%I) into "HwordFinal".
  iRename select
    ((_ ↦ₘ∗ drop 72
      (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
        transaction))%I) into "HsuffixFinal".
  iPoseProof (mem_mapsto_array_recombine_u64_read
    (base + 288 * Z.of_nat (length processed))
    (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction)
    64 _ _ with
    "HprefixFinal HsuffixFinal HwordFinal [] [] []") as "HarrayFinal".
  { iPureIntro. cbn. lia. }
  { iPureIntro. cbn. lia. }
  { iPureIntro. rewrite H0. lia. }
  iRename select
    (writeSuccessTransactionsCurrentPhaseFrame P sp base transaction
      transactions processed remaining bytes prefix suffix tail)%I
    into "HframeFinal".
  iExists (tail, suffix, prefix, bytes, remaining, processed,
    transactions, transaction, base, sp, tt)ₗ.
  cbn.
  iRename select
    ((_ -∗ writeSuccessTransactionsMachine15028
      sp base transactions processed transaction)%I) into "HmachineWand".
  iAssert (writeSuccessTransactionsMachine15028
    sp base transactions processed transaction)%I
    with "[-HarrayFinal HframeFinal]" as "HmachineFinal".
  { iApply "HmachineWand".
    rewrite /reg_col.
    cbn. iFrame.
    repeat iSplit; try iPureIntro; try done. }
  iFrame "HmachineFinal HframeFinal HarrayFinal".
  rewrite /writeSuccessTransactionsLoadFacts.
  repeat iSplit; try iPureIntro; try assumption; try done.
Qed.

Lemma write_success_transactions_chunk_15020_block
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x15024 (writeSuccessTransactionsAt15024Spec P) -∗
  instr_body 0x15020 (writeSuccessTransactionsAt15020Block P sp base
    transaction transactions processed remaining bytes prefix suffix tail).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode Hnext".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: rewrite ?write_success_1501c_current_unsigned; try lia.
  all: iExists
    (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction,
      tt)ₗ.
  all: try prepare_sidecond.
  all: try assumption.
  all: rewrite ?write_success_1501c_current_unsigned; try lia.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try solve_zesu_ld_array_at.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve. all: try exact inhabitant.
  Unshelve. all: repeat iIntros "?"; liARun.
  Unshelve.
  iExists
    (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction,
      tt)ₗ.
  iIntros "Hprefix56 Hsuffix64".
  cbn.
  have Hstart56 :
      Z.to_nat
        (bv_unsigned (Z_to_bv 64
          (base + 288 * Z.of_nat (length processed))) + 56 -
         (base + 288 * Z.of_nat (length processed))) = 56%nat.
  { rewrite H7. lia. }
  iEval (rewrite Hstart56) in "Hprefix56 Hsuffix64".
  rewrite Hstart56 H7 !Z.add_0_r.
  iFrame "Hprefix56 Hsuffix64".
  repeat iSplit; try iPureIntro; try lia; try done.
  liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve. all: try exact inhabitant.
  iRename select
    ((_ ↦ₘ∗ take 56
      (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
        transaction))%I) into "HprefixFinal".
  iRename select
    ((_ ↦ₘ Z_to_bv 64
      (little_endian_to_bv 8
        (take 8 (drop 56
          (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
            transaction)))))%I) into "HwordFinal".
  iRename select
    ((_ ↦ₘ∗ drop 64
      (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
        transaction))%I) into "HsuffixFinal".
  iPoseProof (mem_mapsto_array_recombine_u64_read
    (base + 288 * Z.of_nat (length processed))
    (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction)
    56 _ _ with
    "HprefixFinal HsuffixFinal HwordFinal [] [] []") as "HarrayFinal".
  { iPureIntro. cbn. lia. }
  { iPureIntro. cbn. lia. }
  { iPureIntro. rewrite H0. lia. }
  iRename select
    (writeSuccessTransactionsCurrentPhaseFrame P sp base transaction
      transactions processed remaining bytes prefix suffix tail)%I
    into "HframeFinal".
  iRename select ("x29" ↦ᵣ RVal_Bits _)%I into "Hx29Exact".
  iAssert ("x29" ↦ᵣ: fun value =>
    ⌜valu_has_shape value (BitsShape 64)⌝)%I
    with "[Hx29Exact]" as "Hx29Shape".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists _. iSplit; first iExact "Hx29Exact".
    iPureIntro. done. }
  rewrite /writeSuccessTransactionsAt15024Spec.
  iExists sp, base, transaction, transactions, processed, remaining,
    bytes, prefix, suffix, tail.
  cbn.
  iFrame "Hx29Shape HframeFinal HarrayFinal".
  rewrite /reg_col.
  cbn. iFrame.
  rewrite /writeSuccessTransactionsLoadFacts.
  repeat iSplit; try iPureIntro; try assumption; try done.
Qed.

Lemma write_success_transactions_chunk_15024
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x15028 (writeSuccessTransactionsAt15028Spec P) -∗
  instr_body 0x15024 (writeSuccessTransactionsAt15024Spec P).
Proof.
  iIntros "#Hlookup #Hcode Hnext".
  rewrite instr_pre'_eq. iIntros "Hentry".
  rewrite /writeSuccessTransactionsAt15024Spec.
  iDestruct "Hentry" as
    (sp base transaction transactions processed remaining
      bytes prefix suffix tail)
    "(Hsys & Hx10 & Hx18 & Hx20 & Hx29 & HmachineWand &
      Harray & Hframe & Hfacts & _)".
  iPoseProof "Hfacts" as "#HfactsCopy".
  iDestruct "HfactsCopy" as
    "(%Hlength & %HcurrentAlign & %HcurrentLower & %HcurrentUpper &
      %HspAlign & %HspLower & %HspUpper & _)".
  iAssert (writeSuccessTransactionsLoadFacts
    sp base transaction processed bytes)%I as "HfactsRebuilt".
  { rewrite /writeSuccessTransactionsLoadFacts.
    repeat iSplit; try iPureIntro; try assumption; done. }
  iPoseProof
    (write_success_transactions_chunk_15024_block P sp base transaction
      transactions processed remaining bytes prefix suffix tail)
    as "Hbody".
  iEval (rewrite instr_pre'_eq) in "Hbody".
  iSpecialize ("Hbody" with "Hlookup Hcode Hnext").
  iApply "Hbody".
  rewrite /writeSuccessTransactionsAt15024Block.
  iFrame "Hsys Hx10 Hx18 Hx20 Hx29 HmachineWand Harray Hframe HfactsRebuilt".
  iPureIntro.
  split.
  { apply write_success_1501c_current_unsigned; lia. }
  done.
Qed.

Lemma write_success_transactions_chunk_15020
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x15024 (writeSuccessTransactionsAt15024Spec P) -∗
  instr_body 0x15020 (writeSuccessTransactionsAt15020Spec P).
Proof.
  iIntros "#Hlookup #Hcode Hnext".
  rewrite instr_pre'_eq. iIntros "Hentry".
  rewrite /writeSuccessTransactionsAt15020Spec.
  iDestruct "Hentry" as
    (sp base transaction transactions processed remaining
      bytes prefix suffix tail)
    "(Hsys & Hx10 & Hx18 & Hx20 & Hx29 & HmachineWand &
      Harray & Hframe & Hfacts & _)".
  iPoseProof "Hfacts" as "#HfactsCopy".
  iDestruct "HfactsCopy" as
    "(%Hlength & %HcurrentAlign & %HcurrentLower & %HcurrentUpper &
      %HspAlign & %HspLower & %HspUpper & _)".
  iAssert (writeSuccessTransactionsLoadFacts
    sp base transaction processed bytes)%I as "HfactsRebuilt".
  { rewrite /writeSuccessTransactionsLoadFacts.
    repeat iSplit; try iPureIntro; try assumption; done. }
  iPoseProof
    (write_success_transactions_chunk_15020_block P sp base transaction
      transactions processed remaining bytes prefix suffix tail)
    as "Hbody".
  iEval (rewrite instr_pre'_eq) in "Hbody".
  iSpecialize ("Hbody" with "Hlookup Hcode Hnext").
  iApply "Hbody".
  rewrite /writeSuccessTransactionsAt15020Block.
  iFrame "Hsys Hx10 Hx18 Hx20 Hx29 HmachineWand Harray Hframe HfactsRebuilt".
  iPureIntro.
  split.
  { apply write_success_1501c_current_unsigned; lia. }
  done.
Qed.

Lemma write_success_transactions_chunk_1501c
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x15028 (writeSuccessTransactionsAt15028Spec P) -∗
  instr_body 0x1501c (writeSuccessTransactionsAt1501cSpec P).
Proof.
  iIntros "#Hlookup #Hcode Hnext".
  rewrite instr_pre'_eq. iIntros "Hentry".
  rewrite /writeSuccessTransactionsAt1501cSpec.
  iDestruct "Hentry" as
    (sp base transaction transactions processed remaining
      bytes prefix suffix tail)
    "(Hsys & Hx10 & Hx18 & Hx20 & Hx29 & HmachineWand &
      Harray & Hframe & Hfacts & _)".
  iPoseProof "Hfacts" as "#HfactsCopy".
  iDestruct "HfactsCopy" as
    "(%Hlength & %HcurrentAlign & %HcurrentLower & %HcurrentUpper &
      %HspAlign & %HspLower & %HspUpper & _)".
  iAssert (writeSuccessTransactionsLoadFacts
    sp base transaction processed bytes)%I as "HfactsRebuilt".
  { rewrite /writeSuccessTransactionsLoadFacts.
    repeat iSplit; try iPureIntro; try assumption; done. }
  iEval (rewrite -instr_pre'_eq) in "Hnext".
  iPoseProof (write_success_transactions_chunk_15024 P)
    as "Hbody15024".
  iSpecialize ("Hbody15024" with "Hlookup Hcode Hnext").
  iPoseProof (write_success_transactions_chunk_15020 P)
    as "Hbody15020".
  iSpecialize ("Hbody15020" with "Hlookup Hcode Hbody15024").
  iPoseProof
    (write_success_transactions_chunk_1501c_block P sp base transaction
      transactions processed remaining bytes prefix suffix tail)
    as "Hbody".
  iSpecialize ("Hbody" with "Hlookup Hcode Hbody15020").
  iEval (rewrite instr_pre'_eq) in "Hbody".
  iApply "Hbody".
  rewrite /writeSuccessTransactionsAt1501cBlock.
  iFrame "Hsys Hx10 Hx18 Hx20 Hx29 HmachineWand Harray Hframe HfactsRebuilt".
  iPureIntro.
  split.
  { apply write_success_1501c_current_unsigned; lia. }
  done.
Qed.
