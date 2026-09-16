Require Import ZesuSsz.Automation.AllLegacy.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Specs.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary14f1c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15028.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15044.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15048.
Require Import IslaTraces.write_success_32.a15044_spec.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.
#[local] Typeclasses Opaque writeSuccessTransactionsCurrentPhaseFrame.

Lemma write_success_15044_current_unsigned (current : Z) :
  (0 <= current)%Z ->
  (current < 2 ^ 64)%Z ->
  bv_unsigned (Z_to_bv 64 current) = current.
Proof. intros. bv_solve. Qed.

#[local] Hint Rewrite write_success_15044_current_unsigned using lia :
  lithium_rewrite.

Definition writeSuccessTransactionsAt15044Block
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec)
    (x21 : valu) : iProp Sigma :=
  (writeSuccessTransactionsMachine15044WithX21
     sp base transactions processed transaction x21 ∗
   (base + 288 * Z.of_nat (length processed)) ↦ₘ∗
     WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction ∗
   writeSuccessTransactionsCurrentPhaseFrame P sp base transaction
     transactions processed remaining bytes prefix suffix tail ∗
   writeSuccessTransactionsLoadFacts
     sp base transaction processed bytes ∗
   ⌜bv_unsigned
      (Z_to_bv 64 (base + 288 * Z.of_nat (length processed))) =
     (base + 288 * Z.of_nat (length processed))%Z⌝ ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsAt15044Block) := I.

Lemma write_success_transactions_chunk_15044_load_block
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) (x21 : valu) :
  instr_body 0x15044
    (zesu_ld_byte_array_at_spec 0x15044 "x21" "x10" 72 0 72) -∗
  instr_body 0x15048 (writeSuccessTransactionsAt15048Spec P) -∗
  instr_body 0x15044 (writeSuccessTransactionsAt15044Block P sp base
    transaction transactions processed remaining bytes prefix suffix tail x21).
Proof.
  move => *.
  iStartProof.
  iIntros "Hnext".
  liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: rewrite ?write_success_15044_current_unsigned; try lia.
  all: try bv_solve.
  all: iExists
    (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction,
      tt)ₗ.
  all: try prepare_sidecond.
  all: try assumption.
  all: rewrite ?write_success_15044_current_unsigned; try lia.
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
  iIntros "Hprefix72 Hsuffix80".
  cbn.
  have Hstart :
    Z.to_nat
      (bv_unsigned (Z_to_bv 64
        (base + 288 * Z.of_nat (length processed))) + 72 -
       (base + 288 * Z.of_nat (length processed))) = 72%nat.
  { rewrite Z_to_bv_unsigned; rewrite bv_wrap_small; [lia | bv_solve]. }
  iEval (rewrite Hstart) in "Hprefix72 Hsuffix80".
  rewrite ?Hstart ?Z_to_bv_unsigned ?bv_wrap_small ?Z.add_0_r; try bv_solve.
  iFrame "Hprefix72 Hsuffix80".
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
    ((_ ↦ₘ∗ take 72
      (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
        transaction))%I) into "HprefixFinal".
  iRename select (_ ↦ₘ _)%I into "HwordFinal".
  iRename select
    ((_ ↦ₘ∗ drop 80
      (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes
        transaction))%I) into "HsuffixFinal".
  iPoseProof (mem_mapsto_array_recombine_u64_read
    (base + 288 * Z.of_nat (length processed))
    (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction)
    72 _ _ with
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
  iAssert (writeSuccessTransactionsMachine15048 sp base transactions
    processed transaction) with "[-HarrayFinal HframeFinal]"
    as "HmachineFinal".
  { rewrite /writeSuccessTransactionsMachine15048
      /writeSuccessTransactionsMachine15044WithX21
      /writeSuccessTransactionsMachine15044WithRegisterFrame.
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

Lemma write_success_transactions_chunk_15044_load
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr 0x15044 (Some IslaTraces.write_success_32.a15044.a15044) -∗
  instr_body 0x15048 (writeSuccessTransactionsAt15048Spec P) -∗
  instr_body 0x15044 (writeSuccessTransactionsAt15044Spec P).
Proof.
  iIntros "#Hinstr Hnext".
  iPoseProof
    (IslaTraces.write_success_32.a15044_spec.a15044_spec 0x15044 with
      "Hinstr") as "Hld".
  rewrite instr_pre'_eq. iIntros "Hentry".
  rewrite /writeSuccessTransactionsAt15044Spec.
  iDestruct "Hentry" as
    (sp base transaction transactions processed remaining
      bytes prefix suffix tail)
    "(Hmachine & Harray & Hframe & Hfacts & _)".
  iPoseProof "Hfacts" as "#HfactsCopy".
  iDestruct "HfactsCopy" as
    "(%Hlength & %HcurrentAlign & %HcurrentLower & %HcurrentUpper &
      %HspAlign & %HspLower & %HspUpper & _)".
  rewrite /writeSuccessTransactionsMachine15044
    /writeSuccessTransactionsMachine15044WithRegisterFrame.
  iDestruct "Hmachine" as "(HregisterFrame & HmachineRest)".
  iDestruct "HregisterFrame" as "(Hsys & Hother)".
  iDestruct (reg_col_lookup writeSuccessTransactions15028OtherRegShapes
    3%nat (KindReg "x21", BitsShape 64) with "Hother") as
    (x21 Hx21Shape) "(Hx21 & Hother)".
  { vm_compute. reflexivity. }
  iAssert (writeSuccessTransactionsMachine15044WithX21
      sp base transactions processed transaction x21)
    with "[Hsys Hother Hx21 HmachineRest]" as "Hmachine".
  { rewrite /writeSuccessTransactionsMachine15044WithX21
      /writeSuccessTransactionsMachine15044WithRegisterFrame.
    iFrame. iPureIntro. exact Hx21Shape. }
  iPoseProof (write_success_transactions_chunk_15044_load_block P sp base
    transaction transactions processed remaining bytes prefix suffix tail x21)
    as "Hbody".
  iEval (rewrite instr_pre'_eq) in "Hbody".
  iSpecialize ("Hbody" with "Hld Hnext").
  iApply "Hbody".
  rewrite /writeSuccessTransactionsAt15044Block.
  iFrame.
  iPureIntro.
  repeat split; try assumption.
  apply write_success_15044_current_unsigned; lia.
Qed.
