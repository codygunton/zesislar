Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Specs.
From IslaTraces.write_success_blocks Require Import
  Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary14f1c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary14f3c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary14f40.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.
#[local] Typeclasses Opaque writeSuccessTransactionsCurrentPhaseFrame.

Lemma write_success_14f3c_current_unsigned (current : Z) :
  (0 <= current)%Z ->
  (current < 2 ^ 64)%Z ->
  bv_unsigned (Z_to_bv 64 current) = current.
Proof. intros. bv_solve. Qed.

#[local] Hint Rewrite write_success_14f3c_current_unsigned using lia :
  lithium_rewrite.

Definition writeSuccessTransactionsAt14f3cBlock
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x25" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 0) ∗
   "x24" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 8) ∗
   "x9" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 16) ∗
   "x23" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 24) ∗
   "x11" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 144) ∗
   "x10" ↦ᵣ RVal_Bits
     (Z_to_bv 64 (base + 288 * Z.of_nat (length processed))) ∗
   (base + 288 * Z.of_nat (length processed)) ↦ₘ∗
     WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction ∗
   writeSuccessTransactions14f40Frame
     sp base transactions processed transaction ∗
   writeSuccessTransactionsCurrentPhaseFrame P sp base transaction
     transactions processed remaining bytes prefix suffix tail ∗
   writeSuccessTransactionsLoadFacts sp base transaction processed bytes ∗
   ⌜bv_unsigned
      (Z_to_bv 64 (base + 288 * Z.of_nat (length processed))) =
     (base + 288 * Z.of_nat (length processed))%Z⌝ ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsAt14f3cBlock) := I.

Lemma write_success_transactions_chunk_14f3c_block
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x14f40 (writeSuccessTransactionsAt14f40Spec P) -∗
  instr_body 0x14f3c (writeSuccessTransactionsAt14f3cBlock P sp base
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
  all: rewrite ?write_success_14f3c_current_unsigned; try lia.
  all: try (iExists
    (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction,
      WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 152,
      tt)ₗ).
  all: try prepare_sidecond.
  all: try assumption.
  all: rewrite ?write_success_14f3c_current_unsigned; try lia.
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
  iIntros "Hprefix152 Hsuffix160".
  cbn.
  have Hstart :
    Z.to_nat
      (bv_unsigned (Z_to_bv 64
        (base + 288 * Z.of_nat (length processed))) + 152 -
       (base + 288 * Z.of_nat (length processed))) = 152%nat.
  { rewrite H7. lia. }
  iEval (rewrite Hstart) in "Hprefix152 Hsuffix160".
  rewrite Hstart H7 !Z.add_0_r.
  iFrame "Hprefix152 Hsuffix160".
  repeat iSplit; try iPureIntro; try lia; try done.
  liARun.
  iExists (tail, suffix, prefix, bytes, remaining, transactions, sp, tt)ₗ.
  iFrame.
  repeat iSplit; try (iPureIntro; assumption).
  all: try done.
  Unshelve. all: try prepare_sidecond.
  all: try assumption.
  all: try solve_zesu_ld_array_at.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  all: try done.
Qed.

Lemma write_success_transactions_chunk_14f3c
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x14f40 (writeSuccessTransactionsAt14f40Spec P) -∗
  instr_body 0x14f3c (writeSuccessTransactionsAt14f3cSpec P).
Proof.
  iIntros "#Hlookup #Hcode Hnext".
  rewrite instr_pre'_eq. iIntros "Hentry".
  rewrite /writeSuccessTransactionsAt14f3cSpec.
  iDestruct "Hentry" as
    (sp base transaction transactions processed remaining
      bytes prefix suffix tail)
    "(Hsys & Hx25 & Hx24 & Hx9 & Hx23 & Hx11 & Hx10 & Hprefix144 &
      Hword144 & Hsuffix152 & Hmachine & Hframe & Hfacts & _)".
  iPoseProof "Hfacts" as "#HfactsCopy".
  iDestruct "HfactsCopy" as
    "(%Hlength & %HcurrentAlign & %HcurrentLower & %HcurrentUpper &
      %HspAlign & %HspLower & %HspUpper & _)".
  iEval (unfold writeSuccessTransactions14f3cFrame) in "Hmachine".
  iDestruct "Hmachine" as
    "(Hstack0 & Hstack1 & Hstack2 & Hstack3 & HstackWord144 &
      HstackWord136 & Hstack4 & Hstack5 & Hx2 & Hother & _)".
  iAssert (writeSuccessTransactions14f40Frame
      sp base transactions processed transaction)
    with "[Hstack0 Hstack1 Hstack2 Hstack3 HstackWord144 HstackWord136 Hstack4 Hstack5
      Hx2 Hother]" as "Hmachine".
  { rewrite /writeSuccessTransactions14f40Frame. iFrame. }
  iPoseProof (mem_mapsto_array_recombine_u64_read
    (base + 288 * Z.of_nat (length processed))
    (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction)
    144
    (base + 288 * Z.of_nat (length processed) + 152)
    (base + 288 * Z.of_nat (length processed) + 144) with
    "Hprefix144 Hsuffix152 Hword144 [] [] []") as "Harray".
  { iPureIntro. lia. }
  { iPureIntro. cbn. lia. }
  { iPureIntro. rewrite Hlength. lia. }
  iEval (rewrite -instr_pre'_eq) in "Hnext".
  iPoseProof (write_success_transactions_chunk_14f3c_block P sp base
    transaction transactions processed remaining bytes prefix suffix tail with
    "Hlookup Hcode Hnext") as "Hbody".
  iEval (rewrite instr_pre'_eq) in "Hbody".
  iApply "Hbody".
  rewrite /writeSuccessTransactionsAt14f3cBlock.
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: rewrite ?write_success_14f3c_current_unsigned; try lia.
  all: try iFrame.
  all: try done.
Qed.
