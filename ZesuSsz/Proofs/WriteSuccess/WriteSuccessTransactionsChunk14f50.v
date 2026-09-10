From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Specs.
From IslaTraces.write_success_blocks Require Import
  Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary14f1c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary14f50.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary14f54.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.
#[local] Typeclasses Opaque writeSuccessTransactionsCurrentPhaseFrame.

Definition writeSuccessTransactionsAt14f50Block
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
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 160) ∗
   "x12" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 168) ∗
   "x13" ↦ᵣ RVal_Bits
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 176) ∗
   "x10" ↦ᵣ RVal_Bits
     (Z_to_bv 64 (base + 288 * Z.of_nat (length processed))) ∗
   (base + 288 * Z.of_nat (length processed)) ↦ₘ∗
     take 176
       (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction) ∗
   (base + 288 * Z.of_nat (length processed) + 176) ↦ₘ
     WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 176 ∗
   (base + 288 * Z.of_nat (length processed) + 184) ↦ₘ∗
     drop 184
       (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction) ∗
   (bv_unsigned sp - 48) ↦ₘ? 152 ∗
   (bv_unsigned sp + 104) ↦ₘ Z_to_bv 64 base ∗
   (bv_unsigned sp + 112) ↦ₘ
     Z_to_bv 64 (Z.of_nat (length transactions)) ∗
   (bv_unsigned sp + 120) ↦ₘ? 104 ∗
   (bv_unsigned sp + 224) ↦ₘ
     WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 152 ∗
   (bv_unsigned sp + 232) ↦ₘ
     WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 144 ∗
   (bv_unsigned sp + 240) ↦ₘ
     WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 136 ∗
   (bv_unsigned sp + 248) ↦ₘ
     Z_to_bv 64 (Z.of_nat (length processed)) ∗
   (bv_unsigned sp + 256) ↦ₘ? 1640 ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   reg_col (delete 7%nat
     (delete 7%nat
       (delete 18%nat
         (delete 7%nat
           (delete 20%nat writeSuccessTransactions14f1cOtherRegShapes))))) ∗
   writeSuccessTransactionsCurrentPhaseFrame P sp base transaction
     transactions processed remaining bytes prefix suffix tail ∗
   writeSuccessTransactionsLoadFacts sp base transaction processed bytes ∗
   True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsAt14f50Block) := I.

Lemma write_success_transactions_chunk_14f50_block
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x14f54 (writeSuccessTransactionsAt14f54Spec P) -∗
  instr_body 0x14f50 (writeSuccessTransactionsAt14f50Block P sp base
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
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve. all: repeat iIntros "?"; liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  all: try done.
  Unshelve.
  iExists (tail, suffix, prefix, bytes, remaining, transactions, sp, tt)ₗ.
  rewrite /writeSuccessTransactions14f54Frame
    /writeSuccessTransactionsLoadFacts.
  iFrame.
  repeat iSplit; try iPureIntro; try assumption; try done.
  replace (bv_unsigned sp + 280)%Z with
    (bv_unsigned sp + 272 + 8)%Z by lia.
  iFrame.
Qed.

Lemma write_success_transactions_chunk_14f50
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x14f54 (writeSuccessTransactionsAt14f54Spec P) -∗
  instr_body 0x14f50 (writeSuccessTransactionsAt14f50Spec P).
Proof.
  iIntros "#Hlookup #Hcode Hnext".
  rewrite instr_pre'_eq. iIntros "Hentry".
  rewrite /writeSuccessTransactionsAt14f50Spec.
  iDestruct "Hentry" as
    (sp base transaction transactions processed remaining
      bytes prefix suffix tail)
    "(Hsys & Hx25 & Hx24 & Hx9 & Hx23 & Hx11 & Hx12 & Hx13 & Hx10 &
      Hprefix176 & Hword176 & Hsuffix184 & Hmachine & Hframe &
      Hfacts & _)".
  iEval (unfold writeSuccessTransactions14f50Frame) in "Hmachine".
  iDestruct "Hmachine" as
    "(Hstack0 & Hstack1 & Hstack2 & Hstack3 & HstackWord152 &
      HstackWord144 & HstackWord136 & Hstack4 & Hstack5 & Hx2 &
      Hother & _)".
  iEval (rewrite -instr_pre'_eq) in "Hnext".
  iPoseProof (write_success_transactions_chunk_14f50_block P sp base
    transaction transactions processed remaining bytes prefix suffix tail with
    "Hlookup Hcode Hnext") as "Hbody".
  iEval (rewrite instr_pre'_eq) in "Hbody".
  iApply "Hbody".
  rewrite /writeSuccessTransactionsAt14f50Block.
  iFrame.
  replace (bv_unsigned sp + 256)%Z with
    (bv_unsigned sp + 248 + 8)%Z by lia.
  iFrame.
Qed.
