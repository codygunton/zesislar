Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessByteLists.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCallAbi.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrier150f8CallFrame.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierCall150ec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.

Definition writeSuccessTransactions150fcCarrierReturn
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec)
    (first second third fourth : bv 64) (items : list ByteListItem)
    (tagTail : list (bv 8)) : iProp Sigma :=
  zesu_c_call_ret 32 (writeSuccessTransactions150ecSavedValues transaction)
    (BV 64 0x150fc) sp
    (fun _ =>
      writeSuccessTransactions150f8CarrierCallFrame P sp base transaction
        transactions processed remaining bytes prefix suffix tail
        first second third fourth items ∗
      (bv_unsigned sp + 1664) ↦ₘ
        writeSuccessTransactionWord transaction 160 ∗
      (bv_unsigned sp + 1672) ↦ₘ
        writeSuccessTransactionByte transaction 168 ∗
      (bv_unsigned sp + 1673) ↦ₘ∗ tagTail ∗
      ⌜bv_to_little_endian 8 8
          (bv_unsigned (writeSuccessTransactionWord transaction 168)) =
        writeSuccessTransactionByte transaction 168 :: tagTail⌝ ∗
      mmio_range 0x2401a0c0 16 ∗
      spec_trace
        (writeSuccessTransactionPhaseEvents TransactionNonce sp transaction
          (writeSuccessTransactionsEvents sp remaining
            (writeSuccessTransactionsCarrierOutputTail sp items tail))) ∗ True)%I.

Definition writeSuccessTransactionsAt150fcCarrierAbiSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
      (transactions processed remaining : list writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec)
      (first second third fourth : bv 64) (items : list ByteListItem)
      (tagTail : list (bv 8)),
    writeSuccessTransactions150fcCarrierReturn P sp base transaction
      transactions processed remaining bytes prefix suffix tail
      first second third fourth items tagTail)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsAt150fcCarrierAbiSpec) := I.
Global Typeclasses Opaque writeSuccessTransactions150fcCarrierReturn.

Lemma write_success_transactions_150fc_carrier_abi_fixed
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec)
    (first second third fourth : bv 64) (items : list ByteListItem)
    (tagTail : list (bv 8)) :
  instr_body 0x150fc (writeSuccessTransactionsAt150fcCarrierAbiSpec P) -∗
  instr_pre 0x150fc
    (writeSuccessTransactions150fcCarrierReturn P sp base transaction
      transactions processed remaining bytes prefix suffix tail
      first second third fourth items tagTail).
Proof.
  iIntros "Hnext".
  iApply instr_pre_to_body. iNext.
  iApply (instr_pre_wand 0x150fc 0x150fc false false with "Hnext");
    [done | done |].
  iIntros "Hreturn".
  rewrite /writeSuccessTransactionsAt150fcCarrierAbiSpec.
  iExists sp, base, transaction, transactions, processed, remaining,
    bytes, prefix, suffix, tail, first, second, third, fourth, items, tagTail.
  iExact "Hreturn".
Qed.

Lemma write_success_transactions_150fc_carrier_abi_continuation
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec)
    (first second third fourth : bv 64) (items : list ByteListItem)
    (tagTail : list (bv 8)) :
  instr_body 0x150fc (writeSuccessTransactionsAt150fcCarrierAbiSpec P) -∗
  writeSuccessTransactions150f8CarrierCallFrame P sp base transaction
      transactions processed remaining bytes prefix suffix tail
      first second third fourth items -∗
  (bv_unsigned sp + 1673) ↦ₘ∗ tagTail -∗
  ⌜bv_to_little_endian 8 8
      (bv_unsigned (writeSuccessTransactionWord transaction 168)) =
    writeSuccessTransactionByte transaction 168 :: tagTail⌝ -∗
  instr_pre 0x150fc
    (zesu_c_call_ret 32 (writeSuccessTransactions150ecSavedValues transaction)
      (BV 64 0x150fc) sp
      (fun _ =>
        (bv_unsigned sp + 1664) ↦ₘ
          writeSuccessTransactionWord transaction 160 ∗
        (bv_unsigned sp + 1672) ↦ₘ
          writeSuccessTransactionByte transaction 168 ∗
        mmio_range 0x2401a0c0 16 ∗
        spec_trace
          (writeSuccessTransactionPhaseEvents TransactionNonce sp transaction
            (writeSuccessTransactionsEvents sp remaining
              (writeSuccessTransactionsCarrierOutputTail sp items tail))) ∗ True)).
Proof.
  iIntros "Hnext Hframe HtagTail" (Hshape).
  iPoseProof (write_success_transactions_150fc_carrier_abi_fixed P sp base
    transaction transactions processed remaining bytes prefix suffix tail
    first second third fourth items tagTail with "Hnext") as "Hret".
  iApply (instr_pre_wand 0x150fc 0x150fc true true with "Hret");
    [done | done |].
  iIntros "Hpost".
  iEval (unfold zesu_c_call_ret) in "Hpost".
  iDestruct "Hpost" as "(Hsys & Htmp & Hsaved & Hrest)".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "Hrest".
  iDestruct "Hrest" as (r10) "(H10 & Hrest)".
  iDestruct "Hrest" as (b10) "(%Hr10 & Hrest)".
  iDestruct "Hrest" as (r11) "(H11 & Hrest)".
  iDestruct "Hrest" as (b11) "(%Hr11 & H2 & Hstack & HQ)".
  iEval (unfold writeSuccessTransactions150fcCarrierReturn, zesu_c_call_ret).
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def).
  iFrame "Hsys Htmp Hsaved H10 H11 H2 Hstack".
  iExists b10. iSplit; first done.
  iExists b11. iSplit; first done.
  iDestruct "HQ" as "(Hvalue & Htag & Hmmio & Htrace & _)".
  iFrame. done.
Qed.
