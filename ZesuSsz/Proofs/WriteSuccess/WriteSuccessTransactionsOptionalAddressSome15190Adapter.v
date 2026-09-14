Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCallAbi.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsOptionalAddressSome15190Boundary.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.

Lemma write_success_transactions_optional_address_some_15190_return_adapter
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
  zesu_c_call_ret 0
    [RVal_Bits (writeSuccessTransactionWord transaction 192);
     RVal_Bits (writeSuccessTransactionWord transaction 16);
     RVal_Bits (writeSuccessTransactionWord transaction 48);
     RVal_Bits (writeSuccessTransactionWord transaction 224);
     RVal_Bits (writeSuccessTransactionWord transaction 56);
     RVal_Bits (writeSuccessTransactionWord transaction 72);
     RVal_Bits (writeSuccessTransactionWord transaction 200);
     RVal_Bits (writeSuccessTransactionWord transaction 24);
     RVal_Bits (writeSuccessTransactionWord transaction 8);
     RVal_Bits (writeSuccessTransactionWord transaction 0);
     RVal_Bits (writeSuccessTransactionWord transaction 184);
     RVal_Bits (bv_zero_extend 64 (writeSuccessTransactionByte transaction 32))]
    (BV 64 0x15190) sp
    (fun _ => mmio_range (machineOutputAddress defaultMap) 16 ∗
      spec_trace (writeSuccessTransactionPhaseEvents TransactionValue sp transaction
        (writeSuccessTransactionsEvents sp remaining tail)) ∗ True) -∗
  writeSuccessTransactionsOptionalAddressSome15190Frame P sp base transaction
    transactions processed remaining bytes prefix suffix tail -∗
  writeSuccessTransactionsOptionalAddressSomeAt15190Spec P.
Proof.
  iIntros "Hpost Hframe".
  iExists sp, base, transaction, transactions, processed, remaining, bytes,
    prefix, suffix, tail.
  iEval (unfold zesu_c_call_ret) in "Hpost".
  iEval (unfold zesu_c_call_ret).
  iDestruct "Hpost" as "(Hsys & Hcaller & Hsaved & Hrest)".
  iEval (rewrite !reg_mapsto_pred_eq /reg_mapsto_pred_def) in "Hrest".
  iDestruct "Hrest" as (r10) "(H10 & Hrest)".
  iDestruct "Hrest" as (b10) "(%Hr10 & Hrest)". subst r10.
  iDestruct "Hrest" as (r11) "(H11 & Hrest)".
  iDestruct "Hrest" as (b11) "(%Hr11 & H2 & Hstack & Hmmio & Htrace & _)".
  subst r11.
  iEval (rewrite !reg_mapsto_pred_eq /reg_mapsto_pred_def).
  iFrame "Hsys Hcaller Hsaved H10 H11 H2 Hstack".
  iExists b10. iSplit; first done.
  iExists b11. iSplit; first done.
  iFrame "Hmmio Htrace Hframe".
Qed.
