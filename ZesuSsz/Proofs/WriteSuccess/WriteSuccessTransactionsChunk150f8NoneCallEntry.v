Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCallAbi.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk150f0Spec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary150fc.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk150f8ScratchRest.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk150f8RawReturn.

Import ListNotations.

Lemma write_success_transactions_chunk_150f8_none_call_entry
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec)
    (tagTail : list (bv 8)) :
  instr_pre'_def false 0x150fc (writeSuccessTransactionsAt150fcFramedSpec P) -∗
  ⌜bv_to_little_endian 8 8
      (bv_unsigned
        (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 168)) =
      BV 8 0 :: tagTail⌝ -∗
  reg_col [(KindReg "x3", BitsShape 64); (KindReg "x4", BitsShape 64)] -∗
  instr_pre (bv_unsigned (BV 64 0x150fc))
    (zesu_c_call_ret 32
      [RVal_Bits (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 192);
       RVal_Bits (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 16);
       RVal_Bits (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 48);
       RVal_Bits (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 224);
       RVal_Bits (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 56);
       RVal_Bits (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 72);
       RVal_Bits (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 200);
       RVal_Bits (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 24);
       RVal_Bits (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 8);
       RVal_Bits (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 0);
       RVal_Bits (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 184);
       RVal_Bits (bv_zero_extend 64
         (WriteSuccessTransactionsSpec.writeSuccessTransactionByte transaction 32))]
      (BV 64 0x150fc) sp
      (fun _ =>
        writeSuccessTransactions150f0Frame P sp base transaction transactions
          processed remaining bytes prefix suffix tail ∗
        writeSuccessTransactionsScratchRest150f8 sp base transactions processed transaction ∗
        (bv_unsigned sp + 1664) ↦ₘ
          (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 160) ∗
        (bv_unsigned sp + 1672) ↦ₘ BV 8 0 ∗
        (bv_unsigned sp + 1673) ↦ₘ∗ tagTail ∗
        mmio_range (machineOutputAddress defaultMap) 16 ∗
        spec_trace
          (WriteSuccessTransactionsSpec.writeSuccessTransactionPhaseEvents
            WriteSuccessTransactionsSpec.TransactionNonce sp transaction
            (WriteSuccessTransactionsSpec.writeSuccessTransactionsEvents
              sp remaining tail)) ∗ True)).
Proof.
  iStartProof. iIntros "Hnext" (Hshape) "Hcaller34".
  iEval (rewrite <- instr_pre'_eq) in "Hnext".
  iApply (instr_pre_wand 0x150fc 0x150fc false true with "Hnext");
    [done | reflexivity |].
  iIntros "Hpost".
  iPoseProof (write_success_transactions_150fc_raw_return_adapter P
    sp base transaction transactions processed remaining bytes prefix suffix
    tail tagTail) as "Hraw".
  iSpecialize ("Hraw" with "Hpost").
  iSpecialize ("Hraw" with "[]").
  { iPureIntro. exact Hshape. }
  iSpecialize ("Hraw" with "Hcaller34").
  iExact "Hraw".
Qed.
