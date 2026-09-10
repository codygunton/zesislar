From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCallAbi.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsOptionalAddressSome15190Adapter.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsOptionalAddressSome15190Boundary.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.

Lemma write_success_transactions_optional_address_some_1518c_call_continuation
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
  instr_body 0x15190 (writeSuccessTransactionsOptionalAddressSomeAt15190Spec P) -∗
  writeSuccessTransactionsOptionalAddressSome15190Frame P sp base transaction
    transactions processed remaining bytes prefix suffix tail -∗
  instr_pre 0x15190
    (zesu_c_call_ret 0
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
      (fun _ => mmio_range 0x2401a0c0 16 ∗
        spec_trace (writeSuccessTransactionPhaseEvents TransactionValue sp transaction
          (writeSuccessTransactionsEvents sp remaining tail)) ∗ True)).
Proof.
  iIntros "Hnext Hframe".
  iPoseProof (instr_pre_wand 0x15190 0x15190 false true with "Hnext")
    as "HretPre"; [done | reflexivity |].
  iSpecialize ("HretPre" with "[Hframe]").
  { iIntros "Hpost".
    iApply (write_success_transactions_optional_address_some_15190_return_adapter
      P sp base transaction transactions processed remaining bytes prefix suffix tail
      with "Hpost Hframe"). }
  iExact "HretPre".
Qed.
