Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCallAbi.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeBooleanCallRet.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeBooleanReturn.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.

Definition writeSuccessTransactionsPriorityFeeBooleanAbiTail
    `{!islaG Sigma} `{!threadG} (sp : bv 64)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (remaining : list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (tail : spec) : iProp Sigma :=
  (⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜bv_extract 0 1 (BV 64 0x15148) = BV 1 0⌝ ∗
   ⌜bv_extract 1 1 (BV 64 0x15148) = BV 1 0⌝ ∗
   ⌜bv_extract 0 2 (BV 64 0x15148) = BV 2 0⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 16 /\
     bv_unsigned sp < (machineRamEnd defaultMap)⌝ ∗
   (bv_unsigned sp - 16) ↦ₘ? 16 ∗
   (∃ callTail : spec,
     mmio_range (machineOutputAddress defaultMap) 16 ∗
     spec_trace (writeOutputEventsAny (sp - BV 64 9)%bv (BV 64 1) callTail) ∗
     instr_pre 0x15148
       (zesu_c_call_ret 16
         (writeSuccessTransactionsPriorityFeeSavedValues transaction)
         (BV 64 0x15148) sp
         (fun _ => mmio_range (machineOutputAddress defaultMap) 16 ∗ spec_trace callTail ∗ True))))%I.

Global Typeclasses Opaque writeSuccessTransactionsPriorityFeeBooleanAbiTail.

Lemma write_success_transactions_priority_fee_boolean_abi_tail
    `{!islaG Sigma} `{!threadG}
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (remaining : list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (sp : bv 64) (tail : spec)
    (Halign : bv_unsigned sp `mod` 16 = 0)
    (Hlower : (mapRamBase defaultMap) <= bv_unsigned sp - 16)
    (Hupper : bv_unsigned sp < (machineRamEnd defaultMap)) :
  (bv_unsigned sp - 16) ↦ₘ? 16 -∗
  mmio_range (machineOutputAddress defaultMap) 16 -∗
  spec_trace
    (writeOutputEventsAny (sp - BV 64 9)%bv (BV 64 1)
      (writeSuccessTransactionPhaseEvents TransactionGasLimit sp transaction
        (writeSuccessTransactionsEvents sp remaining tail))) -∗
  instr_pre 0x15148
    (writeSuccessTransactionsPriorityFeeBooleanCallRet
      sp transaction remaining tail) -∗
  writeSuccessTransactionsPriorityFeeBooleanAbiTail
    sp transaction remaining tail.
Proof.
  iStartProof. iIntros "Hstack Hmmio Htrace Hret".
  rewrite /writeSuccessTransactionsPriorityFeeBooleanAbiTail.
  iFrame "Hstack Hmmio Htrace".
  iEval (unfold writeSuccessTransactionsPriorityFeeBooleanCallRet,
    writeSuccessTransactionsPriorityFeeBooleanMmio,
    writeSuccessTransactionsPriorityFeeBooleanTrace) in "Hret".
  iFrame "Hret".
  repeat iSplit; try iPureIntro; try assumption; try native_compute;
    try bv_solve; try lia; try done.
Qed.
