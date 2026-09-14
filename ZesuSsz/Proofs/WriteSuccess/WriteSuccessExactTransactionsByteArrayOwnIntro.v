Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.

Lemma transaction_byte_array_own_intro `{!islaG Sigma} (pointer : bv 64) bytes :
  (bytes <> [] -> (mapRamBase defaultMap) <= bv_unsigned pointer /\
    bv_unsigned pointer + Z.of_nat (length bytes) < (machineRamEnd defaultMap)) ->
  bv_unsigned pointer ↦ₘ∗ bytes -∗ writeSuccessByteArrayOwn pointer bytes.
Proof.
  intros Hbounds. destruct bytes as [|byte bytes].
  - cbn [writeSuccessByteArrayOwn]. iIntros "_". done.
  - destruct (Hbounds ltac:(discriminate)) as [Hlow Hhigh].
    cbn [writeSuccessByteArrayOwn]. iIntros "Hbytes".
    iSplitL "Hbytes"; first iExact "Hbytes".
    repeat iSplit; done.
Qed.
Print Assumptions transaction_byte_array_own_intro.
