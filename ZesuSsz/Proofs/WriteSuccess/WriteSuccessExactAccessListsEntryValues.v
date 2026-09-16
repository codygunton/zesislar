Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsGasLoads.
Require Import isla.riscv64.riscv64.
From Coq Require Import ZArith.ZArith.

Lemma access_entry_count_value entry :
  writeSuccessAccessEntryValid entry ->
  bv_unsigned (transactionRowWord (writeSuccessAccessEntryBytes entry) 0 8) =
    Z.of_nat (writeSuccessAccessEntryStorageCount entry).
Proof.
  intros Hvalid. destruct Hvalid as [Hlength [Hpointer [Hword [Hsize Hbound]]]].
  apply Nat2Z.inj_lt in Hbound. rewrite Nat2Z.inj_pow in Hbound.
  change (Z.of_nat (writeSuccessAccessEntryStorageCount entry) < 18446744073709551616)%Z in Hbound.
  change (bv_unsigned (writeSuccessAccessEntryWord entry 8) =
    Z.of_nat (writeSuccessAccessEntryStorageCount entry)).
  rewrite Hword Z_to_bv_small; [reflexivity|unfold bv_modulus; cbn; lia].
Qed.
Print Assumptions access_entry_count_value.

Lemma access_entry_pointer_value entry :
  writeSuccessAccessEntryValid entry ->
  transactionRowWord (writeSuccessAccessEntryBytes entry) 0 0 = writeSuccessAccessEntryStoragePointer entry.
Proof.
  intros Hvalid. change (writeSuccessAccessEntryWord entry 0 = writeSuccessAccessEntryStoragePointer entry).
  exact (proj1 (proj2 Hvalid)).
Qed.
Print Assumptions access_entry_pointer_value.
