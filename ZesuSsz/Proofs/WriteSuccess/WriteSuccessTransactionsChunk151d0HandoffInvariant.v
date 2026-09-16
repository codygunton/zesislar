Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsAccessEntryInvariant.

Lemma write_success_transactions_151d0_nonempty_invariant
    `{!islaG Sigma} (sp : bv 64) (base : Z)
    (entry : writeSuccessAccessEntry) (entries : list writeSuccessAccessEntry)
    (Hlength : length (writeSuccessAccessEntriesBytes (entry :: entries)) =
      (40 * length (entry :: entries))%nat)
    (Hbound : (length (entry :: entries) < 2 ^ 64)%nat)
    (HspAlign : bv_unsigned sp `mod` 16 = 0)
    (HspLower : (mapRamBase defaultMap) <= bv_unsigned sp - 48)
    (HspUpper : bv_unsigned sp + 1896 < (machineRamEnd defaultMap))
    (HbaseLower : (mapRamBase defaultMap) <= base)
    (HbaseUpper : base +
      Z.of_nat (length (writeSuccessAccessEntriesBytes (entry :: entries))) <
      (machineRamEnd defaultMap)) :
  ⊢ writeSuccessAccessListsInvariant sp base
    (entry :: entries) [] (entry :: entries)
    (writeSuccessAccessEntriesBytes (entry :: entries)) []
    (writeSuccessAccessEntriesBytes (entry :: entries)).
Proof.
  iApply (write_success_transactions_access_entry_invariant
    sp base (entry :: entries)
    (writeSuccessAccessEntriesBytes (entry :: entries)));
    [discriminate | reflexivity | exact Hlength | exact Hbound |
     exact HspAlign | exact HspLower | exact HspUpper |
     exact HbaseLower | exact HbaseUpper].
Qed.
