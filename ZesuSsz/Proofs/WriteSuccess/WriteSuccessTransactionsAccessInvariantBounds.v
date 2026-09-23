Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.

Lemma write_success_transactions_access_invariant_bounds
    `{!islaG Sigma} (base : Z) (entries : list writeSuccessAccessEntry)
    (bytes : list (bv 8)) (R : iProp Sigma)
    (HbaseLow : (mapRamBase defaultMap) <= base)
    (HbaseHigh : base + Z.of_nat (length bytes) < (machineRamEnd defaultMap)) :
  R -∗
  ⌜entries <> [] -> (mapRamBase defaultMap) <= base⌝ ∗
  ⌜entries <> [] -> base + Z.of_nat (length bytes) < (machineRamEnd defaultMap)⌝ ∗ R.
Proof. move => *. zesu_block. Qed.
