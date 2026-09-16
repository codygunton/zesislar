Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith.

Lemma access_empty_branch_impossible `{!islaG Sigma} `{!threadG}
    sp base entries processed bytes storedIndex x19 savedX22 data x22 x27 tail (P : iProp Sigma) :
  (writeSuccessExactAccessListsState sp base entries processed [] bytes storedIndex
     x19 savedX22 data x22 x27 tail P ∗
   ⌜Z_to_bv 64 (Z.of_nat (length processed)) <> Z_to_bv 64 (Z.of_nat (length entries))⌝ ∗ True)%I -∗
  False.
Proof.
  iIntros "(Hstate & %Hne & _)".
  iDestruct "Hstate" as "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & %Hpartition & _)".
  rewrite app_nil_r in Hpartition. rewrite Hpartition in Hne. contradiction.
Qed.
Print Assumptions access_empty_branch_impossible.
