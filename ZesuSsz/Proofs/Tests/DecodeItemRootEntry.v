Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Generated.DecodeItem.BlockTable.

Lemma decodeItemRootEntryResources `{!islaG Sigma} `{!threadG}
    returnAddress args :
  decodeItemEntryAt800d6960 returnAddress args =
    (decodeItemEntryResources
       (decodeItemDomainAt returnAddress decodeItemC1BDomain) args ∗
     decodeItemBranchContinuationAt args returnAddress)%I.
Proof. reflexivity. Qed.
Print Assumptions decodeItemRootEntryResources.

Lemma decodeItemRootEntryContinuation `{!islaG Sigma} `{!threadG}
    returnAddress args :
  ⊢ (decodeItemEntryAt800d6960 returnAddress args -∗
     decodeItemBranchContinuationAt args returnAddress)%I.
Proof.
  unfold decodeItemEntryAt800d6960.
  iIntros "[_ Hcontinuation]". iExact "Hcontinuation".
Qed.
Print Assumptions decodeItemRootEntryContinuation.

Lemma decodeItemRootCallerContinuation `{!islaG Sigma} `{!threadG}
    returnAddress args :
  decodeItemBranchContinuationAt args returnAddress =
    (instr_pre returnAddress
      (∃ outcome : DecodeItemOutcome,
        ⌜decodeItemDomainAt returnAddress decodeItemC1BDomain args /\
          DecodeMeaningModuloKnownBugs args outcome⌝ ∗
        decodeItemExitResources args outcome))%I.
Proof. reflexivity. Qed.
Print Assumptions decodeItemRootCallerContinuation.

Lemma decodeItemRootTableResources `{!islaG Sigma} `{!threadG} :
  decodeItemState800d6960 =
    (∃ (returnAddress : Z) (args : DecodeItemArgs),
      decodeItemEntryResources
        (decodeItemDomainAt returnAddress decodeItemC1BDomain) args ∗
      decodeItemBranchContinuationAt args returnAddress)%I.
Proof. reflexivity. Qed.
Print Assumptions decodeItemRootTableResources.
