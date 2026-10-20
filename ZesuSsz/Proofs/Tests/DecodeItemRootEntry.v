Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Compliance.DecodeItemUnfoldRegistrations.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.DecodeItemCompositional.
Require Import ZesuSsz.Compliance.DecodeItemCompositionalWeakening.
Require Import ZesuSsz.Compliance.DecodeItemCompositionalCompliance.
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

Lemma decodeItemRootInternalCallerContinuation `{!islaG Sigma} `{!threadG}
    returnAddress args :
  decodeItemBranchContinuationAt args returnAddress =
    (instr_pre returnAddress
      (∃ outcome : DecodeItemOutcome,
        decodeItemExitResourcesRegisters args outcome ∗
        ⌜decodeItemDomainAt returnAddress decodeItemC1BDomain args /\
          DecodeMeaningModuloKnownBugs args outcome⌝))%I.
Proof. reflexivity. Qed.
Print Assumptions decodeItemRootInternalCallerContinuation.

Lemma decodeItemRootCallerContinuation `{!islaG Sigma} `{!threadG}
    returnAddress args :
  (instr_pre returnAddress
    (∃ outcome : DecodeItemOutcome,
      ⌜decodeItemDomainAt returnAddress decodeItemC1BDomain args /\
        DecodeMeaningModuloKnownBugs args outcome⌝ ∗
      decodeItemExitResources args outcome))%I ⊢
  decodeItemBranchContinuationAt args returnAddress.
Proof.
  unfold decodeItemBranchContinuationAt.
  rewrite decodeItemInstrPreExistOrder.
  iIntros "Hpublic".
  iApply (instr_pre_wand with "Hpublic []"); [done|done|].
  iIntros "Hafter". iDestruct "Hafter" as (outcome) "[%Hallowed Hexit]".
  iExists outcome. iFrame "%".
  iApply (decodeItemRegisterExitWeakens with "Hexit").
Qed.
Print Assumptions decodeItemRootCallerContinuation.

Lemma decodeItemRootTableResources `{!islaG Sigma} `{!threadG} :
  decodeItemState800d6960 =
    (∃ (returnAddress : Z) (args : DecodeItemArgs),
      decodeItemEntryResources
        (decodeItemDomainAt returnAddress decodeItemC1BDomain) args ∗
      decodeItemBranchContinuationAt args returnAddress)%I.
Proof. reflexivity. Qed.
Print Assumptions decodeItemRootTableResources.
