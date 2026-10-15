Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemCompositional.

Lemma decodeItemRegisterExitWeakens `{!islaG Sigma} `{!threadG}
    args after :
  decodeItemExitResourcesRegisters args after ⊢ decodeItemExitResources args after.
Proof.
  rewrite /decodeItemExitResourcesRegisters.
  iIntros "[Hbase _]". iExact "Hbase".
Qed.

Lemma decodeItemCompositionalExitWeakens `{!islaG Sigma} `{!threadG}
    args after :
  decodeItemExitResourcesCompositional args after ⊢
  decodeItemExitResources (decodeItemCompositionalBase args) after.
Proof.
  rewrite /decodeItemExitResourcesCompositional /decodeItemExitResourcesRegisters.
  iIntros "[[Hbase _] _]". iExact "Hbase".
Qed.

Lemma decodeItemCompositionalEntryProjects `{!islaG Sigma} `{!threadG}
    domain args :
  decodeItemEntryResourcesCompositional domain args ⊢
  decodeItemEntryResources domain (decodeItemCompositionalBase args).
Proof.
  rewrite /decodeItemEntryResourcesCompositional.
  iIntros "[Hbase _]". iExact "Hbase".
Qed.
