Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.BlockTable.
Require Import ZesuSsz.Generated.DecodeItem.BlockTable.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6ad8Conditional.
Require Import ZesuSsz.Proofs.DecodeItem.Hand.Block800d6ad8.

Lemma decodeItemSlotBody800d6ad8 `{!islaG Sigma} `{!threadG} :
  ⊢ block_table_pre decodeItemBlockTable -∗
    instr_body 0x800d6ad8 decodeItemState800d6ad8.
Proof.
  apply decodeItemSlotBody800d6ad8Conditional.
  intros args n payloadStart lengthBytes frameBytes loaded inputPrefix rest.
  exact (DesignedBoundary_800d6ad8 args n payloadStart lengthBytes frameBytes loaded inputPrefix rest).
Qed.
Print Assumptions decodeItemSlotBody800d6ad8.
