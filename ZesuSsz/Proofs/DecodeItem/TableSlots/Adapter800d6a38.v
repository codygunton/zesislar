Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.BlockTable.
Require Import ZesuSsz.Generated.DecodeItem.BlockTable.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6a38Conditional.
Require Import ZesuSsz.Proofs.DecodeItem.Hand.Block800d6a38.

Lemma decodeItemSlotBody800d6a38 `{!islaG Sigma} `{!threadG} :
  ⊢ block_table_pre decodeItemBlockTable -∗
    instr_body 0x800d6a38 decodeItemState800d6a38.
Proof.
  apply decodeItemSlotBody800d6a38Conditional.
  intros args n payloadStart lengthBytes frameBytes loaded inputPrefix rest.
  exact (DesignedBoundary_800d6a38 args n payloadStart lengthBytes frameBytes loaded inputPrefix rest).
Qed.
Print Assumptions decodeItemSlotBody800d6a38.
