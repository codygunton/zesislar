Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.BlockTable.
Require Import ZesuSsz.Generated.DecodeItem.BlockTable.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6a40Conditional.
Require Import ZesuSsz.Proofs.DecodeItem.Auto.Block800d6a40.

Lemma decodeItemSlotBody800d6a40 `{!islaG Sigma} `{!threadG} :
  ⊢ block_table_pre decodeItemBlockTable -∗
    instr_body 0x800d6a40 decodeItemState800d6a40.
Proof.
  apply decodeItemSlotBody800d6a40Conditional.
  intros args locals inputPrefix rest headerLength payloadLength.
  exact (DesignedBoundary_800d6a40 args locals inputPrefix rest headerLength payloadLength).
Qed.
Print Assumptions decodeItemSlotBody800d6a40.
