Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.BlockTable.
Require Import ZesuSsz.Generated.DecodeItem.BlockTable.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6a78Conditional.
Require Import ZesuSsz.Proofs.DecodeItem.Auto.Block800d6a78.

Lemma decodeItemSlotBody800d6a78 `{!islaG Sigma} `{!threadG} :
  ⊢ block_table_pre decodeItemBlockTable -∗
    instr_body 0x800d6a78 decodeItemState800d6a78.
Proof.
  apply decodeItemSlotBody800d6a78Conditional.
  intros args locals inputPrefix rest.
  exact (DesignedBoundary_800d6a78 args locals inputPrefix rest).
Qed.
Print Assumptions decodeItemSlotBody800d6a78.
