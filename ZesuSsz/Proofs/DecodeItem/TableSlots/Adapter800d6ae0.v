Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.BlockTable.
Require Import ZesuSsz.Generated.DecodeItem.BlockTable.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6ae0Conditional.
Require Import ZesuSsz.Proofs.DecodeItem.Hand.Block800d6ae0.

Lemma decodeItemSlotBody800d6ae0 `{!islaG Sigma} `{!threadG} :
  ⊢ block_table_pre decodeItemBlockTable -∗
    instr_body 0x800d6ae0 decodeItemState800d6ae0.
Proof.
  apply decodeItemSlotBody800d6ae0Conditional.
  intros args locals.
  exact (DesignedBoundary_800d6ae0 args locals).
Qed.
Print Assumptions decodeItemSlotBody800d6ae0.
