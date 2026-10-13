Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.BlockTable.
Require Import ZesuSsz.Generated.DecodeItem.BlockTable.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6960Conditional.
Require Import ZesuSsz.Proofs.DecodeItem.Hand.Block800d6960.

Lemma decodeItemSlotBody800d6960 `{!islaG Sigma} `{!threadG} :
  ⊢ block_table_pre decodeItemBlockTable -∗
    instr_body 0x800d6960 decodeItemState800d6960.
Proof.
  apply decodeItemSlotBody800d6960Conditional.
  intros returnAddress args.
  exact (DesignedBoundary_800d6960 returnAddress args).
Qed.
Print Assumptions decodeItemSlotBody800d6960.
