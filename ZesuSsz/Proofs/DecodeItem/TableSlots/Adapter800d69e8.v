Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.BlockTable.
Require Import ZesuSsz.Generated.DecodeItem.BlockTable.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d69e8Conditional.
Require Import ZesuSsz.Proofs.DecodeItem.Hand.Block800d69e8.

Lemma decodeItemSlotBody800d69e8 `{!islaG Sigma} `{!threadG} :
  ⊢ block_table_pre decodeItemBlockTable -∗
    instr_body 0x800d69e8 decodeItemState800d69e8.
Proof.
  apply decodeItemSlotBody800d69e8Conditional.
  intros args frameBytes x13 inputPrefix rest.
  exact (DesignedBoundary_800d69e8 args frameBytes x13 inputPrefix rest).
Qed.
Print Assumptions decodeItemSlotBody800d69e8.
