Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.BlockTable.
Require Import ZesuSsz.Generated.DecodeItem.BlockTable.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6aa8Conditional.
Require Import ZesuSsz.Proofs.DecodeItem.Hand.Block800d6aa8.

Lemma decodeItemSlotBody800d6aa8 `{!islaG Sigma} `{!threadG} :
  ⊢ block_table_pre decodeItemBlockTable -∗
    instr_body 0x800d6aa8 decodeItemState800d6aa8.
Proof.
  apply decodeItemSlotBody800d6aa8Conditional.
  intros args frameBytes x13 inputPrefix rest.
  exact (DesignedBoundary_800d6aa8 args frameBytes x13 inputPrefix rest).
Qed.
Print Assumptions decodeItemSlotBody800d6aa8.
