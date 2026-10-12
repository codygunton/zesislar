Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.BlockTable.
Require Import ZesuSsz.Generated.DecodeItem.BlockTable.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d697cConditional.
Require Import ZesuSsz.Proofs.DecodeItem.Hand.Block800d697c.

Lemma decodeItemSlotBody800d697c `{!islaG Sigma} `{!threadG} :
  ⊢ block_table_pre decodeItemBlockTable -∗
    instr_body 0x800d697c decodeItemState800d697c.
Proof.
  apply decodeItemSlotBody800d697cConditional.
  intros args frameBytes x13 inputPrefix rest.
  exact (DesignedBoundary_800d697c args frameBytes x13 inputPrefix rest).
Qed.
Print Assumptions decodeItemSlotBody800d697c.
