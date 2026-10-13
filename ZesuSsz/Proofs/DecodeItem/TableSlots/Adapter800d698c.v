Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.BlockTable.
Require Import ZesuSsz.Generated.DecodeItem.BlockTable.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d698cConditional.
Require Import ZesuSsz.Proofs.DecodeItem.Hand.Block800d698c.

Lemma decodeItemSlotBody800d698c `{!islaG Sigma} `{!threadG} :
  ⊢ block_table_pre decodeItemBlockTable -∗
    instr_body 0x800d698c decodeItemState800d698c.
Proof.
  apply decodeItemSlotBody800d698cConditional.
  intros args locals pointerBytes lengthBytes inputPrefix rest isLiteral.
  exact (DesignedBoundary_800d698c args locals pointerBytes lengthBytes inputPrefix rest isLiteral).
Qed.
Print Assumptions decodeItemSlotBody800d698c.
