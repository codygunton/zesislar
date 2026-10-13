Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.BlockTable.
Require Import ZesuSsz.Generated.DecodeItem.BlockTable.
Require Import ZesuSsz.Generated.DecodeItem.PromotedBodies.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6a78.

Lemma decodeItemPromoted6a78ExactSignature `{!islaG Sigma} `{!threadG} :
  ⊢ block_table_pre decodeItemBlockTable -∗
    instr_body 0x800d6a78 decodeItemState800d6a78.
Proof. exact decodeItemPromotedBody800d6a78. Qed.

Print Assumptions decodeItemSlotBody800d6a78.
Print Assumptions decodeItemPromotedBody800d6a78.
Print Assumptions decodeItemPromoted6a78ExactSignature.
