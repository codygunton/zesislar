Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.BlockTable.
Require Import ZesuSsz.Generated.DecodeItem.BlockTable.
Require Import ZesuSsz.Generated.DecodeItem.PromotedBodies.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d697c.

Lemma decodeItemPromoted697cExactSignature `{!islaG Sigma} `{!threadG} :
  ⊢ block_table_pre decodeItemBlockTable -∗
    instr_body 0x800d697c decodeItemState800d697c.
Proof. exact decodeItemPromotedBody800d697c. Qed.

Print Assumptions decodeItemSlotBody800d697c.
Print Assumptions decodeItemPromotedBody800d697c.
Print Assumptions decodeItemPromoted697cExactSignature.
