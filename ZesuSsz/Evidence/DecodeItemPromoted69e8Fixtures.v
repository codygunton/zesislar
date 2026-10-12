Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.BlockTable.
Require Import ZesuSsz.Generated.DecodeItem.BlockTable.
Require Import ZesuSsz.Generated.DecodeItem.PromotedBodies.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d69e8.

Lemma decodeItemPromoted69e8ExactSignature `{!islaG Sigma} `{!threadG} :
  ⊢ block_table_pre decodeItemBlockTable -∗
    instr_body 0x800d69e8 decodeItemState800d69e8.
Proof. exact decodeItemPromotedBody800d69e8. Qed.

Print Assumptions decodeItemSlotBody800d69e8.
Print Assumptions decodeItemPromotedBody800d69e8.
Print Assumptions decodeItemPromoted69e8ExactSignature.
