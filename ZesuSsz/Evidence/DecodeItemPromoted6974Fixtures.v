Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.BlockTable.
Require Import ZesuSsz.Generated.DecodeItem.BlockTable.
Require Import ZesuSsz.Generated.DecodeItem.PromotedBodies.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6974.

Lemma decodeItemPromoted6974ExactSignature `{!islaG Sigma} `{!threadG} :
  ⊢ block_table_pre decodeItemBlockTable -∗
    instr_body 0x800d6974 decodeItemState800d6974.
Proof. exact decodeItemPromotedBody800d6974. Qed.

Print Assumptions decodeItemSlotBody800d6974.
Print Assumptions decodeItemPromotedBody800d6974.
Print Assumptions decodeItemPromoted6974ExactSignature.
