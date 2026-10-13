Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.BlockTable.
Require Import ZesuSsz.Generated.DecodeItem.BlockTable.
Require Import ZesuSsz.Generated.DecodeItem.PromotedBodies.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6ae0.

Lemma decodeItemPromoted6ae0ExactSignature `{!islaG Sigma} `{!threadG} :
  ⊢ block_table_pre decodeItemBlockTable -∗
    instr_body 0x800d6ae0 decodeItemState800d6ae0.
Proof. exact decodeItemPromotedBody800d6ae0. Qed.

Print Assumptions decodeItemSlotBody800d6ae0.
Print Assumptions decodeItemPromotedBody800d6ae0.
Print Assumptions decodeItemPromoted6ae0ExactSignature.
