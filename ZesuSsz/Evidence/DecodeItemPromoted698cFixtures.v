Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.BlockTable.
Require Import ZesuSsz.Generated.DecodeItem.BlockTable.
Require Import ZesuSsz.Generated.DecodeItem.PromotedBodies.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d698c.

Lemma decodeItemPromoted698cExactSignature `{!islaG Sigma} `{!threadG} :
  ⊢ block_table_pre decodeItemBlockTable -∗
    instr_body 0x800d698c decodeItemState800d698c.
Proof. exact decodeItemPromotedBody800d698c. Qed.

Print Assumptions decodeItemSlotBody800d698c.
Print Assumptions decodeItemPromotedBody800d698c.
Print Assumptions decodeItemPromoted698cExactSignature.
