Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.BlockTable.
Require Import ZesuSsz.Generated.DecodeItem.BlockTable.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6974.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d69a4.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d69d8.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d69e0.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6a00.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6a14.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6a64.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6a6c.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6ab4.

(* Pending slots have no proof term. No composition theorem is generated. *)
Section promoted_block_bodies.
Context `{!islaG Sigma} `{!threadG}.

Definition decodeItemPromotedBody800d6974 :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d6974 decodeItemState800d6974 :=
  ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6974.decodeItemSlotBody800d6974.

Definition decodeItemPromotedBody800d69a4 :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d69a4 decodeItemState800d69a4 :=
  ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d69a4.decodeItemSlotBody800d69a4.

Definition decodeItemPromotedBody800d69d8 :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d69d8 decodeItemState800d69d8 :=
  ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d69d8.decodeItemSlotBody800d69d8.

Definition decodeItemPromotedBody800d69e0 :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d69e0 decodeItemState800d69e0 :=
  ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d69e0.decodeItemSlotBody800d69e0.

Definition decodeItemPromotedBody800d6a00 :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d6a00 decodeItemState800d6a00 :=
  ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6a00.decodeItemSlotBody800d6a00.

Definition decodeItemPromotedBody800d6a14 :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d6a14 decodeItemState800d6a14 :=
  ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6a14.decodeItemSlotBody800d6a14.

Definition decodeItemPromotedBody800d6a64 :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d6a64 decodeItemState800d6a64 :=
  ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6a64.decodeItemSlotBody800d6a64.

Definition decodeItemPromotedBody800d6a6c :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d6a6c decodeItemState800d6a6c :=
  ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6a6c.decodeItemSlotBody800d6a6c.

Definition decodeItemPromotedBody800d6ab4 :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d6ab4 decodeItemState800d6ab4 :=
  ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6ab4.decodeItemSlotBody800d6ab4.

End promoted_block_bodies.

Print Assumptions decodeItemPromotedBody800d6974.
Print Assumptions decodeItemPromotedBody800d69a4.
Print Assumptions decodeItemPromotedBody800d69d8.
Print Assumptions decodeItemPromotedBody800d69e0.
Print Assumptions decodeItemPromotedBody800d6a00.
Print Assumptions decodeItemPromotedBody800d6a14.
Print Assumptions decodeItemPromotedBody800d6a64.
Print Assumptions decodeItemPromotedBody800d6a6c.
Print Assumptions decodeItemPromotedBody800d6ab4.
