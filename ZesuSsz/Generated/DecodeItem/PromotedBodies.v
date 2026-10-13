Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.BlockTable.
Require Import ZesuSsz.Generated.DecodeItem.BlockTable.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6960.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6974.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d697c.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d698c.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d69a4.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d69d8.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d69e0.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d69e8.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6a00.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6a08.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6a14.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6a24.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6a38.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6a64.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6a6c.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6a78.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6aa8.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6ab4.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6ac4.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6ad8.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6ae0.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6b08.

(* Pending slots have no proof term. No composition theorem is generated. *)
Section promoted_block_bodies.
Context `{!islaG Sigma} `{!threadG}.

Definition decodeItemPromotedBody800d6960 :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d6960 decodeItemState800d6960 :=
  ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6960.decodeItemSlotBody800d6960.

Definition decodeItemPromotedBody800d6974 :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d6974 decodeItemState800d6974 :=
  ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6974.decodeItemSlotBody800d6974.

Definition decodeItemPromotedBody800d697c :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d697c decodeItemState800d697c :=
  ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d697c.decodeItemSlotBody800d697c.

Definition decodeItemPromotedBody800d698c :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d698c decodeItemState800d698c :=
  ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d698c.decodeItemSlotBody800d698c.

Definition decodeItemPromotedBody800d69a4 :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d69a4 decodeItemState800d69a4 :=
  ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d69a4.decodeItemSlotBody800d69a4.

Definition decodeItemPromotedBody800d69d8 :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d69d8 decodeItemState800d69d8 :=
  ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d69d8.decodeItemSlotBody800d69d8.

Definition decodeItemPromotedBody800d69e0 :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d69e0 decodeItemState800d69e0 :=
  ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d69e0.decodeItemSlotBody800d69e0.

Definition decodeItemPromotedBody800d69e8 :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d69e8 decodeItemState800d69e8 :=
  ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d69e8.decodeItemSlotBody800d69e8.

Definition decodeItemPromotedBody800d6a00 :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d6a00 decodeItemState800d6a00 :=
  ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6a00.decodeItemSlotBody800d6a00.

Definition decodeItemPromotedBody800d6a08 :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d6a08 decodeItemState800d6a08 :=
  ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6a08.decodeItemSlotBody800d6a08.

Definition decodeItemPromotedBody800d6a14 :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d6a14 decodeItemState800d6a14 :=
  ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6a14.decodeItemSlotBody800d6a14.

Definition decodeItemPromotedBody800d6a24 :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d6a24 decodeItemState800d6a24 :=
  ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6a24.decodeItemSlotBody800d6a24.

Definition decodeItemPromotedBody800d6a38 :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d6a38 decodeItemState800d6a38 :=
  ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6a38.decodeItemSlotBody800d6a38.

Definition decodeItemPromotedBody800d6a64 :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d6a64 decodeItemState800d6a64 :=
  ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6a64.decodeItemSlotBody800d6a64.

Definition decodeItemPromotedBody800d6a6c :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d6a6c decodeItemState800d6a6c :=
  ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6a6c.decodeItemSlotBody800d6a6c.

Definition decodeItemPromotedBody800d6a78 :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d6a78 decodeItemState800d6a78 :=
  ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6a78.decodeItemSlotBody800d6a78.

Definition decodeItemPromotedBody800d6aa8 :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d6aa8 decodeItemState800d6aa8 :=
  ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6aa8.decodeItemSlotBody800d6aa8.

Definition decodeItemPromotedBody800d6ab4 :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d6ab4 decodeItemState800d6ab4 :=
  ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6ab4.decodeItemSlotBody800d6ab4.

Definition decodeItemPromotedBody800d6ac4 :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d6ac4 decodeItemState800d6ac4 :=
  ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6ac4.decodeItemSlotBody800d6ac4.

Definition decodeItemPromotedBody800d6ad8 :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d6ad8 decodeItemState800d6ad8 :=
  ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6ad8.decodeItemSlotBody800d6ad8.

Definition decodeItemPromotedBody800d6ae0 :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d6ae0 decodeItemState800d6ae0 :=
  ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6ae0.decodeItemSlotBody800d6ae0.

Definition decodeItemPromotedBody800d6b08 :
  ⊢ block_table_pre decodeItemBlockTable -∗ instr_body 0x800d6b08 decodeItemState800d6b08 :=
  ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6b08.decodeItemSlotBody800d6b08.

End promoted_block_bodies.

Print Assumptions decodeItemPromotedBody800d6960.
Print Assumptions decodeItemPromotedBody800d6974.
Print Assumptions decodeItemPromotedBody800d697c.
Print Assumptions decodeItemPromotedBody800d698c.
Print Assumptions decodeItemPromotedBody800d69a4.
Print Assumptions decodeItemPromotedBody800d69d8.
Print Assumptions decodeItemPromotedBody800d69e0.
Print Assumptions decodeItemPromotedBody800d69e8.
Print Assumptions decodeItemPromotedBody800d6a00.
Print Assumptions decodeItemPromotedBody800d6a08.
Print Assumptions decodeItemPromotedBody800d6a14.
Print Assumptions decodeItemPromotedBody800d6a24.
Print Assumptions decodeItemPromotedBody800d6a38.
Print Assumptions decodeItemPromotedBody800d6a64.
Print Assumptions decodeItemPromotedBody800d6a6c.
Print Assumptions decodeItemPromotedBody800d6a78.
Print Assumptions decodeItemPromotedBody800d6aa8.
Print Assumptions decodeItemPromotedBody800d6ab4.
Print Assumptions decodeItemPromotedBody800d6ac4.
Print Assumptions decodeItemPromotedBody800d6ad8.
Print Assumptions decodeItemPromotedBody800d6ae0.
Print Assumptions decodeItemPromotedBody800d6b08.
