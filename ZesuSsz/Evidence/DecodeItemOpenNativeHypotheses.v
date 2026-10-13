Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.BlockTable.
Require Import ZesuSsz.Generated.DecodeItem.BlockTable.
Require Import ZesuSsz.Generated.DecodeItem.PromotedBodies.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
Require Import ZesuSsz.Contracts.RlpDecodeItemFoldEntries.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Proofs.DecodeItem.Composition.CompleteFamily.
From Coq Require Import List ZArith.
Open Scope Z_scope.
Require Import ZesuSsz.Proofs.DecodeItem.Auto.Block800d6974.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d697cConditional.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d698cConditional.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d69b0Conditional.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d69e8Conditional.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6a08Conditional.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6a24Conditional.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6a38Conditional.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6a40Conditional.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6a78Conditional.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6aa8Conditional.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6ac4Conditional.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6ad8Conditional.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6ae0Conditional.
Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6b08Conditional.

Require Import ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6960Conditional.
Require Import ZesuSsz.Proofs.DecodeItem.Composition.CompleteNativeFamily.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Contracts.RlpDecodeItem.

Import ListNotations.

Definition decodeItemOpenNativeClosure6960 : Prop :=
  forall (Sigma : gFunctors) (HG : islaG Sigma) (HT : threadG), forall (returnAddress : Z) (args : DecodeItemArgs),
  instr_pre 0x800d6974 (∃ (successor_frameBytes : list byte) (successor_inputPrefix : byte) (successor_rest : list byte), ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6974 (args) (successor_frameBytes) (successor_inputPrefix) (successor_rest))%I -∗
  instr_pre 0x800d6ae0 (∃ (successor_locals : DecodeItemReturnLocals), ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d6ae0 (args) (successor_locals))%I -∗
  decodeItemSelectedCode -∗
  instr_body 0x800d6960
    (decodeItemEntryAt800d6960 returnAddress args ∗ True).

Definition decodeItemOpenNativeClosure6974 : Prop :=
  forall (Sigma : gFunctors) (HG : islaG Sigma) (HT : threadG), forall (args : DecodeItemArgs) (frameBytes : list byte)
      (inputPrefix : byte) (rest : list byte),
    instr_pre 0x800d697c
      (∃ (successor_frameBytes : list byte) (successor_x13 : bv 64)
         (successor_inputPrefix : byte) (successor_rest : list byte),
        decodeItemEntryAt800d697c args successor_frameBytes successor_x13
          successor_inputPrefix successor_rest) -∗
    instr_pre 0x800d69a4
      (∃ (successor_frameBytes : list byte) (successor_x13 : bv 64)
         (successor_inputPrefix : byte) (successor_rest : list byte),
        decodeItemEntryAt800d69a4 args successor_frameBytes successor_x13
          successor_inputPrefix successor_rest) -∗
    decodeItemSelectedCode -∗ instr_body 0x800d6974
      (decodeItemEntryAt800d6974 args frameBytes inputPrefix rest ∗ True).

Definition decodeItemOpenNativeClosure697c : Prop :=
  forall (Sigma : gFunctors) (HG : islaG Sigma) (HT : threadG), forall (args : DecodeItemArgs) (frameBytes : list byte) (x13 : bv 64) (inputPrefix : byte) (rest : list byte),
  instr_pre 0x800d698c (∃ (successor_locals : DecodeItemReturnLocals) (successor_pointerBytes : list byte) (successor_lengthBytes : list byte) (successor_inputPrefix : byte) (successor_rest : list byte) (successor_isLiteral : bool), ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d698c (args) (successor_locals) (successor_pointerBytes) (successor_lengthBytes) (successor_inputPrefix) (successor_rest) (successor_isLiteral))%I -∗
  decodeItemSelectedCode -∗
  instr_body 0x800d697c
    (decodeItemEntryAt800d697c args frameBytes x13 inputPrefix rest ∗ True).

Definition decodeItemOpenNativeClosure698c : Prop :=
  forall (Sigma : gFunctors) (HG : islaG Sigma) (HT : threadG), forall (args : DecodeItemArgs) (locals : DecodeItemReturnLocals) (pointerBytes : list byte) (lengthBytes : list byte) (inputPrefix : byte) (rest : list byte) (isLiteral : bool),
  decodeItemSelectedCode -∗
  instr_body 0x800d698c
    (decodeItemEntryAt800d698c args locals pointerBytes lengthBytes inputPrefix rest isLiteral ∗ True).

Definition decodeItemOpenNativeClosure69b0 : Prop :=
  forall (Sigma : gFunctors) (HG : islaG Sigma) (HT : threadG), forall (args : DecodeItemArgs) (locals : DecodeItemReturnLocals) (inputPrefix : byte) (rest : list byte),
  decodeItemSelectedCode -∗
  instr_body 0x800d69b0
    (decodeItemEntryAt800d69b0 args locals inputPrefix rest ∗ True).

Definition decodeItemOpenNativeClosure69e8 : Prop :=
  forall (Sigma : gFunctors) (HG : islaG Sigma) (HT : threadG), forall (args : DecodeItemArgs) (frameBytes : list byte) (x13 : bv 64) (inputPrefix : byte) (rest : list byte),
  instr_pre 0x800d698c (∃ (successor_locals : DecodeItemReturnLocals) (successor_pointerBytes : list byte) (successor_lengthBytes : list byte) (successor_inputPrefix : byte) (successor_rest : list byte) (successor_isLiteral : bool), ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d698c (args) (successor_locals) (successor_pointerBytes) (successor_lengthBytes) (successor_inputPrefix) (successor_rest) (successor_isLiteral))%I -∗
  decodeItemSelectedCode -∗
  instr_body 0x800d69e8
    (decodeItemEntryAt800d69e8 args frameBytes x13 inputPrefix rest ∗ True).

Definition decodeItemOpenNativeClosure6a08 : Prop :=
  forall (Sigma : gFunctors) (HG : islaG Sigma) (HT : threadG), forall (args : DecodeItemArgs) (frameBytes : list byte) (x13 : bv 64) (inputPrefix : byte) (rest : list byte),
  instr_pre 0x800d6a14 (∃ (successor_n : Z) (successor_payloadStart : Z) (successor_lengthBytes : list byte) (successor_frameBytes : list byte) (successor_oldAcc : bv 64) (successor_oldCursor : bv 64) (successor_loaded : bv 64) (successor_inputPrefix : byte) (successor_rest : list byte), ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6a14 (args) (successor_n) (successor_payloadStart) (successor_lengthBytes) (successor_frameBytes) (successor_oldAcc) (successor_oldCursor) (successor_loaded) (successor_inputPrefix) (successor_rest))%I -∗
  instr_pre 0x800d6ae0 (∃ (successor_locals : DecodeItemReturnLocals), ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d6ae0 (args) (successor_locals))%I -∗
  decodeItemSelectedCode -∗
  instr_body 0x800d6a08
    (decodeItemEntryAt800d6a08 args frameBytes x13 inputPrefix rest ∗ True).

Definition decodeItemOpenNativeClosure6a24 : Prop :=
  forall (Sigma : gFunctors) (HG : islaG Sigma) (HT : threadG), forall (args : DecodeItemArgs) (inputPrefix : byte) (rest : list byte),
  instr_pre 0x800d6a38 (∃ (successor_n : Z) (successor_payloadStart : Z) (successor_lengthBytes : list byte) (successor_frameBytes : list byte) (successor_loaded : bv 64) (successor_inputPrefix : byte) (successor_rest : list byte), ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6a38 (args) (successor_n) (successor_payloadStart) (successor_lengthBytes) (successor_frameBytes) (successor_loaded) (successor_inputPrefix) (successor_rest))%I -∗
  instr_pre 0x800d6a24 (∃ (successor_inputPrefix : byte) (successor_rest : list byte), ZesuSsz.Contracts.RlpDecodeItemFoldEntries.decodeItemEntryAt800d6a24 (args) (successor_inputPrefix) (successor_rest))%I -∗
  decodeItemSelectedCode -∗
  instr_body 0x800d6a24
    (decodeItemEntryAt800d6a24 args inputPrefix rest ∗ True).

Definition decodeItemOpenNativeClosure6a38 : Prop :=
  forall (Sigma : gFunctors) (HG : islaG Sigma) (HT : threadG), forall (args : DecodeItemArgs) (n : Z) (payloadStart : Z) (lengthBytes : list byte) (frameBytes : list byte) (loaded : bv 64) (inputPrefix : byte) (rest : list byte),
  instr_pre 0x800d6a40 (∃ (successor_locals : DecodeItemReturnLocals) (successor_inputPrefix : byte) (successor_rest : list byte) (successor_headerLength : Z) (successor_payloadLength : Z), ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d6a40 (args) (successor_locals) (successor_inputPrefix) (successor_rest) (successor_headerLength) (successor_payloadLength))%I -∗
  instr_pre 0x800d6ae0 (∃ (successor_locals : DecodeItemReturnLocals), ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d6ae0 (args) (successor_locals))%I -∗
  decodeItemSelectedCode -∗
  instr_body 0x800d6a38
    (decodeItemEntryAt800d6a38 args n payloadStart lengthBytes frameBytes loaded inputPrefix rest ∗ True).

Definition decodeItemOpenNativeClosure6a40 : Prop :=
  forall (Sigma : gFunctors) (HG : islaG Sigma) (HT : threadG), forall (args : DecodeItemArgs) (locals : DecodeItemReturnLocals) (inputPrefix : byte) (rest : list byte) (headerLength : Z) (payloadLength : Z),
  decodeItemSelectedCode -∗
  instr_body 0x800d6a40
    (decodeItemEntryAt800d6a40 args locals inputPrefix rest headerLength payloadLength ∗ True).

Definition decodeItemOpenNativeClosure6a78 : Prop :=
  forall (Sigma : gFunctors) (HG : islaG Sigma) (HT : threadG), forall (args : DecodeItemArgs) (locals : DecodeItemReturnLocals) (inputPrefix : byte) (rest : list byte),
  decodeItemSelectedCode -∗
  instr_body 0x800d6a78
    (decodeItemEntryAt800d6a78 args locals inputPrefix rest ∗ True).

Definition decodeItemOpenNativeClosure6aa8 : Prop :=
  forall (Sigma : gFunctors) (HG : islaG Sigma) (HT : threadG), forall (args : DecodeItemArgs) (frameBytes : list byte) (x13 : bv 64) (inputPrefix : byte) (rest : list byte),
  instr_pre 0x800d6ab4 (∃ (successor_n : Z) (successor_payloadStart : Z) (successor_lengthBytes : list byte) (successor_frameBytes : list byte) (successor_oldAcc : bv 64) (successor_oldCursor : bv 64) (successor_loaded : bv 64) (successor_inputPrefix : byte) (successor_rest : list byte), ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6ab4 (args) (successor_n) (successor_payloadStart) (successor_lengthBytes) (successor_frameBytes) (successor_oldAcc) (successor_oldCursor) (successor_loaded) (successor_inputPrefix) (successor_rest))%I -∗
  instr_pre 0x800d6ae0 (∃ (successor_locals : DecodeItemReturnLocals), ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d6ae0 (args) (successor_locals))%I -∗
  decodeItemSelectedCode -∗
  instr_body 0x800d6aa8
    (decodeItemEntryAt800d6aa8 args frameBytes x13 inputPrefix rest ∗ True).

Definition decodeItemOpenNativeClosure6ac4 : Prop :=
  forall (Sigma : gFunctors) (HG : islaG Sigma) (HT : threadG), forall (args : DecodeItemArgs) (inputPrefix : byte) (rest : list byte),
  instr_pre 0x800d6ad8 (∃ (successor_n : Z) (successor_payloadStart : Z) (successor_lengthBytes : list byte) (successor_frameBytes : list byte) (successor_loaded : bv 64) (successor_inputPrefix : byte) (successor_rest : list byte), ZesuSsz.Contracts.DecodeItemBranchEntries.decodeItemEntryAt800d6ad8 (args) (successor_n) (successor_payloadStart) (successor_lengthBytes) (successor_frameBytes) (successor_loaded) (successor_inputPrefix) (successor_rest))%I -∗
  instr_pre 0x800d6ac4 (∃ (successor_inputPrefix : byte) (successor_rest : list byte), ZesuSsz.Contracts.RlpDecodeItemFoldEntries.decodeItemEntryAt800d6ac4 (args) (successor_inputPrefix) (successor_rest))%I -∗
  decodeItemSelectedCode -∗
  instr_body 0x800d6ac4
    (decodeItemEntryAt800d6ac4 args inputPrefix rest ∗ True).

Definition decodeItemOpenNativeClosure6ad8 : Prop :=
  forall (Sigma : gFunctors) (HG : islaG Sigma) (HT : threadG), forall (args : DecodeItemArgs) (n : Z) (payloadStart : Z) (lengthBytes : list byte) (frameBytes : list byte) (loaded : bv 64) (inputPrefix : byte) (rest : list byte),
  instr_pre 0x800d6ae0 (∃ (successor_locals : DecodeItemReturnLocals), ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d6ae0 (args) (successor_locals))%I -∗
  instr_pre 0x800d6b08 (∃ (successor_locals : DecodeItemReturnLocals) (successor_inputPrefix : byte) (successor_rest : list byte) (successor_headerLength : Z) (successor_payloadLength : Z), ZesuSsz.Contracts.RlpDecodeItemBlockEntries.decodeItemEntryAt800d6b08 (args) (successor_locals) (successor_inputPrefix) (successor_rest) (successor_headerLength) (successor_payloadLength))%I -∗
  decodeItemSelectedCode -∗
  instr_body 0x800d6ad8
    (decodeItemEntryAt800d6ad8 args n payloadStart lengthBytes frameBytes loaded inputPrefix rest ∗ True).

Definition decodeItemOpenNativeClosure6ae0 : Prop :=
  forall (Sigma : gFunctors) (HG : islaG Sigma) (HT : threadG), forall (args : DecodeItemArgs) (locals : DecodeItemReturnLocals),
  decodeItemSelectedCode -∗
  instr_body 0x800d6ae0
    (decodeItemEntryAt800d6ae0 args locals ∗ True).

Definition decodeItemOpenNativeClosure6b08 : Prop :=
  forall (Sigma : gFunctors) (HG : islaG Sigma) (HT : threadG), forall (args : DecodeItemArgs) (locals : DecodeItemReturnLocals) (inputPrefix : byte) (rest : list byte) (headerLength : Z) (payloadLength : Z),
  decodeItemSelectedCode -∗
  instr_body 0x800d6b08
    (decodeItemEntryAt800d6b08 args locals inputPrefix rest headerLength payloadLength ∗ True).

Record DecodeItemOpenNativeHypotheses : Prop := {
  native800d69b0 : decodeItemOpenNativeClosure69b0;
  native800d6a24 : decodeItemOpenNativeClosure6a24;
  native800d6a40 : decodeItemOpenNativeClosure6a40;
  native800d6a78 : decodeItemOpenNativeClosure6a78;
  native800d6aa8 : decodeItemOpenNativeClosure6aa8;
  native800d6ac4 : decodeItemOpenNativeClosure6ac4;
  native800d6ad8 : decodeItemOpenNativeClosure6ad8
}.

Definition decodeItemOpenNativeBlocks : list Z :=
  [0x800d69b0; 0x800d6a24; 0x800d6a40; 0x800d6a78; 0x800d6aa8; 0x800d6ac4; 0x800d6ad8].
Require Import ZesuSsz.Proofs.DecodeItem.Hand.Block800d697c.
Require Import ZesuSsz.Proofs.DecodeItem.Hand.Block800d69e8.
Require Import ZesuSsz.Proofs.DecodeItem.Hand.Block800d6a08.
Require Import ZesuSsz.Proofs.DecodeItem.Hand.Block800d6b08.
Require Import ZesuSsz.Proofs.DecodeItem.Hand.Block800d698c.
Require Import ZesuSsz.Proofs.DecodeItem.Hand.Block800d6a38.
Require Import ZesuSsz.Proofs.DecodeItem.Hand.Block800d6960.
Require Import ZesuSsz.Proofs.DecodeItem.Hand.Block800d6ae0.

Lemma decodeItemOpenNativeBlockCount : length decodeItemOpenNativeBlocks = 7%nat.
Proof. reflexivity. Qed.

Lemma decodeItemOpenNativeHypothesesTable `{!islaG Sigma} `{!threadG}
  (Hopen : DecodeItemOpenNativeHypotheses) :
  □ decodeItemSelectedCode -∗ block_table_pre decodeItemBlockTable.
Proof.
  destruct Hopen as [H69b0 H6a24 H6a40 H6a78 H6aa8 H6ac4 H6ad8].
  exact (@ZesuSsz.Proofs.DecodeItem.Composition.CompleteNativeFamily.decodeItemBlockTable_complete_native_family Sigma islaG0 H
    (@ZesuSsz.Proofs.DecodeItem.TableSlots.Adapter800d6960Conditional.decodeItemSlotBody800d6960Conditional Sigma islaG0 H (@ZesuSsz.Proofs.DecodeItem.Hand.Block800d6960.DesignedBoundary_800d6960 Sigma islaG0 H))
    (@ZesuSsz.Proofs.DecodeItem.Auto.Block800d6974.DesignedBoundary_800d6974 Sigma islaG0 H)
    (@ZesuSsz.Proofs.DecodeItem.Hand.Block800d697c.DesignedBoundary_800d697c Sigma islaG0 H)
    (@ZesuSsz.Proofs.DecodeItem.Hand.Block800d698c.DesignedBoundary_800d698c Sigma islaG0 H)
    (H69b0 Sigma islaG0 H)
    (@ZesuSsz.Proofs.DecodeItem.Hand.Block800d69e8.DesignedBoundary_800d69e8 Sigma islaG0 H)
    (@ZesuSsz.Proofs.DecodeItem.Hand.Block800d6a08.DesignedBoundary_800d6a08 Sigma islaG0 H)
    (H6a24 Sigma islaG0 H)
    (@ZesuSsz.Proofs.DecodeItem.Hand.Block800d6a38.DesignedBoundary_800d6a38 Sigma islaG0 H)
    (H6a40 Sigma islaG0 H)
    (H6a78 Sigma islaG0 H)
    (H6aa8 Sigma islaG0 H)
    (H6ac4 Sigma islaG0 H)
    (H6ad8 Sigma islaG0 H)
    (@ZesuSsz.Proofs.DecodeItem.Hand.Block800d6ae0.DesignedBoundary_800d6ae0 Sigma islaG0 H)
    (@ZesuSsz.Proofs.DecodeItem.Hand.Block800d6b08.DesignedBoundary_800d6b08 Sigma islaG0 H)).
Qed.
Print Assumptions decodeItemOpenNativeBlockCount.
Print Assumptions decodeItemOpenNativeHypothesesTable.

(* Retained I62 measurements at 33b9a455; these counts are not proof premises. *)
Definition decodeItemI62NativeResidualCounts : list (Z * nat) :=
  [(0x800d6960, 7%nat);
   (0x800d6974, 0%nat);
   (0x800d697c, 3%nat);
   (0x800d698c, 3%nat);
   (0x800d69b0, 5%nat);
   (0x800d69e8, 3%nat);
   (0x800d6a08, 4%nat);
   (0x800d6a24, 8%nat);
   (0x800d6a38, 1%nat);
   (0x800d6a40, 5%nat);
   (0x800d6a78, 5%nat);
   (0x800d6aa8, 4%nat);
   (0x800d6ac4, 8%nat);
   (0x800d6ad8, 1%nat);
   (0x800d6ae0, 4%nat);
   (0x800d6b08, 5%nat)].

(* I67 measured e17a8888. None records an unavailable active count.
   These printed active counts are not complete kernel goal groups. *)
Definition decodeItemI67NativeResidualCounts : list (Z * option nat) :=
  [(0x800d69b0, Some 3%nat);
   (0x800d6a24, Some 8%nat);
   (0x800d6a40, Some 3%nat);
   (0x800d6a78, Some 3%nat);
   (0x800d6aa8, Some 4%nat);
   (0x800d6ac4, Some 8%nat);
   (0x800d6ad8, Some 1%nat)].

Lemma decodeItemI67StatusMatchesOpenBlocks :
  map fst decodeItemI67NativeResidualCounts = decodeItemOpenNativeBlocks.
Proof. reflexivity. Qed.

Lemma decodeItemProduction6974Closed : decodeItemOpenNativeClosure6974.
Proof.
  intros Sigma HG HT.
  exact (@ZesuSsz.Proofs.DecodeItem.Auto.Block800d6974.DesignedBoundary_800d6974 Sigma HG HT).
Qed.
Print Assumptions decodeItemI67StatusMatchesOpenBlocks.
Print Assumptions decodeItemProduction6974Closed.
