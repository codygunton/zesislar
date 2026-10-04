From Coq Require Import List ZArith.
Require Import EvmSailRlp.evm_rlp_types.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Machine.
Require Import ZesuSsz.Compliance.SailRun.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemSchema.

(* The ABI assigns a0 to output, a1 to input, and a2 to input length.
   The caller owns the 40-byte result and the 16-byte stack frame. *)
Record DecodeItemArgs : Type := {
  decodeItemOutputPointer : Z;
  decodeItemInputPointer : Z;
  decodeItemInputLength : Z;
  decodeItemInputBytes : list byte;
  decodeItemBeforeStorage : list byte;
  decodeItemStackPointer : Z;
  decodeItemReturnAddress : Z;
  decodeItemSavedFramePointer : bv 64
}.

Definition DecodeItemOutcome : Type := list byte.

Definition decodeItemArgsWellFormed (args : DecodeItemArgs) : Prop :=
  decodeItemInputLength args = Z.of_nat (List.length (decodeItemInputBytes args)) /\
  (List.length (decodeItemBeforeStorage args) = 40)%nat /\
  decodeItemEntryLayout
    (decodeItemInputPointer args) (decodeItemInputLength args)
    (decodeItemOutputPointer args) (decodeItemStackPointer args)
    (decodeItemReturnAddress args).

Definition decodeItemC1ADomain (args : DecodeItemArgs) : Prop :=
  decodeItemArgsWellFormed args /\ headerFits (decodeItemInputBytes args).

Definition decodeItemC1BDomain (args : DecodeItemArgs) : Prop :=
  decodeItemArgsWellFormed args.

Definition decodeItemDomainAt (returnAddress : Z)
    (domain : DecodeItemArgs -> Prop) (args : DecodeItemArgs) : Prop :=
  decodeItemReturnAddress args = returnAddress /\ domain args.

Definition decodeItemAllows
    (R : Z -> list byte -> list byte -> list byte -> Prop)
    (args : DecodeItemArgs) (after : DecodeItemOutcome) : Prop :=
  R (decodeItemInputPointer args) (decodeItemInputBytes args)
    (decodeItemBeforeStorage args) after.

Definition decodeItemAllowsC1A : DecodeItemArgs -> DecodeItemOutcome -> Prop :=
  decodeItemAllows C1AResult.

Definition decodeItemAllowsC1B : DecodeItemArgs -> DecodeItemOutcome -> Prop :=
  decodeItemAllows C1BResult.

Definition decodeItemSailCursor (args : DecodeItemArgs) :
    RlpCursor 0 (Z.of_nat (List.length (decodeItemInputBytes args))) :=
  {| StatelessInputSliceFields_bytes := 0;
     StatelessInputSliceFields_len :=
       Z.of_nat (List.length (decodeItemInputBytes args)) |}.

Definition decodeItemC1ASailResult
    (args : DecodeItemArgs) (after : DecodeItemOutcome) : Prop :=
  @relateItem 0 (Z.of_nat (List.length (decodeItemInputBytes args)))
    (decodeItemInputPointer args)
    (decodeItemInputBytes args) (decodeItemBeforeStorage args) after
    (runRlpDecodeItem (decodeItemInputBytes args) (decodeItemSailCursor args)).

Definition decodeItemEntryResources `{!islaG Sigma} `{!threadG}
    (domain : DecodeItemArgs -> Prop) (args : DecodeItemArgs) : iProp Sigma :=
  (reg_col zesu_sys_regs ∗
   "x10" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemOutputPointer args)) ∗
   "x11" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemInputPointer args)) ∗
   "x12" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemInputLength args)) ∗
   "x2" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemStackPointer args)) ∗
   "x1" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemReturnAddress args)) ∗
   "x8" ↦ᵣ RVal_Bits (decodeItemSavedFramePointer args) ∗
   decodeItemInputPointer args ↦ₘ∗ decodeItemInputBytes args ∗
   decodeItemOutputPointer args ↦ₘ∗ decodeItemBeforeStorage args ∗
   (decodeItemStackPointer args - decodeItemStackBytes) ↦ₘ? decodeItemStackBytes ∗
   ⌜domain args⌝ ∗ True)%I.

Definition decodeItemExitResources `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (after : DecodeItemOutcome) : iProp Sigma :=
  (reg_col zesu_sys_regs ∗
   "x2" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemStackPointer args)) ∗
   "x1" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemReturnAddress args)) ∗
   "x8" ↦ᵣ RVal_Bits (decodeItemSavedFramePointer args) ∗
   decodeItemInputPointer args ↦ₘ∗ decodeItemInputBytes args ∗
   decodeItemOutputPointer args ↦ₘ∗ after ∗
   (decodeItemStackPointer args - decodeItemStackBytes) ↦ₘ? decodeItemStackBytes ∗
   True)%I.
