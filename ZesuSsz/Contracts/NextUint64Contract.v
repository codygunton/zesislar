From Coq Require Import List ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Contracts.ParentHeader.
Require Import ZesuSsz.Contracts.ParentHeaderRootFacts.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.NextUint64BlockEntries.
Require Import ZesuSsz.Contracts.NextUint64Selected.
Open Scope Z_scope.

(* The public entry owns the caller's 96 bytes and the callee's separate 16 bytes. *)
Definition nextUint64ContractEntry `{!islaG Sigma} `{!threadG}
    (returnAddress : Z) (params : NextUint64Args) : iProp Sigma :=
  (nextUint64BoundaryEntry params ∗
   ⌜nextReturnAddress (nextUint64Base params) = returnAddress⌝ ∗ True)%I.

(* The ABI returns caller-saved registers with arbitrary bit-vector values.
   It preserves all twelve callee-saved registers and the stack pointer. *)
Definition nextUint64ContractExit `{!islaG Sigma} `{!threadG}
    (params : NextUint64Args) (result : NextUint64Return) : iProp Sigma :=
  let args := nextUint64Base params in
  (∃ x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : bv 64,
   reg_col (nextUint64SysRegs params) ∗
   nextUint64Registers
     (Z_to_bv 64 (nextReturnAddress args))
     (Z_to_bv 64 (nextStackPointer args)) x5 x6 x7
     (nextSavedS0 args) (nextSavedS1 args) x10 x11 x12 x13 x14 x15 x16 x17
     (nextSavedS2 args) (nextSavedS3 args) (nextSavedS4 args)
     (nextUint64SavedX21 params) (nextUint64SavedX22 params)
     (nextUint64SavedX23 params) (nextUint64SavedX24 params)
     (nextUint64SavedX25 params) (nextUint64SavedX26 params)
     (nextUint64SavedX27 params) x28 x29 x30 x31 ∗
   nextInputPointer args ↦ₘ∗ nextInputBytes args ∗
   nextSlicePointer args ↦ₘ∗
     nextUint64SliceImage (nextRestPointer result) (nextRestLength result) ∗
   nextResultPointer args ↦ₘ∗ nextResultBytes result ∗
   (nextStackPointer args - nextUint64StackBytes) ↦ₘ? nextUint64StackBytes ∗
   (nextStackPointer args - nextUint64StackBytes - decodeItemStackBytes) ↦ₘ?
     decodeItemStackBytes ∗ True)%I.

(* The result image carries error!u64. The slice image carries rest.*.
   The existing relation leaves unwritten result padding unconstrained. *)
Definition nextUint64ContractAllows (returnAddress : Z)
    (params : NextUint64Args) (result : NextUint64Return) : Prop :=
  nextReturnAddress (nextUint64Base params) = returnAddress /\
  nextUint64BoundaryDomain params /\
  nextUint64RootResult (nextUint64Base params) result.

Definition nextUint64ContractResources `{!islaG Sigma} `{!threadG}
    (returnAddress : Z) :
    IslarisContractResources NextUint64Args NextUint64Return :=
  {| islarisCode := nextUint64SelectedCode;
     islarisEntry := nextUint64ContractEntry returnAddress;
     islarisExit := nextUint64ContractExit |}.

Definition nextUint64ContractModel (returnAddress : Z) :
    IslarisContractModel NextUint64Args NextUint64Return :=
  {| islarisContractAllows := nextUint64ContractAllows returnAddress;
     islarisContractStep := fun source target =>
       ZesuSsz.Stock.Closure.index_nextUint64.nextUint64_cfg_step source target \/
       ZesuSsz.Stock.Closure.index_decodeItem.decodeItem_cfg_step source target;
     islarisContractResources := fun Sigma HG HT =>
       @nextUint64ContractResources Sigma HG HT returnAddress |}.

(* This declaration states the native proof objective. It does not prove it. *)
Definition NextUint64ContractCorrect : Prop :=
  forall returnAddress,
    IslarisContractCorrect nextUint64Entry returnAddress
      (nextUint64ContractModel returnAddress).
