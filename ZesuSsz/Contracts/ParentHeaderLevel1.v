From Coq Require Import List ZArith.
From stdpp Require Import bitvector.definitions.
Require Import isla.isla isla.riscv64.riscv64.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.ParentHeader.
Require Import ZesuSsz.Contracts.ParentHeaderRootFacts.
Require Import ZesuSsz.Contracts.ZiskRuntime.

Open Scope Z_scope.

(* These are internal handoff statements, not public Level 1 root contracts.
   Their fixed exit PCs name return instructions or a tail jump. A complete
   root proof must execute each return through the caller return address,
   including the memcpy tail path, and establish the exact output relation.
   nested wrap classification remains a separate composition obligation. *)
Definition nextUint64Domain (args : NextUint64Call) : Prop :=
  nextUint64EntryLayout
    args.(nextInputPointer) (Z.of_nat (List.length args.(nextInputBytes)))
    args.(nextSlicePointer) args.(nextResultPointer)
    args.(nextStackPointer) args.(nextReturnAddress).

Definition nextUint64Allows (args : NextUint64Call)
    (ret : NextUint64Return) : Prop :=
  nextUint64Domain args /\ nextUint64RootResult args ret.

Definition NextUint64InternalHandoffSpec {Sigma : gFunctors}
    (HG : islaG Sigma) (HT : threadG)
    (resources : @IslarisContractResources Sigma HG HT
      NextUint64Call NextUint64Return) : iProp Sigma :=
  @IslarisContractSpec riscv64_arch Sigma HG HT
    NextUint64Call NextUint64Return nextUint64Entry nextUint64ReturnPc
    nextUint64Allows resources.

Definition NextUint64InternalHandoffCorrect
    (resources : forall (Sigma : gFunctors) (HG : islaG Sigma) (HT : threadG),
      @IslarisContractResources Sigma HG HT
        NextUint64Call NextUint64Return) : Prop :=
  forall (Sigma : gFunctors) (HG : islaG Sigma) (HT : threadG),
    ⊢ NextUint64InternalHandoffSpec HG HT (resources Sigma HG HT).

Record ParentHeaderCall := {
  headerInputPointer : Z;
  headerInputBytes : list byte;
  headerResultPointer : Z;
  headerStackPointer : Z;
  headerReturnAddress : Z;
  headerSavedS0 : bv 64;
  headerSavedS1 : bv 64;
  headerSavedS2 : bv 64;
  headerSavedS3 : bv 64;
  headerSavedS4 : bv 64;
  headerSavedS5 : bv 64;
  headerSavedS6 : bv 64;
  headerSavedS7 : bv 64;
  headerSavedS8 : bv 64;
  headerBeforeFrame : list byte;
  headerMemcpySourceBefore : list byte;
  headerMemcpyScratchBefore : list byte
}.

Definition parentHeaderDomain (args : ParentHeaderCall) : Prop :=
  parentHeaderEntryLayout
    args.(headerInputPointer) (Z.of_nat (List.length args.(headerInputBytes)))
    args.(headerResultPointer) args.(headerStackPointer)
    args.(headerReturnAddress).

(* This direct-return schema describes the 80-byte error union. A later
   decoder proof must strengthen success with the exact input-to-field
   relation before claiming the Level 1 contract is discharged. *)
Definition parentHeaderDirectAllows (args : ParentHeaderCall)
    (result : list byte) : Prop :=
  parentHeaderDomain args /\
  (parentHeaderError80 result \/
   exists header, parentHeaderResult80 result header).

Record ParentHeaderTailCall := {
  tailTargetPc : Z;
  tailDestination : Z;
  tailSource : Z;
  tailLength : Z;
  tailCallerReturn : Z
}.

(* The tail transfer is at 0x800d5da0. The original ra is restored before
   the jump. This relation stops before memcpy executes. The service contract
   supplies its entry identity here. This handoff gives no post-call result. *)
Definition parentHeaderTailAllows (memcpy : ZiskMemcpyServiceContract)
    (args : ParentHeaderCall) (tail : ParentHeaderTailCall) : Prop :=
  parentHeaderDomain args /\
  memcpy.(ziskMemcpyEntryPc) = 0x800e06c0 /\
  tail.(tailTargetPc) = memcpy.(ziskMemcpyEntryPc) /\
  tail.(tailDestination) = args.(headerResultPointer) /\
  tail.(tailSource) = 0x80114fb8 /\
  tail.(tailLength) = 80 /\
  tail.(tailCallerReturn) = args.(headerReturnAddress).

Definition ParentHeaderDirectHandoffSpec {Sigma : gFunctors}
    (HG : islaG Sigma) (HT : threadG)
    (resources : @IslarisContractResources Sigma HG HT
      ParentHeaderCall (list byte)) : iProp Sigma :=
  @IslarisContractSpec riscv64_arch Sigma HG HT
    ParentHeaderCall (list byte) decodeParentHeaderEntry parentHeaderReturnPc
    parentHeaderDirectAllows resources.

Definition ParentHeaderTailHandoffSpec {Sigma : gFunctors}
    (HG : islaG Sigma) (HT : threadG) (memcpy : ZiskMemcpyServiceContract)
    (resources : @IslarisContractResources Sigma HG HT
      ParentHeaderCall ParentHeaderTailCall) : iProp Sigma :=
  @IslarisContractSpec riscv64_arch Sigma HG HT
    ParentHeaderCall ParentHeaderTailCall decodeParentHeaderEntry
    parentHeaderTailPc (parentHeaderTailAllows memcpy) resources.

Definition ParentHeaderDirectHandoffCorrect
    (resources : forall (Sigma : gFunctors) (HG : islaG Sigma) (HT : threadG),
      @IslarisContractResources Sigma HG HT ParentHeaderCall (list byte))
    : Prop :=
  forall (Sigma : gFunctors) (HG : islaG Sigma) (HT : threadG),
    ⊢ ParentHeaderDirectHandoffSpec HG HT (resources Sigma HG HT).

Definition ParentHeaderTailHandoffCorrect (memcpy : ZiskMemcpyServiceContract)
    (resources : forall (Sigma : gFunctors) (HG : islaG Sigma) (HT : threadG),
      @IslarisContractResources Sigma HG HT
        ParentHeaderCall ParentHeaderTailCall) : Prop :=
  forall (Sigma : gFunctors) (HG : islaG Sigma) (HT : threadG),
    ⊢ ParentHeaderTailHandoffSpec HG HT memcpy (resources Sigma HG HT).

(* These obligations remain before a public contract can claim completion:
   - nextUint64: execute the instruction at nextUint64ReturnPc and prove that
     its target is nextReturnAddress.
   - decodeParentHeader direct path: execute the instruction at
     parentHeaderReturnPc and prove that its target is headerReturnAddress.
   - decodeParentHeader tail path: compose the memcpy service contract at
     parentHeaderTailPc, then prove return to headerReturnAddress.
   All paths must relate input bytes to exact output fields. *)
