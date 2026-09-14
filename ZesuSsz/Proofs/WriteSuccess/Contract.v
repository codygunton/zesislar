Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import ZArith.ZArith.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Proofs.WriteSuccess.Interfaces.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeContract.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessRepresentation.

(** Phase 3.5 fixes the public target before the region proofs arrive.
    The final theorem must discharge this proposition without region premises.
    Transactions use the exact live boundaries exported by [Interfaces].
    The entry chain reaches 0x14f04. Transactions reach 0x15668.
    The tail chain returns [writeSuccessTerminalResources] at 0x14d10. *)
Definition writeSuccessContractTarget {Decoded}
    `{!WriteSuccessMemoryRepresentation Decoded}
    (allows : WriteSuccessArgs Decoded -> ByteString -> Prop)
    (outputRelation : WriteSuccessOutputRelation Decoded)
    (nextPc : Z -> Z -> Prop) : Prop :=
  IslarisContractCorrect 0x14d30 0x14d10
    (writeSuccessNativeModel allows outputRelation nextPc).

(** The exact target preserves the caller trace and returned registers. *)
Definition writeSuccessFixedTailContractTarget {Decoded}
    `{!WriteSuccessMemoryRepresentation Decoded}
    (allows : WriteSuccessArgs Decoded -> ByteString -> Prop)
    (outputRelation : WriteSuccessOutputRelation Decoded)
    (fixedTail : spec) (nextPc : Z -> Z -> Prop) : Prop :=
  IslarisContractCorrect 0x14d30 0x14d10
    (writeSuccessFixedTailModel allows outputRelation fixedTail nextPc).
