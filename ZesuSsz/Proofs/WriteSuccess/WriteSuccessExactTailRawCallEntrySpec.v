Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeContract.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessRepresentation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessByteLists.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessValueBlock.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactSuffixByteListPayloadAtSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTailRawCallSpec.
Open Scope Z_scope.
Definition exactTailRawCallEntry `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded) (witness : writeSuccessNativeWitness Decoded)
    (P : iProp Sigma) : iProp Sigma :=
  (∃ s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : bv 64,
    exactSuffixByteListEntryAt (BV 64 0x15670) (writeSuccessFrameSp witness)
      (writeSuccessValueWord (writeSuccessValues witness) 9)
      (writeSuccessValueWord (writeSuccessValues witness) 10)
      (writeSuccessRawTransactions witness) (exactTailAfterRawEvents witness)
      s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
      (exactTailRawCallFrame args witness P))%I.
Global Instance : LithiumUnfold (@exactTailRawCallEntry) := I.
