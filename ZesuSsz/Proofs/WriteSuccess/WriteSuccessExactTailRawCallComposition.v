Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeContract.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessRepresentation.
Require Import ZesuSsz.Proofs.WriteSuccess.Interfaces.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessValueBlock.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactSuffixByteListPayloadAtSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTailByteListPayload15674At.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTailRawCallSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTailRawCallEntrySpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTailRawCallReturnSpec.
Open Scope Z_scope.

Lemma exact_tail_raw_call `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded) (witness : writeSuccessNativeWitness Decoded)
    (P : iProp Sigma) :
  writeSuccessCompleteNativeCode -∗
  □ instr_pre 0x15678 (exactTailRawCallReturn args witness P) -∗
  instr_body 0x15674 (exactTailRawCallEntry args witness P).
Proof.
  iIntros "#Hcode #Hnext".
  rewrite instr_pre'_eq.
  iEval (rewrite -instr_pre'_eq) in "Hnext".
  iIntros "Hentry".
  rewrite /exactTailRawCallEntry.
  iDestruct "Hentry" as (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) "Hentry".
  iAssert (□ instr_pre 0x15678
    (exactSuffixByteListReturnAt (BV 64 0x15678) (writeSuccessFrameSp witness)
      (writeSuccessValueWord (writeSuccessValues witness) 9)
      (writeSuccessValueWord (writeSuccessValues witness) 10)
      (writeSuccessRawTransactions witness) (exactTailAfterRawEvents witness)
      s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
      (exactTailRawCallFrame args witness P)))%I with "[]" as "#HnextExact".
  { iModIntro.
    iApply (instr_pre_wand 0x15678 0x15678 true true
      (exactTailRawCallReturn args witness P)
      (exactSuffixByteListReturnAt (BV 64 0x15678) (writeSuccessFrameSp witness)
        (writeSuccessValueWord (writeSuccessValues witness) 9)
        (writeSuccessValueWord (writeSuccessValues witness) 10)
        (writeSuccessRawTransactions witness) (exactTailAfterRawEvents witness)
        s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
        (exactTailRawCallFrame args witness P)) with "Hnext");
      [done | reflexivity |].
    iIntros "Hreturn".
    rewrite /exactTailRawCallReturn.
    iExists s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11.
    iExact "Hreturn". }
  iPoseProof (exact_suffix_15674_payload_at
    (writeSuccessFrameSp witness)
    (writeSuccessValueWord (writeSuccessValues witness) 9)
    (writeSuccessValueWord (writeSuccessValues witness) 10)
    (writeSuccessRawTransactions witness) (exactTailAfterRawEvents witness)
    s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    (exactTailRawCallFrame args witness P) with "Hcode HnextExact") as "Hbody".
  iEval (rewrite instr_pre'_eq) in "Hbody".
  iApply ("Hbody" with "Hentry").
Qed.

Print Assumptions exact_tail_raw_call.
