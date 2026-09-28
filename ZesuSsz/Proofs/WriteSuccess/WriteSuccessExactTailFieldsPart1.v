Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Lookup.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessRepresentation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeContract.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputDescriptors.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputSemantic.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPostTransactionDescriptors.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactSuffixBytesPayload158e0At.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactSuffixBytesPayload158f0At.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactSuffixBytesPayload15900At.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactSuffixBytesPayload15910At.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactSuffixBytesPayload15920At.
Require Import ZesuSsz.Proofs.WriteSuccess.Interfaces.

Definition writeSuccessExactTailAfterFirstBytesReady {Decoded}
    (witness : writeSuccessNativeWitness Decoded) : spec :=
  let descriptors := writeSuccessPost158e0Descriptors
    (writeSuccessFrameSp witness) (writeSuccessPostData witness) in
  writeOutputPayloadsSpec (drop 2 descriptors)
    (drop 2 (writeSuccessExactPostPayloadsAt descriptors witness))
    (writeSuccessTraceTail witness).

Lemma write_success_exact_tail_fields_part1
    `{!islaG Sigma} `{!threadG} {Decoded}
    `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded) (oldS0 oldS1 : bv 64) :
  writeSuccessCompleteNativeCode -∗
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15c6c encoderBytesEntryBoundary -∗
  □ instr_pre 0x15c10 encoderByteListsEntryBoundary -∗
  □ instr_pre 0x15d10 encoderIntEntryBoundary -∗
  instr_body 0x1596c
    (writeSuccessTailFirstBranchBoundary
      (fun _ => writeSuccessExactTailFirstBranchState args witness
        (writeSuccessExactTailFirstBranchEvents witness))) -∗
  instr_body 0x158e0
    (writeSuccessExactTailFieldsEntryBoundary
      (writeSuccessFrameSp witness)
      (fst (writeSuccessPostBytes158e0 (writeSuccessPostData witness)))
      (snd (writeSuccessPostBytes158e0 (writeSuccessPostData witness)))
      oldS0 oldS1
      (writeSuccessPostBytes158e0Payload (writeSuccessPostData witness))
      (writeSuccessExactTailAfterFirstBytesReady witness)
      (writeSuccessExactTailRemainingDescriptorSlots args witness)).
Proof.
  move => *.
  iIntros "_ #Hnative #Hlookup #Hcode #Hbytes #Hlists #Hint Hnext".
  repeat first
    [ iApply (exact_suffix_bytes_158e0_payload_at with "Hnative")
    | iApply (exact_suffix_bytes_158f0_payload_at with "Hnative")
    | iApply (exact_suffix_bytes_15900_payload_at with "Hnative")
    | iApply (exact_suffix_bytes_15910_payload_at with "Hnative")
    | iApply (exact_suffix_bytes_15920_payload_at with "Hnative") ].
  zesu_block.
Qed.

Print Assumptions write_success_exact_tail_fields_part1.
