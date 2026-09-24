Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Endpoints.
From IslaTraces.write_success_89 Require Import instrs.
From ZesuSsz.Proofs.WriteSuccess Require Import
  Interfaces WriteSuccessExactPostWithdrawalsSegment
  WriteSuccessExactWithdrawalsHeadConnection WriteSuccessNativeContract
  WriteSuccessRepresentation.

Lemma write_success_exact_withdrawals_nonzero_region
    `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded) (P : iProp Sigma)
    (Hwf : writeSuccessWitnessWellFormed args witness) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15d10 encoderIntEntryBoundary -∗
  □ instr_pre 0x15bc8 encoderOptionalEntryBoundary -∗
  □ instr_pre 0x15c6c encoderBytesEntryBoundary -∗
  □ instr_pre 0x10190 writeOutputEntryBoundary -∗
  instr_body 0x15744
    (writeSuccessSuffixHashesBoundary
      (fun _ => writeSuccessExactPostWithdrawalsExitFrame args witness P)) -∗
  withdrawalLoopCode -∗
  instr_body 0x15694
    (exactTailWithdrawalsBranchNonzeroEntry args witness P).
Proof.
  iStartProof.
  iIntros "#Hlookup #Hresources #Hint #Hoptional #Hbytes #Houtput Hsuffix
    #Hloop".
  iPoseProof (write_success_exact_post_withdrawals_segment args witness P Hwf
    with "Hlookup Hresources Hint Hoptional Hbytes Houtput Hsuffix") as "Hpost".
  iApply (write_success_exact_withdrawals_head_connection args witness P Hwf with
    "Hloop Hpost").
Qed.

Print Assumptions write_success_exact_withdrawals_nonzero_region.
