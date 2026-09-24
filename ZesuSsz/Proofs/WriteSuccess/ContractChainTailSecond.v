Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Endpoints.
From IslaTraces.write_success_blocks Require Import Index.
From ZesuSsz.Proofs.WriteSuccess Require Import
  Interfaces WriteSuccessNativeContract WriteSuccessRepresentation
  WriteSuccessExactTailFieldsThirdSegment WriteSuccessExactEpilogueSegment
  ContractChainEpilogueCode.

(** The 0x1596c wand translates the frozen TF2 draft.
    That draft also needs code and call premises and fixes its tail. *)
Lemma draft_tail_second_through_epilogue
    `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded) (tail : spec) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  □ instr_pre 0x15bc8 encoderOptionalEntryBoundary -∗
  □ instr_pre 0x15c10 encoderByteListsEntryBoundary -∗
  (instr_body 0x159b8
      (writeSuccessExactTailSecondBranchState args witness) -∗
   instr_body 0x1596c
      (writeSuccessExactTailFirstBranchState args witness tail)) -∗
  instr_body 0x1596c
    (writeSuccessExactTailFirstBranchState args witness tail).
Proof.
  iIntros "#Hlookup #Hoptional #Hlists Hsecond".
  iApply "Hsecond".
  iApply (write_success_exact_tail_fields_third_segment args witness
    with "Hlookup Hoptional Hlists").
  iApply (write_success_exact_epilogue_segment witness).
  iApply draft_epilogue_code_from_lookup. iExact "Hlookup".
Qed.

Print Assumptions draft_tail_second_through_epilogue.
