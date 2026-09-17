Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Contracts.IslarisCode.
From ZesuSsz.Proofs.WriteSuccess Require Import
  Interfaces WriteSuccessNativeContract WriteSuccessRepresentation.

Lemma write_success_exact_tail_fields_third_segment
    `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  □ instr_pre 0x15bc8 encoderOptionalEntryBoundary -∗
  □ instr_pre 0x15c10 encoderByteListsEntryBoundary -∗
  instr_body 0x159d8
    (writeSuccessEpilogueSpec (writeSuccessExactEpilogueExit witness)) -∗
  instr_body 0x159b8
    (writeSuccessExactTailSecondBranchState args witness).
Proof.
  zesu_block. iIntros.
  iRename select ((bv_unsigned (writeSuccessFrameSp witness) + 296) ↦ₘ _)%I into "Hlow".
  iRename select ((bv_unsigned (writeSuccessFrameSp witness) + 304) ↦ₘ _)%I into "Hhigh".
  iEval (replace (bv_unsigned (writeSuccessFrameSp witness) + 304)%Z with
    (bv_unsigned (writeSuccessFrameSp witness) + 296 + 8)%Z by lia) in "Hhigh".
  iDestruct (mem_mapsto_u64_pair_to_byte_array with "Hlow Hhigh") as "Hbytes".
  zesu_run. all: try bv_solve.
  rename select (writeSuccessExactTailSecondBranchEvents witness = _) into Hevents.
  iExists (writeSuccessExactTailThirdBranchEvents witness, tt)ₗ.
  rewrite -Hevents.
  iRename select (instr_pre 0x159bc _)%I into "Hreturn".
  zesu_run.
  rewrite /subsume; iIntros "_"; iExists tt; iSplit; last done.
  iEval (replace (Z_to_bv 64 88504 + 4)%bv with (BV 64 88508) by bv_solve);
    iEval (replace (bv_unsigned (BV 64 88508)) with 88508 by bv_solve).
  iApply (instr_pre_wand 88508 88508 true true with "Hreturn");
    [done | reflexivity |]; iIntros "Hrequested"; iFrame;
    repeat iSplit; iPureIntro; assumption.
Qed.

Print Assumptions write_success_exact_tail_fields_third_segment.
