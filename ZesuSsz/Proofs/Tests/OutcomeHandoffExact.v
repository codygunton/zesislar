Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.OutcomeHandoff.
Require Import ZesuSsz.Automation.Switches.OutcomeHandoff.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Contracts.IslarisCode.
From ZesuSsz.Proofs.WriteSuccess Require Import
  Interfaces WriteSuccessNativeContract WriteSuccessRepresentation.

Lemma test_outcome_handoff_exact_tf3
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
  rewrite /subsume; iIntros "Hwords".
  iPoseProof (IslarisMemory.mem_mapsto_u64_array_to_bytes with "Hwords") as "Hbytes".
  iEval (cbn [IslarisMemory.bytes_of_u64s]) in "Hbytes".
  iEval (replace (bv_unsigned (writeSuccessFrameSp witness) + 296)%Z with
    (bv_unsigned (writeSuccessFrameSp witness + BV 64 296)) by bv_solve) in "Hbytes".
  zesu_run.
  all: try bv_solve.
  all: try (match goal with
    | Htrace : writeSuccessExactTailSecondBranchEvents _ = _ |- _ =>
        rewrite Htrace; done
    end).
  iRename select (instr_pre 0x159bc _)%I into "Hreturn".
  zesu_run.
  rewrite /subsume.
  iExists (writeSuccessExactTailThirdBranchEvents witness, tt)ₗ.
  iSplit; first (iPureIntro;
    match goal with
    | Htrace : writeSuccessExactTailSecondBranchEvents _ = _ |- _ =>
        rewrite Htrace
    end; set_solver).
  repeat (iSplit; first (iPureIntro; first [assumption | bv_solve])).
  iSplit; last done.
  iEval (replace (Z_to_bv 64 88504 + 4)%bv with (BV 64 88508) by bv_solve);
    iEval (replace (bv_unsigned (BV 64 88508)) with 88508 by bv_solve).
  iApply (instr_pre_wand 88508 88508 true true with "Hreturn");
    [done | reflexivity |]; iIntros "Hrequested"; iFrame;
    repeat iSplit; iPureIntro; assumption.
Qed.

Print Assumptions test_outcome_handoff_exact_tf3.
