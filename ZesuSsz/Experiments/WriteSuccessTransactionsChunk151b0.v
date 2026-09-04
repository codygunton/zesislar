Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
From IslaTraces.write_success_49 Require Import a151b0_spec.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderU256.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsChunk151b0Prepared.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Lemma write_success_transactions_chunk_151b0_core
    `{!islaG Sigma} `{!threadG} :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  □ instr_pre 0x15cb0 zesuEncoderU256CallSpec -∗
  instr_body 0x151b0 writeSuccessTransactions151b0PreparedSpec.
Proof.
  iStartProof. iIntros "#Hlookup #Hu256".
  iPoseProof "Hlookup" as "#Hlookup151b0".
  iEval (rewrite /instr_lookup_resources) in "Hlookup151b0".
  iPoseProof ("Hlookup151b0" $! 0x151b0 with "[]") as "#Hinstr".
  { iPureIntro. rewrite IslaTraces.write_success_blocks.Index.lookup_a151b0.
    done. }
  iPoseProof (a151b0_spec 0x151b0 with "Hinstr") as "Hbody".
  iEval (rewrite instr_pre'_eq) in "Hbody".
  rewrite instr_pre'_eq. iIntros "Hsetup".
  iEval (unfold writeSuccessTransactions151b0PreparedSpec) in "Hsetup".
  iDestruct "Hsetup" as
    "(%sp & %b5 & %b12 & %b13 & %b14 & %b15 & %b16 & %b17 & %transaction &
      %remaining & %tail & Hsys & H1 & Hframe & _)".
  iApply "Hbody".
  rewrite /InstrSpecs.Specs.zesu_jalr_same_spec.
  iExists (Z_to_bv 64 90540).
  replace (Z_to_bv 64 90540)
    with (Z_to_bv 64 86444 + 4096)%bv by bv_solve.
  iFrame "Hsys H1".
  iSplit; first (iPureIntro; bv_solve).
  have Htarget :
      bv_unsigned
        (bv_or
          (bv_and
            ((Z_to_bv 64 86444 + 4096) + 18446744073709550340)
            18446744073709551614)
          0) = 0x15cb0 by native_compute.
  rewrite Htarget.
  iDestruct (bi.intuitionistically_elim with "Hu256") as "Hu256Ready".
  iEval (rewrite -instr_pre'_eq) in "Hu256Ready".
  iApply (instr_pre_wand 0x15cb0 0x15cb0 true true with "Hu256Ready");
    [done | reflexivity |].
  iIntros "(Hsys & H1 & _)".
  iEval (replace (Z_to_bv 64 (86448 + 4)) with (BV 64 0x151b4)
    by bv_solve) in "H1".
  iApply (write_success_transactions_151b0_call sp b5 b12 b13 b14 b15 b16
    b17 transaction remaining tail with "Hsys H1 Hframe").
Qed.
