From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index HintsTransactionsLoop.
From IslaTraces.write_success_46 Require Import a1518c_spec.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Experiments.WriteSuccessCalls.
Require Import ZesuSsz.Experiments.WriteSuccessCallAbi.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsOptionalAddressSome1517cBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsOptionalAddressSome1518cCallAdapter.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsOptionalAddressSome1518cCallFrame.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsOptionalAddressSome15190.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsOptionalAddressSome15190Boundary.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsSpec.

Lemma write_success_transactions_optional_address_some_1518c_to_15190
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  instr_body 0x15190 (writeSuccessTransactionsOptionalAddressSomeAt15190Spec P) -∗
  instr_body 0x1518c (writeSuccessTransactionsOptionalAddressSomeAt1518cSpec P).
Proof.
  move => *. iStartProof.
  iIntros "_ #Hlookup #Hcode #Houtput Hnext".
  iPoseProof "Hlookup" as "#Hlookup1518c".
  iEval (rewrite /instr_lookup_resources) in "Hlookup1518c".
  iPoseProof ("Hlookup1518c" $! 0x1518c with "[]") as "#Hinstr1518c".
  { iPureIntro. rewrite IslaTraces.write_success_blocks.Index.lookup_a1518c. done. }
  iPoseProof (a1518c_spec 0x1518c with "Hinstr1518c") as "Hbody1518c".
  iClear "Hlookup1518c".
  iEval (rewrite instr_pre'_eq) in "Hbody1518c".
  rewrite instr_pre'_eq. iIntros "Hsetup".
  iEval (unfold writeSuccessTransactionsOptionalAddressSomeAt1518cSpec)
    in "Hsetup".
  iDestruct "Hsetup" as
    "(%sp & %base & %transaction & %transactions & %processed & %remaining &
      %bytes & %prefix & %suffix & %tail & Hsys & Hother & H1 & H2 & H5 & H12 &
      H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27 &
      H10 & H11 & Hscratch & Hmmio & Htrace & Hframe & _)".
  iApply "Hbody1518c".
  rewrite /InstrSpecs.Specs.zesu_jalr_same_spec.
  iExists (BV 64 0x10188). iFrame "Hsys H1".
  iSplit; first (iPureIntro; bv_solve).
  have Htarget :
    bv_unsigned
      (bv_or (bv_and ((BV 64 0x10188) + BV 64 8)%bv
        (BV 64 18446744073709551614)) (BV 64 0)) = 0x10190
    by bv_solve.
  rewrite Htarget.
  iDestruct (bi.intuitionistically_elim with "Houtput") as "HoutputReady".
  iEval (rewrite -instr_pre'_eq) in "HoutputReady Hnext".
  iApply (instr_pre_wand 0x10190 0x10190 true true with "HoutputReady");
    [done | reflexivity |].
  iIntros "(Hsys & H1 & _)".
  have Hret : Z_to_bv 64 (86412 + 4) = BV 64 0x15190 by bv_solve.
  iEval (rewrite Hret) in "H1".
  iAssert (writeSuccessTransactionsOptionalAddressSome1518cCallFrame P sp base
    transaction transactions processed remaining bytes prefix suffix tail)%I
    with "[Hsys Hother H1 H2 H5 H12 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25
      H26 H27 H10 H11 Hscratch Hmmio Htrace Hframe Hnext]" as "Hentry".
  { rewrite /writeSuccessTransactionsOptionalAddressSome1518cCallFrame.
    iFrame "Hsys Hother H1 H2 H5 H12 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25
      H26 H27 H10 H11 Hscratch Hmmio Htrace Hframe Hnext"; done. }
  iApply (write_success_transactions_optional_address_some_1518c_call_adapter
    P sp base transaction transactions processed remaining bytes prefix suffix tail
    with "Hentry").
Qed.
