From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index HintsTransactionsLoop.
From IslaTraces.write_success_39 Require Import a15124_spec.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderBooleanCall.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPriorityFeeSomeBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPriorityFeeSomeBooleanCallEntry.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Lemma write_success_transactions_priority_fee_some_call_15124
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15b9c zesuEncoderBooleanCallSpec -∗
  instr_body 0x15128
    (writeSuccessTransactionsPriorityFeeSomeAt15128Spec P) -∗
  instr_body 0x15124
    (writeSuccessTransactionsPriorityFeeSomeAt15124Spec P).
Proof.
  move => *. iStartProof.
  iIntros "_ #Hlookup #Hcode #Hboolean Hnext".
  iPoseProof "Hlookup" as "#Hlookup15124".
  iEval (rewrite /instr_lookup_resources) in "Hlookup15124".
  iPoseProof ("Hlookup15124" $! 0x15124 with "[]") as "#Hinstr".
  { iPureIntro. rewrite IslaTraces.write_success_blocks.Index.lookup_a15124.
    done. }
  iPoseProof (a15124_spec 0x15124 with "Hinstr") as "Hbody".
  iEval (rewrite instr_pre'_eq) in "Hbody".
  rewrite instr_pre'_eq. iIntros "Hsetup".
  iEval (unfold writeSuccessTransactionsPriorityFeeSomeAt15124Spec)
    in "Hsetup".
  iDestruct "Hsetup" as
    "(%sp & %base & %transaction & %transactions & %processed & %remaining &
      %bytes & %prefix & %suffix & %tail & Hsys & Htmp & Hcaller & Hsaved &
      H1 & H2 & H10 & H11 & Hstack & Hmmio & Htrace & Hframe & %Halign &
      %Hlower & %Hupper & _)".
  iApply "Hbody".
  rewrite /InstrSpecs.Specs.zesu_jalr_same_spec.
  iExists (BV 64 0x16120).
  iFrame "Hsys H1".
  iSplit; first (iPureIntro; bv_solve).
  have Htarget :
    bv_unsigned
      (bv_or (bv_and ((BV 64 0x16120) + BV 64 18446744073709550204)%bv
        (BV 64 18446744073709551614)) (BV 64 0)) = 0x15b9c
    by native_compute.
  rewrite Htarget.
  iDestruct (bi.intuitionistically_elim with "Hboolean") as "HbooleanReady".
  iEval (rewrite -instr_pre'_eq) in "HbooleanReady".
  iApply (instr_pre_wand 0x15b9c 0x15b9c true true with "HbooleanReady");
    [done | reflexivity |].
  iIntros "(Hsys & H1 & _)".
  have Hret : Z_to_bv 64 (0x15124 + 4) = BV 64 0x15128 by bv_solve.
  iEval (rewrite Hret) in "H1".
  iAssert (writeSuccessTransactionsPriorityFeeSomeBooleanPreparedSpec P)%I
    with "[Hsys Htmp Hcaller Hsaved H1 H2 H10 H11 Hstack Hmmio Htrace Hframe]"
    as "Hentry".
  { rewrite /writeSuccessTransactionsPriorityFeeSomeBooleanPreparedSpec.
    iExists sp, base, transaction, transactions, processed, remaining,
      bytes, prefix, suffix, tail.
    iFrame.
    repeat iSplit; try iPureIntro; try assumption; done. }
  iEval (rewrite -instr_pre'_eq) in "Hnext".
  iApply (write_success_transactions_priority_fee_some_boolean_call_entry P
    with "Hnext Hentry").
Qed.
