Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import
  Index HintsTransactionsLoop.
From IslaTraces.write_success_42 Require Import a15144_spec.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderBooleanCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeCore.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeBooleanCallEntry.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeNoneBoundary.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Lemma write_success_transactions_priority_fee_none_call
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15b9c zesuEncoderBooleanCallSpec -∗
  instr_body 0x15148 (writeSuccessTransactionsPriorityFeePostSpec P) -∗
  instr_body 0x15144 (writeSuccessTransactionsPriorityFeeNoneAt15144Spec P).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode #Hboolean Hnext".
  iPoseProof "Hlookup" as "#Hlookup15144".
  iEval (rewrite /instr_lookup_resources) in "Hlookup15144".
  iPoseProof ("Hlookup15144" $! 0x15144 with "[]") as "#Hinstr".
  { iPureIntro. rewrite IslaTraces.write_success_blocks.Index.lookup_a15144.
    done. }
  iPoseProof (a15144_spec 0x15144 with "Hinstr") as "Hbody".
  iEval (rewrite instr_pre'_eq) in "Hbody".
  rewrite instr_pre'_eq. iIntros "Hsetup".
  iEval (unfold writeSuccessTransactionsPriorityFeeNoneAt15144Spec,
    writeSuccessTransactionsPriorityFeeBooleanSetupSpec) in "Hsetup".
  iDestruct "Hsetup" as
    "(%sp & %base & %transaction & %transactions & %processed & %remaining &
      %bytes & %prefix & %suffix & %tail & Hsys & Htmp & Hcaller & Hsaved &
      H1 & H2 & H10 & H11 & Hstack & Hmmio & Htrace & Hframe & %Halign &
      %Hlower & %Hupper & _)".
  iApply "Hbody".
  rewrite /InstrSpecs.Specs.zesu_jalr_same_spec.
  iExists (BV 64 0x16140).
  iFrame "Hsys H1".
  iSplit; first (iPureIntro; bv_solve).
  have Htarget :
    bv_unsigned
      (bv_or (bv_and ((BV 64 0x16140) + BV 64 18446744073709550172)%bv
        (BV 64 18446744073709551614)) (BV 64 0)) = 0x15b9c
    by native_compute.
  rewrite Htarget.
  iDestruct (bi.intuitionistically_elim with "Hboolean") as "HbooleanReady".
  iEval (rewrite -instr_pre'_eq) in "HbooleanReady".
  iApply (instr_pre_wand 0x15b9c 0x15b9c true true with "HbooleanReady");
    [done | reflexivity |].
  iIntros "(Hsys & H1 & _)".
  have Hret : Z_to_bv 64 (0x15144 + 4) = BV 64 0x15148 by bv_solve.
  iEval (rewrite Hret) in "H1".
  iAssert (writeSuccessTransactionsPriorityFeeBooleanCallPreparedSpec P)%I
    with "[Hsys Htmp Hcaller Hsaved H1 H2 H10 H11 Hstack Hmmio Htrace Hframe]"
    as "Hentry".
  { rewrite /writeSuccessTransactionsPriorityFeeBooleanCallPreparedSpec
      /writeSuccessTransactionsPriorityFeeBooleanSetupSpec.
    iExists sp, base, transaction, transactions, processed, remaining,
      bytes, prefix, suffix, tail.
    iFrame.
    repeat iSplit; try iPureIntro; try assumption; try done. }
  iEval (rewrite -instr_pre'_eq) in "Hnext".
  iApply (write_success_transactions_priority_fee_boolean_call_entry P
    with "Hnext Hentry").
Qed.
