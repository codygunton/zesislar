From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index HintsTransactionsLoop.
From IslaTraces.write_success_44 Require Import a15158.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCalls.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBitvector.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderBooleanCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15158.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary1519c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk15154SomePrefix.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk15154SomeContinuation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsOptionalAddressNone.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Ltac write_success_transactions_15158_to_nil :=
  lazymatch goal with
  | |- context[WPasm ?trace] =>
      let trace' := (eval cbv [TRACE_LET] in trace) in
      lazymatch trace' with
      | tnil => idtac
      | _ => liAStep; write_success_transactions_15158_to_nil
      end
  | |- context[WPasm] => liAStep; write_success_transactions_15158_to_nil
  | _ => first [liAStep; write_success_transactions_15158_to_nil | shelve]
  end.

Lemma write_success_transactions_15158_branches
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15b9c zesuEncoderBooleanCallSpec -∗
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  instr_body 0x1519c (writeSuccessTransactionsAt1519cSpec P) -∗
  instr_body 0x15158 (writeSuccessTransactionsAt15158Spec P).
Proof.
  move => *. iStartProof.
  iIntros "_ #Hlookup #Hcode #Hboolean #Houtput Hnext".
  iPoseProof "Hlookup" as "#Hlookup15158".
  iEval (rewrite /instr_lookup_resources) in "Hlookup15158".
  iPoseProof ("Hlookup15158" $! 0x15158 with "[]") as "#Hinstr15158".
  { iPureIntro.
    rewrite IslaTraces.write_success_blocks.Index.lookup_a15158.
    done. }
  iApply li_instr_pre.
  iEval (unfold li_tactic, normalize_instr_addr).
  iExists 0x15158.
  iSplit.
  { iPureIntro. reflexivity. }
  rewrite /find_in_context /FindInstrKind /=.
  iExists (IKInstr (Some IslaTraces.write_success_44.a15158.a15158)).
  iSplitL "".
  { iExact "Hinstr15158". }
  cbn. li_pm_reduce.
  iIntros "HPC".
  iEval (unfold writeSuccessTransactionsAt15158Spec) in "HPC".
  iDestruct "HPC" as
    "(%sp & %base & %transaction & %transactions & %processed & %remaining &
      %bytes & %prefix & %suffix & %tail & Hphase)".
  iEval (unfold WriteSuccessTransactionsSpec.writeSuccessTransactionPhaseHandoff)
    in "Hphase".
  iDestruct "Hphase" as
    "(Hmachine & Hprefix & Hsuffix & Hprocessed & Htransaction & Hremaining &
      Hmmio & Htrace & HP & Hinv & Hexit & _)".
  iEval (unfold writeSuccessTransactionsMachine15158) in "Hmachine".
  iDestruct "Hmachine" as
    "(Hsys & Hother & H1 & H2 & H5 & H8 & H9 & H10 & H11 & H18 & H19 & H20 &
      H21 & H22 & H23 & H24 & H25 & H26 & H27 & Hscratch & _)".
  write_success_transactions_15158_to_nil.
  all: liAStep.
  all: liAStep.
  all: li_pm_reduce.
  - have Hzero : WriteSuccessTransactionsSpec.writeSuccessTransactionByte
      transaction 285 = BV 8 0.
    { apply bv_zero_extend_64_zero_8. exact H1. }
    iPoseProof (write_success_transactions_optional_address_none P
      with "Hlookup Hcode Hboolean Hnext") as "Hnone".
    liInst (λ x, x.1ₗ = LET1).
    liARun.
    iExists (tail, suffix, prefix, bytes, remaining, processed, transactions,
      transaction, base, sp, tt)ₗ.
    iSplitL "".
    { iPureIntro. exact Hzero. }
    iEval (unfold WriteSuccessTransactionsSpec.writeSuccessTransactionPhaseHandoff,
      writeSuccessTransactionsMachine1515c).
    iFrame.
  - have Hnonzero : WriteSuccessTransactionsSpec.writeSuccessTransactionByte
      transaction 285 ≠ BV 8 0.
    { intro Hzero. apply H1. rewrite Hzero. bv_solve. }
    iPoseProof (write_success_transactions_chunk_15168_to_1519c P
      with "Hlookup Hcode Hboolean Houtput Hnext") as "Hsome15168".
    iPoseProof (write_success_transactions_chunk_1515c_to_15168 P
      with "Hlookup Hcode Hsome15168") as "Hsome1515c".
    liInst (λ x, x.1ₗ = LET).
    liARun.
    iExists (tail, suffix, prefix, bytes, remaining, processed, transactions,
      transaction, base, sp, tt)ₗ.
    iSplitL "".
    { iPureIntro. exact Hnonzero. }
    iEval (unfold WriteSuccessTransactionsSpec.writeSuccessTransactionPhaseHandoff,
      writeSuccessTransactionsMachine1515c).
    iFrame.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
Qed.
