Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCalls.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk1558cBranch.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderBytesCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderIntCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderInt1645Call.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderU256.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBodyPrefixWitnessProvider.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBodyCompose.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsLoopEntryBody.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsLoopEntryExit.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Lemma write_success_transactions_loop_compose
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  writeSuccessTransactionsBodyPrefixWitness P -∗
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x101d4 zesuMemcpyCallSpec -∗
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  □ instr_pre 0x153d4 (writeSuccessBlobHashesLoopSpec P) -∗
  □ instr_pre 0x15590
    (writeSuccessTransactionsAuthorizationsAnyLoopSpec P) -∗
  □ instr_pre 0x15c6c zesuEncoderBytesCallSpec -∗
  □ instr_pre 0x15cb0 zesuEncoderU256CallSpec -∗
  □ instr_pre 0x15ce4 zesuEncoderInt1645CallSpec -∗
  □ instr_pre 0x15d10 zesuEncoderIntCallSpec -∗
  □ instr_pre 0x14f04 (writeSuccessTransactionsLoopSpec P) -∗
  instr_body 0x14f04 (writeSuccessTransactionsLoopSpec P).
Proof.
  iIntros "Hprefix #Hlookup #Hcode #Hmemcpy #Houtput #Hblob #Hauth #Hbytes
    #Hu256 #Hint128 #Hint64 #Hloop".
  iPoseProof (write_success_transactions_body_compose P with
    "Hprefix Hlookup Hcode Hmemcpy Houtput Hblob Hauth Hbytes Hu256 Hint128
      Hint64 Hloop") as "Hbody".
  liARun.
  - iApply (write_success_transactions_loop_entry_exit
      P sp base processed remaining tail H4 H12).
    rewrite /writeSuccessTransactionsLoopExitBranchFrame.
    iFrame.
    iAssumption.
  - have Hfacts : writeSuccessTransactionsLoopEntryFacts
        sp base processed remaining.
    { rewrite /writeSuccessTransactionsLoopEntryFacts.
      repeat split; assumption. }
    iPoseProof (write_success_transactions_loop_entry_body
      P sp base processed remaining tail Hfacts H12 with "[-]") as "Hentry".
    { rewrite /writeSuccessTransactionsLoopBodyBranchFrame.
      iFrame. iAssumption. }
    iEval (unfold
      WriteSuccessTransactionsBoundarySpec.writeSuccessTransactionsAt14f08Spec)
      in "Hentry".
    iDestruct "Hentry" as
      (sp' base' transaction transactions processed' remaining' bytes prefix
        suffix tail') "Hentry".
    iExists
      (tail', suffix, prefix, bytes, remaining', processed', transactions,
        transaction, base', sp', tt)ₗ.
    iExact "Hentry".
Unshelve.
all: prepare_sidecond.
all: try (f_equal; exact H12).
all: try (rewrite (write_success_transactions_loop_exit_remaining_nil
  processed remaining H4 H12); rewrite app_nil_r; reflexivity).
all: apply bv_eq; rewrite bv_and_unsigned !bv_unsigned_BV; exact H11.
Qed.
