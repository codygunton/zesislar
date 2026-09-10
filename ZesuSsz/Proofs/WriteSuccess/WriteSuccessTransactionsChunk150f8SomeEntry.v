From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk150f0Spec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15bc8Some.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk150f8Jump.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Lemma write_success_transactions_chunk_150f8_some_entry
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  instr_pre 0x15bc8 (writeSuccessTransactionsAt15bc8SomeSpec P) -∗
  instr_body 0x150fc (writeSuccessTransactionsAt150fcFramedSpec P) -∗
  instr_body 0x150f8 (writeSuccessTransactionsAt150f8SomeSpec P).
Proof.
  iIntros "#Hlookup Hcall Hnext".
  rewrite instr_pre'_eq. iIntros "Hentry".
  iEval (rewrite -instr_pre'_eq) in "Hcall".
  iEval (rewrite -instr_pre'_eq) in "Hnext".
  iPoseProof (write_success_transactions_150f8_some_frame_pack P with
    "Hnext Hentry") as "Hpacked".
  iDestruct "Hpacked" as
    (chainId sp base transaction transactions processed remaining bytes prefix
      suffix tail) "(Hsys & H1 & Hframe)".
  iAssert (instr_pre 0x15bc8
      (reg_col zesu_ram_sys_regs ∗
       "x1" ↦ᵣ RVal_Bits (BV 64 0x150fc) ∗
       writeSuccessTransactions150f8SomeCallFrame P chainId sp base transaction
         transactions processed remaining bytes prefix suffix tail))
    with "[Hcall]" as "HfixedCall".
  { iApply (instr_pre_wand 0x15bc8 0x15bc8 true true with "Hcall");
      [done | done |].
    iIntros "(Hsys & H1 & Hframe)".
    rewrite /writeSuccessTransactionsAt15bc8SomeSpec.
    iExists chainId, sp, base, transaction, transactions, processed, remaining,
      bytes, prefix, suffix, tail.
    iFrame. }
  iPoseProof (write_success_transactions_chunk_150f8_jump
    (writeSuccessTransactions150f8SomeCallFrame P chainId sp base transaction
      transactions processed remaining bytes prefix suffix tail)
    with "Hlookup HfixedCall") as "Hbody".
  iEval (rewrite instr_pre'_eq) in "Hbody".
  iApply "Hbody". iFrame.
Qed.
