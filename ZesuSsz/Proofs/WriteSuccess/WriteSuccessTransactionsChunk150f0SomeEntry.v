From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import
  Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderOptionalU64Call.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk150f0Spec.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.
Local Opaque
  WriteSuccessTransactionsSpec.writeSuccessTransactionPhaseEvents.
#[local] Typeclasses Opaque writeSuccessTransactions150f0Frame.

#[local] Hint Extern 7
  (FindInContext (FindInstrKind ?address ?later) FICSyntactic) =>
  let reduced := eval vm_compute in address in
  first [ constr_eq address reduced; fail 1
        | change (FindInContext (FindInstrKind reduced later) FICSyntactic);
          typeclasses eauto ] : typeclass_instances.

Lemma write_success_transactions_chunk_150f0_some_entry_block
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (chainId sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x150f8 (writeSuccessTransactionsAt150f8SomeBlock P chainId sp
    base transaction transactions processed remaining bytes prefix suffix tail) -∗
  instr_body 0x150f0 (writeSuccessTransactionsAt150f0SomeBlock P chainId sp
    base transaction transactions processed remaining bytes prefix suffix tail).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode Hnext".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
Qed.

Lemma write_success_transactions_chunk_150f0_some_entry
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x150f8 (writeSuccessTransactionsAt150f8SomeSpec P) -∗
  instr_body 0x150f0 (writeSuccessTransactionsAt150f0SomeSpec P).
Proof.
  iStartProof. iIntros "#Hlookup #Hcode Hnext".
  rewrite instr_pre'_eq. iIntros "Hentry".
  rewrite /writeSuccessTransactionsAt150f0SomeSpec.
  iDestruct "Hentry" as
    (chainId sp base transaction transactions processed remaining bytes prefix
      suffix tail) "Hentry".
  iEval (rewrite -instr_pre'_eq) in "Hnext".
  iPoseProof (instr_pre_wand 0x150f8 0x150f8 false false
    (writeSuccessTransactionsAt150f8SomeSpec P)
    (writeSuccessTransactionsAt150f8SomeBlock P chainId sp base transaction
      transactions processed remaining bytes prefix suffix tail)
    with "Hnext") as "HnextBlock"; [done | done | idtac].
  iSpecialize ("HnextBlock" with "[]").
  { iIntros "Hblock".
    rewrite /writeSuccessTransactionsAt150f8SomeSpec.
    iExists chainId, sp, base, transaction, transactions, processed, remaining,
      bytes, prefix, suffix, tail.
    iExact "Hblock". }
  iPoseProof (write_success_transactions_chunk_150f0_some_entry_block P
    chainId sp base transaction transactions processed remaining bytes prefix
    suffix tail with "Hlookup Hcode HnextBlock") as "Hbody".
  iEval (rewrite instr_pre'_eq) in "Hbody".
  iApply ("Hbody" with "Hentry").
Qed.
