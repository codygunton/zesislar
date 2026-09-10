From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import
  Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary14f1c.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary15100.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsChunk150fcLoadSpec.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.
Local Opaque WriteSuccessTransactionsSpec.writeSuccessTransactionOwn.

Lemma write_success_transactions_chunk_150fc_load_core
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x15100 (writeSuccessTransactions15100LoadPost P sp base
    transaction transactions processed remaining bytes prefix suffix tail) -∗
  instr_body 0x150fc (writeSuccessTransactions150fcLoadEntry P sp base
    transaction transactions processed remaining bytes prefix suffix tail).
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
  Unshelve.
  all: repeat iIntros "?".
  all: iRename select (writeSuccessTransactionOwn transaction) into
    "HtransactionOwn".
  all: iDestruct select (_ ∗ _)%I as
    "(Hremaining & Hmmio & Htrace & HP & Hinvariant & Hexit & _)".
  all: iPoseProof "Hinvariant" as "#HinvariantCopy".
  all: iDestruct "HinvariantCopy" as
    "(_ & _ & _ & _ & _ & _ & _ & _ & _ & %Halign & %Hmin & %Hmax & _)".
  all: have Halign8 := write_success_transactions_stack_aligned_8 sp Halign.
  all: have Hmin272 : 0x20000000 <= bv_unsigned sp + 272 by lia.
  all: have Hmax272 : bv_unsigned sp + 272 < 0x40000000 by lia.
  all: liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
Qed.
