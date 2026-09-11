Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsTailBoundaries.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.
#[local] Typeclasses Opaque writeSuccessAccessListsTailFrame.

Lemma write_success_access_lists_chunk_153b8
    `{!islaG Sigma} `{!threadG} (x19 : bv 64) (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x153bc (writeSuccessAccessListsAt153bcSpec x19 P) -∗
  instr_body 0x153b8 (writeSuccessAccessListsAt153b8Spec x19 P).
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
  Unshelve. all: try exact inhabitant.
  all: iExists
    (tail, x27, x22, x10, savedX22, suffix, prefix, bytes, remaining, entries,
      entry, base, tt)ₗ.
  all: iFrame.
Qed.
