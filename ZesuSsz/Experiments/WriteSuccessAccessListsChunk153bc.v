From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccessAccessListsSpec.
Require Import ZesuSsz.Experiments.WriteSuccessAccessListsTailBoundaries.

Import ListNotations.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Lemma write_success_access_lists_chunk_153bc
    `{!islaG Sigma} `{!threadG} (x19 : bv 64) (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x151d4 (writeSuccessAccessListsAt153bcSpec x19 P) -∗
  instr_body 0x153bc (writeSuccessAccessListsAt153bcSpec x19 P).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode #Hloop".
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
    (tail, x27, x22, x10, suffix, prefix, bytes, remaining, entries,
      entry, base, tt)ₗ.
  all: iFrame.
Qed.
