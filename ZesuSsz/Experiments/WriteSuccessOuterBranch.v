From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import InstrSpecs.Lookup.
Require Import ZesuSsz.Experiments.WriteSuccessValueBlock.

Local Instance : LithiumUnfold (@writeSuccessValuePost) := I.

Definition writeSuccessOuterEmptySpec `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (values : list (bv 64)) (payload : list (bv 8))
      (tail : spec),
    writeSuccessValuePost sp values payload tail P ∗
    ⌜default (BV 64 0) (values !! 8%nat) = BV 64 0⌝ ∗
    instr_pre 0x15668 (writeSuccessValuePost sp values payload tail P) ∗
    True)%I.

Global Instance : LithiumUnfold (@writeSuccessOuterEmptySpec) := I.

Lemma write_success_outer_empty_branch `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  instr_body 0x14f04 (writeSuccessOuterEmptySpec P).
Proof.
  move => *.
  iStartProof. iIntros "_ #Hcode".
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try congruence.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve.
  all: try congruence.
  all: try iFrame.
Qed.
