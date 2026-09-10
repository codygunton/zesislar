From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccessCallAbi.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderU256.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary1519c.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsChunk1519cAdapter.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Remove Hints find_body_a151a4_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Lemma write_success_transactions_chunk_1519c_to_151a0
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x151a0 (writeSuccessTransactionsAt151a0Spec P) -∗
  instr_body 0x1519c (writeSuccessTransactionsAt1519cSpec P).
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
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve.
  all: repeat iIntros "?"; liARun.
  all: iRename select (base ↦ₘ∗ prefix ∗ _)%I into "Hphase".
  all: iDestruct "Hphase" as
    "(Hprefix & Hsuffix & Hprocessed & Htransaction & Hremaining & Hmmio &
      Htrace & HP & Hinv & Hexit & _)".
  all: iPoseProof "Hinv" as "#HinvKeep".
  all: iPoseProof "HinvKeep" as "#HinvCopy".
  all: iEval
    (unfold WriteSuccessTransactionsSpec.writeSuccessTransactionsInvariant)
    in "HinvCopy".
  all: iDestruct "HinvCopy" as
    "(_ & _ & _ & _ & _ & _ & _ & _ & _ & %Halign & %Hmin & %Hmax & _)".
  all: iRename select ("x5" ↦ᵣ _)%I into "Hx5".
  all: iRename select ("x10" ↦ᵣ _)%I into "Hx10".
  all: unLET.
  all: iApply (write_success_transactions_chunk_1519c_adapter
    P sp base transaction transactions processed remaining bytes prefix suffix tail
    Halign Hmin Hmax).
  all: iEval (unfold
    WriteSuccessTransactionsSpec.writeSuccessTransactionPhaseHandoff).
  all: iSplitR
    "Hprefix Hsuffix Hprocessed Htransaction Hremaining Hmmio Htrace HP HinvKeep Hexit".
  - all: iEval (unfold writeSuccessTransactionsMachine151a0).
    all: iEval (unfold writeSuccessTransactionsMachine1519c).
    all: iEval (rewrite ->@bv_add_0_r by done) in "Hx10".
    all: rewrite /reg_col; cbn; iFrame.
    all: repeat iSplit; try (iPureIntro; cbn; done).
    all: try (iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def);
      iExists (RVal_Bits b); iFrame "Hx5"; iPureIntro; cbn; reflexivity).
  - all: iFrame.
  Unshelve.
  all: try assumption.
  all: try bv_solve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  Unshelve.
  all: iExact "HinvKeep".
Qed.
