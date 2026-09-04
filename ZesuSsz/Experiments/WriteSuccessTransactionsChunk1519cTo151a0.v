From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccessCallAbi.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderU256.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary1519c.

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
  all: iRename select ("x5" ↦ᵣ _)%I into "Hx5".
  all: iRename select ("x10" ↦ᵣ _)%I into "Hx10".
  all: unLET;
    iExists (tail, suffix, prefix, bytes, remaining, processed, transactions,
      transaction, base, sp, tt)ₗ;
    iEval (unfold writeSuccessTransactionsMachine151a0);
    iEval (unfold writeSuccessTransactionsMachine1519c);
    rewrite /reg_col;
    cbn;
    iFrame;
    iSplitL "Hx5".
    - iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def).
      iExists (RVal_Bits b). iFrame "Hx5". iPureIntro. cbn. reflexivity.
    - iEval (cbn) in "Hx10".
      set v :=
        WriteSuccessTransactionsSpec.writeSuccessTransactionWord
          transaction 48.
      have -> : (v + 0)%bv = v.
      { apply (bv_add_0_r v (bv_0 64)). apply bv_0_unsigned. }
      iFrame.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
Qed.
