From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeCore.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeFrameBounds.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeNoneBoundary.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeSomeBoundary.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeSomeEvents.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Lemma write_success_transactions_priority_fee_some_setup_15124
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x15124
    (writeSuccessTransactionsPriorityFeeSomeAt15124Spec P) -∗
  instr_body 0x1511c
    (writeSuccessTransactionsPriorityFeeSomeCoreSpec P).
Proof.
  move => *. iStartProof.
  iIntros "_ #Hlookup #Hcode Hnext".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve.
  iExists (tail, suffix, prefix, bytes, remaining, processed,
    transactions, base, tt)ₗ.
  cbn.
  rewrite /writeSuccessTransactionsPriorityFeeSomeBooleanEvents
    /writeSuccessTransactionsPriorityFeeSomeBooleanTail.
  iSplit; first done.
  iRename select (writeSuccessTransactionsPriorityFeeFrame P sp base
    transaction transactions processed remaining bytes prefix suffix tail)%I
    into "Hframe".
  iPoseProof (write_success_transactions_priority_fee_frame_bounds P sp base
    transaction transactions processed remaining bytes prefix suffix tail
    with "Hframe") as "(Hframe & %Halign & %HlowerBound & %HupperBound)".
  rewrite /writeSuccessTransactionsPriorityFeeCallerFrame
    /writeSuccessTransactionsPriorityFeeMachineCallerFrame
    /writeSuccessTransactionsPriorityFeeFrame.
  iFrame.
  iDestruct select ((∃ vact : valu,
      ⌜valu_has_shape vact (BitsShape 64)⌝ ∗ "x3" ↦ᵣ vact) ∗
    (∃ vact : valu,
      ⌜valu_has_shape vact (BitsShape 64)⌝ ∗ "x4" ↦ᵣ vact) ∗ emp)%I
    as "Hregs".
  iDestruct select ((bv_unsigned sp - 48) ↦ₘ? 32)%I as "Hlower".
  iDestruct select ((bv_unsigned sp - 16 + 16) ↦ₘ? 104)%I as "Hupper".
  iSplitL "Hregs Hlower Hupper".
  { iSplitL "Hregs".
    { rewrite !reg_col_cons reg_col_nil. iFrame. }
    iIntros "Hstack".
    iAssert ((bv_unsigned sp - 48) ↦ₘ? 48)%I
      with "[Hlower Hstack]" as "Hlower48".
    { iApply (mem_mapsto_uninit_combine 32 with "Hlower"); first lia.
      have -> : bv_unsigned sp - 48 + 32 = bv_unsigned sp - 16 by lia.
      iExact "Hstack". }
    iApply (mem_mapsto_uninit_combine 48 with "Hlower48"); first lia.
    have -> : bv_unsigned sp - 48 + 48 = bv_unsigned sp by lia.
    have -> : bv_unsigned sp - 16 + 16 = bv_unsigned sp by lia.
    iExact "Hupper". }
  iSplit; first (iPureIntro; exact Halign).
  iSplit; first (iPureIntro; exact HlowerBound).
  iSplit; first (iPureIntro; exact HupperBound).
  done.
Qed.
