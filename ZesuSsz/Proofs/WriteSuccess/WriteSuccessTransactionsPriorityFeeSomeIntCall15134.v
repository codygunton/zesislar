Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderInt1645Call.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeCore.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeFrameBounds32.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeSomeBoundary.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeSomeEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary150e8.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary150f0.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15148.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Lemma write_success_transactions_priority_fee_some_int_call_15134
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15ce4 zesuEncoderInt1645CallSpec -∗
  instr_body 0x15148 (writeSuccessTransactionsPriorityFeePostSpec P) -∗
  instr_body 0x15128
    (writeSuccessTransactionsPriorityFeeSomeAt15128Spec P).
Proof.
  move => *. iStartProof.
  iIntros "_ #Hlookup #Hcode #Hint Hnext".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  liARun.
  Unshelve. all: try prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve.
  iRename select
    ("x8" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 192))%I
    into "H8saved".
  iRename select
    ("x9" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 16))%I
    into "H9saved".
  iRename select
    ("x18" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 48))%I
    into "H18saved".
  iRename select
    ("x19" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 224))%I
    into "H19saved".
  iRename select
    ("x20" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 56))%I
    into "H20saved".
  iRename select
    ("x21" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 72))%I
    into "H21saved".
  iRename select
    ("x22" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 200))%I
    into "H22saved".
  iRename select
    ("x23" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 24))%I
    into "H23saved".
  iRename select
    ("x24" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 8))%I
    into "H24saved".
  iRename select
    ("x25" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 0))%I
    into "H25saved".
  iRename select
    ("x26" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 184))%I
    into "H26saved".
  iRename select
    ("x27" ↦ᵣ RVal_Bits
      (bv_zero_extend 64 (writeSuccessTransactionByte transaction 32)))%I
    into "H27saved".
  iRename select (writeSuccessTransactionsPriorityFeeFrame P sp base
    transaction transactions processed remaining bytes prefix suffix tail)%I
    into "Hframe".
  iPoseProof (write_success_transactions_priority_fee_frame_bounds_32 P sp base
    transaction transactions processed remaining bytes prefix suffix tail
    with "Hframe") as "(Hframe & %Halign & %Hlower & %Hupper)".
  iExists
    (writeSuccessTransactionPhaseEvents TransactionGasLimit sp transaction
      (writeSuccessTransactionsEvents sp remaining tail), tt)ₗ.
  cbn. rewrite /writeSuccessTransactionsPriorityFeeSomeBooleanTail.
  iSplit; first done.
  iSplit; first (iPureIntro; exact Halign).
  iSplit; first (iPureIntro; exact Hlower).
  iSplit; first (iPureIntro; exact Hupper).
  iSplit; first (iPureIntro; bv_solve).
  iSplit; first (iPureIntro; bv_solve).
  iSplit; first (iPureIntro; bv_solve).
  iSplit; first (iPureIntro; bv_solve).
  iSplit; last done.
  iApply instr_pre_to_body. iNext.
  liARun.
  Unshelve. all: try prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve.
  iRename select ("rv_enable_pmp" ↦ᵣ _)%I into "Hs0".
  iRename select ("rv_enable_misaligned_access" ↦ᵣ _)%I into "Hs1".
  iRename select ("rv_ram_base" ↦ᵣ _)%I into "Hs2".
  iRename select ("rv_ram_size" ↦ᵣ _)%I into "Hs3".
  iRename select ("rv_rom_base" ↦ᵣ _)%I into "Hs4".
  iRename select ("rv_rom_size" ↦ᵣ _)%I into "Hs5".
  iRename select ("rv_clint_base" ↦ᵣ _)%I into "Hs6".
  iRename select ("rv_clint_size" ↦ᵣ _)%I into "Hs7".
  iRename select ("rv_htif_tohost" ↦ᵣ _)%I into "Hs8".
  iRename select ("cur_privilege" ↦ᵣ _)%I into "Hs9".
  iRename select ("misa" ↦ᵣ _)%I into "Hs10".
  iRename select ("mtvec" ↦ᵣ _)%I into "Hs11".
  iRename select ("mstatus" ↦ᵣ _)%I into "Hs12".
  iRename select ("satp" ↦ᵣ _)%I into "Hs13".
  iAssert (reg_col zesu_ram_sys_regs)%I
    with "[Hs0 Hs1 Hs2 Hs3 Hs4 Hs5 Hs6 Hs7 Hs8 Hs9 Hs10 Hs11 Hs12 Hs13]"
    as "Hsys".
  { rewrite !reg_col_cons reg_col_nil. iFrame.
    repeat iSplit; iPureIntro; done. }
  liARun.
  Unshelve. all: try prepare_sidecond; try assumption; try bv_solve; try lia;
    try iFrame.
  Unshelve.
  iRename select ("x1" ↦ᵣ _)%I into "H1".
  iRename select ("x2" ↦ᵣ _)%I into "H2".
  iRename select ("x5" ↦ᵣ _)%I into "H5".
  iRename select ("x10" ↦ᵣ _)%I into "H10".
  iRename select ("x11" ↦ᵣ _)%I into "H11".
  iRename select ((bv_unsigned sp - 32) ↦ₘ? 32)%I into "Hstack".
  iRename select ((bv_unsigned sp - 48) ↦ₘ? 16)%I into "HscratchLow".
  iRename select ((bv_unsigned sp - 32 + 32) ↦ₘ? 104)%I
    into "HscratchHigh".
  have HhighAddress : bv_unsigned sp - 32 + 32 = bv_unsigned sp by lia.
  iEval (rewrite HhighAddress) in "HscratchHigh".
  iAssert ((bv_unsigned sp - 48) ↦ₘ? 48)%I
    with "[HscratchLow Hstack]" as "HscratchLow48".
  { iApply (mem_mapsto_uninit_combine 16 with "HscratchLow"); first lia.
    have -> : bv_unsigned sp - 48 + 16 = bv_unsigned sp - 32 by lia.
    iExact "Hstack". }
  iAssert ((bv_unsigned sp - 48) ↦ₘ? 152)%I
    with "[HscratchLow48 HscratchHigh]" as "Hscratch".
  { iApply (mem_mapsto_uninit_combine 48 with "HscratchLow48"); first lia.
    have -> : bv_unsigned sp - 48 + 48 = bv_unsigned sp by lia.
    iExact "HscratchHigh". }
  iDestruct select (_ ∗ _)%I as "Hother".
  iRename select (reg_col zesu_ram_sys_regs)%I into "HsysFinal".
  iRename select (spec_trace _)%I into "HtraceFinal".
  iRename select (mmio_range (604086456 + 8) 16)%I into "HmmioFinal".
  iAssert (writeSuccessTransactionsMachine15148
      sp base transactions processed transaction)%I
    with "[-Hframe HmmioFinal HtraceFinal]" as "Hmachine".
  { rewrite /writeSuccessTransactionsMachine15148
      /writeSuccessTransactionsMachine150f0.
    iSplitL "HsysFinal"; first iExact "HsysFinal".
    iEval (rewrite /reg_col /=) in "Hother".
    iDestruct "Hother" as
      "(H3 & H4 & H6 & H7 & H12 & H13 & H14 & H15 & H16 & H17 & H28 & H29 & H30 & H31 & _)".
    iAssert (reg_col writeSuccessTransactions150f0OtherRegShapes)%I
      with "[H1 H3 H4 H5 H6 H7 H10 H11 H12 H13 H14 H15 H16 H17 H28 H29 H30 H31]"
      as "Hregs".
    { rewrite /writeSuccessTransactions150f0OtherRegShapes
        /writeSuccessTransactions150f0OtherRegisters /reg_col /=.
      iFrame.
      repeat iSplit; iPureIntro; done. }
    iSplitL "Hregs"; first iExact "Hregs".
    iSplitL "H2"; first iExact "H2".
    iFrame "H8saved H9saved H18saved H19saved H20saved H21saved H22saved
      H23saved H24saved H25saved H26saved H27saved".
    rewrite /writeSuccessTransactionsScratch150e8.
    iFrame "Hscratch".
    iFrame. }
  iExists (tail, suffix, prefix, bytes, remaining, processed, transactions,
    transaction, base, sp, tt)ₗ.
  cbn.
  iFrame "Hmachine Hframe HmmioFinal HtraceFinal".
Qed.
