Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import
  Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCallAbi.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderOptionalU64Call.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrier10190Call.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrier150f8Branch.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrier150f8CallFrame.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrier150f8Scratch.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrier150fcAbi.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierChunk150f0Entry.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

#[local] Hint Extern 7
  (FindInContext (FindInstrKind ?address ?later) FICSyntactic) =>
  let reduced := eval vm_compute in address in
  first [ constr_eq address reduced; fail 1
        | change (FindInContext (FindInstrKind reduced later) FICSyntactic);
          typeclasses eauto ] : typeclass_instances.

Lemma write_success_transactions_carrier_150f8_some_call
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15bc8 zesuEncoderOptionalU64SomeCallSpec -∗
  instr_body 0x150fc (writeSuccessTransactionsAt150fcCarrierAbiSpec P) -∗
  instr_body 0x150f8 (writeSuccessTransactionsAt150f8CarrierSomeSpec P).
Proof.
  iStartProof.
  iIntros "#Hlookup #Hcode Hoptional Hnext".
  iEval (rewrite /instr_lookup_resources) in "Hlookup".
  iPoseProof ("Hlookup" $! 0x150f8 with "[]") as "#Hinstr150f8".
  { iPureIntro.
    rewrite IslaTraces.write_success_blocks.Index.lookup_a150f8. done. }
  iPoseProof (IslaTraces.write_success_35.a150f8_spec.a150f8_spec
    0x150f8 with "Hinstr150f8") as "Hjalr".
  rewrite instr_pre'_eq. iIntros "Hentry".
  iEval (rewrite -instr_pre'_eq) in "Hoptional Hnext".
  iEval (unfold writeSuccessTransactionsAt150f8CarrierSomeSpec) in "Hentry".
  iDestruct "Hentry" as
    (chainId sp base transaction transactions processed remaining bytes prefix
      suffix tail first second third fourth items)
    "(%Hchain & #HtagNonzero & Hentry)".
  iDestruct "HtagNonzero" as %HtagNonzero.
  iEval (unfold writeSuccessTransactionsAt150f8CarrierCallBlockFixed) in "Hentry".
  iDestruct "Hentry" as "(Hmachine & Hmmio & Htrace & Hframe & _)".
  iEval (unfold writeSuccessTransactionsMachine150f8CarrierCall) in "Hmachine".
  iDestruct "Hmachine" as
    "(Hsys & Hother & H11 & Hsaved & H1 & H2 & H10 & _)".
  iPoseProof (write_success_transactions_carrier_150ec_call_frame_facts P sp
    base transaction transactions processed remaining bytes prefix suffix tail
    first second third fourth items with "Hframe") as
    "(Hframe & %HspAlign & %HspMin & %HspMax)".
  iPoseProof (write_success_transactions_150f8_carrier_call_frame_enter P sp
    base transaction transactions processed remaining bytes prefix suffix tail
    first second third fourth items with "Hframe") as
    "(Hframe & Hstack & Hvalue & HtagWord & %Hlength & %HstackLower &
      %HstackUpper)".
  iPoseProof (write_success_transactions_150f8_carrier_tag_split sp transaction
    with "[] HtagWord") as "HtagParts".
  { iPureIntro. exact Hlength. }
  iDestruct "HtagParts" as
    (tagTail) "(Htag & HtagTail & %HtagShape)".
  iPoseProof (write_success_transactions_150fc_carrier_abi_continuation P sp
    base transaction transactions processed remaining bytes prefix suffix tail
    first second third fourth items tagTail with
    "Hnext Hframe HtagTail []") as "Hret".
  { iPureIntro. exact HtagShape. }
  iApply "Hjalr".
  rewrite /InstrSpecs.Specs.zesu_jalr_same_spec.
  iExists (BV 64 0x160f4).
  iFrame "Hsys H1".
  iSplit; first (iPureIntro; bv_solve).
  have Htarget :
      bv_unsigned
        (bv_or (bv_and ((BV 64 0x160f4) + BV 64 18446744073709550292)%bv
          (BV 64 18446744073709551614)) (BV 64 0)) = 0x15bc8
    by bv_solve.
  rewrite Htarget.
  iApply (instr_pre_wand 0x15bc8 0x15bc8 true true with "Hoptional");
    [done | done |].
  iIntros "Hcallee".
  iEval (unfold zesuEncoderOptionalU64SomeCallSpec, zesu_c_call).
  iExists sp, (BV 64 0x150fc).
  iDestruct "Hcallee" as "(HsysEntry & H1Entry & _)".
  iFrame "HsysEntry".
  iEval (rewrite !reg_col_cons reg_col_nil) in "Hother Hsaved".
  iDestruct "Hother" as
    "(H12 & H13 & H14 & H15 & H16 & H17 & H5 & H6 & H7 & H28 & H29 &
      H30 & H31 & _)".
  iDestruct "Hsaved" as
    "(H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 &
      H27 & _)".
  iDestruct "H8" as (v8) "(%Hv8 & H8)"; cbn in Hv8; subst v8.
  iDestruct "H9" as (v9) "(%Hv9 & H9)"; cbn in Hv9; subst v9.
  iDestruct "H18" as (v18) "(%Hv18 & H18)"; cbn in Hv18; subst v18.
  iDestruct "H19" as (v19) "(%Hv19 & H19)"; cbn in Hv19; subst v19.
  iDestruct "H20" as (v20) "(%Hv20 & H20)"; cbn in Hv20; subst v20.
  iDestruct "H21" as (v21) "(%Hv21 & H21)"; cbn in Hv21; subst v21.
  iDestruct "H22" as (v22) "(%Hv22 & H22)"; cbn in Hv22; subst v22.
  iDestruct "H23" as (v23) "(%Hv23 & H23)"; cbn in Hv23; subst v23.
  iDestruct "H24" as (v24) "(%Hv24 & H24)"; cbn in Hv24; subst v24.
  iDestruct "H25" as (v25) "(%Hv25 & H25)"; cbn in Hv25; subst v25.
  iDestruct "H26" as (v26) "(%Hv26 & H26)"; cbn in Hv26; subst v26.
  iDestruct "H27" as (v27) "(%Hv27 & H27)"; cbn in Hv27; subst v27.
  iEval (rewrite reg_col_cons reg_col_nil) in "H11".
  iDestruct "H11" as "(H11 & _)".
  iDestruct "H11" as (r11 Hr11) "H11".
  iDestruct "H12" as (r12 Hr12) "H12".
  iDestruct "H13" as (r13 Hr13) "H13".
  iDestruct "H14" as (r14 Hr14) "H14".
  iDestruct "H15" as (r15 Hr15) "H15".
  iDestruct "H16" as (r16 Hr16) "H16".
  iDestruct "H17" as (r17 Hr17) "H17".
  apply valu_has_bits_shape in Hr11 as (b11 & ->).
  apply valu_has_bits_shape in Hr12 as (b12 & ->).
  apply valu_has_bits_shape in Hr13 as (b13 & ->).
  apply valu_has_bits_shape in Hr14 as (b14 & ->).
  apply valu_has_bits_shape in Hr15 as (b15 & ->).
  apply valu_has_bits_shape in Hr16 as (b16 & ->).
  apply valu_has_bits_shape in Hr17 as (b17 & ->).
  iFrame "H5 H6 H7 H28 H29 H30 H31".
  iEval (simpl).
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def).
  iApply bi.emp_sep_1.
  iExists (RVal_Bits (sp + BV 64 1664)%bv).
  iFrame "H10". iExists (sp + BV 64 1664)%bv. iSplit; first done.
  iExists (RVal_Bits b11). iFrame "H11". iExists b11. iSplit; first done.
  iExists (RVal_Bits b12). iFrame "H12". iExists b12. iSplit; first done.
  iExists (RVal_Bits b13). iFrame "H13". iExists b13. iSplit; first done.
  iExists (RVal_Bits b14). iFrame "H14". iExists b14. iSplit; first done.
  iExists (RVal_Bits b15). iFrame "H15". iExists b15. iSplit; first done.
  iExists (RVal_Bits b16). iFrame "H16". iExists b16. iSplit; first done.
  iExists (RVal_Bits b17). iFrame "H17". iExists b17. iSplit; first done.
  iExists (RVal_Bits (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 192)).
  iFrame "H8". iSplit; first (iPureIntro; cbn; done).
  iExists (RVal_Bits (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 16)).
  iFrame "H9". iSplit; first (iPureIntro; cbn; done).
  iExists (RVal_Bits (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 48)).
  iFrame "H18". iSplit; first (iPureIntro; cbn; done).
  iExists (RVal_Bits (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 224)).
  iFrame "H19". iSplit; first (iPureIntro; cbn; done).
  iExists (RVal_Bits (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 56)).
  iFrame "H20". iSplit; first (iPureIntro; cbn; done).
  iExists (RVal_Bits (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 72)).
  iFrame "H21". iSplit; first (iPureIntro; cbn; done).
  iExists (RVal_Bits (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 200)).
  iFrame "H22". iSplit; first (iPureIntro; cbn; done).
  iExists (RVal_Bits (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 24)).
  iFrame "H23". iSplit; first (iPureIntro; cbn; done).
  iExists (RVal_Bits (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 8)).
  iFrame "H24". iSplit; first (iPureIntro; cbn; done).
  iExists (RVal_Bits (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 0)).
  iFrame "H25". iSplit; first (iPureIntro; cbn; done).
  iExists (RVal_Bits (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 184)).
  iFrame "H26". iSplit; first (iPureIntro; cbn; done).
  iExists (RVal_Bits
    (bv_zero_extend 64 (WriteSuccessTransactionsSpec.writeSuccessTransactionByte transaction 32))).
  iFrame "H27". iSplit; first (iPureIntro; cbn; done).
  iAssert ("x1" ↦ᵣ RVal_Bits (BV 64 0x150fc))%I
    with "[H1Entry]" as "H1target".
  { replace (BV 64 0x150fc) with (Z_to_bv 64 (86264 + 4))
      by bv_solve; iExact "H1Entry". }
  iFrame "H1target H2".
  iSplit; first (iPureIntro; exact HspAlign).
  iSplit; first (iPureIntro; bv_solve).
  iSplit; first (iPureIntro; bv_solve).
  iSplit; first (iPureIntro; bv_solve).
  iSplit; first (iPureIntro; split; lia).
  iEval (rewrite /writeSuccessTransactionPhaseEvents Hchain
    /writeSuccessOptionalU64Events) in "Htrace".
  have HtraceAddr :
      (sp - BV 64 16 - BV 64 16 + BV 64 7)%bv = (sp - BV 64 25)%bv
    by bv_solve.
  iEval (rewrite <- HtraceAddr) in "Htrace".
  iAssert (spec_trace
      (writeOutputEvents (sp - BV 64 16 - BV 64 16 + BV 64 7)%bv (BV 64 1)
        (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
          (writeSuccessTransactionPhaseEvents TransactionNonce sp transaction
            (writeSuccessTransactionsEvents sp remaining
              (WriteSuccessTransactionsCarrierCall150ec.writeSuccessTransactionsCarrierOutputTail sp items tail))))))%I
    with "[Htrace]" as "HtracePrefix".
  { iApply (spec_trace_mono _ _); [spec_solver | iExact "Htrace"]. }
  have HvalueAddr : bv_unsigned (sp + BV 64 1664)%bv = bv_unsigned sp + 1664
    by bv_solve.
  have HtagAddr : bv_unsigned (sp + BV 64 1664)%bv + 8 =
      bv_unsigned sp + 1672 by bv_solve.
  iEval (rewrite <- HvalueAddr) in "Hvalue".
  iEval (rewrite <- HtagAddr) in "Htag".
  iEval (rewrite <- HvalueAddr) in "Hret".
  iEval (rewrite <- HtagAddr) in "Hret".
  iFrame "Hstack".
  iExists (writeSuccessTransactionWord transaction 160),
    (writeSuccessTransactionByte transaction 168),
    (writeSuccessTransactionPhaseEvents TransactionNonce sp transaction
      (writeSuccessTransactionsEvents sp remaining
        (WriteSuccessTransactionsCarrierCall150ec.writeSuccessTransactionsCarrierOutputTail
          sp items tail))).
  iFrame "Hvalue Htag Hmmio HtracePrefix".
  iSplit; first (iPureIntro; exact HtagNonzero).
  iSplit; first (iPureIntro; bv_simplify_arith HspAlign; bv_solve).
  iSplit; first (iPureIntro; lia).
  iSplit; first (iPureIntro; rewrite HvalueAddr; lia).
  iExact "Hret".
  Unshelve. all: try prepare_sidecond; try bv_solve; try lia; try iFrame.
Qed.
