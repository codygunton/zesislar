Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index HintsTransactionsLoop.
From IslaTraces.write_success_48 Require Import a15198_spec.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCallAbi.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderBooleanCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsOptionalAddressNone15198Adapter.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary150e8.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary1519c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsOptionalAddressNone15198Boundary.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Lemma write_success_transactions_optional_address_none_15198
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15b9c zesuEncoderBooleanCallSpec -∗
  instr_body 0x1519c (writeSuccessTransactionsAt1519cSpec P) -∗
  instr_body 0x15198
    (writeSuccessTransactionsOptionalAddressNoneAt15198Spec P).
Proof.
  move => *. iStartProof.
  iIntros "_ #Hlookup #Hcode #Hboolean Hnext".
  iPoseProof "Hlookup" as "#Hlookup15198".
  iEval (rewrite /instr_lookup_resources) in "Hlookup15198".
  iPoseProof ("Hlookup15198" $! 0x15198 with "[]") as "#Hinstr15198".
  { iPureIntro.
    rewrite IslaTraces.write_success_blocks.Index.lookup_a15198.
    done. }
  iPoseProof (a15198_spec 0x15198 with "Hinstr15198") as "Hbody15198".
  iAssert (□ (True -∗ instr_pre 0x15b9c zesuEncoderBooleanCallSpec))%I
    with "[]" as "#HbooleanHidden".
  { iModIntro. iIntros "_". iExact "Hboolean". }
  iClear "Hboolean Hlookup15198".
  iEval (rewrite instr_pre'_eq) in "Hbody15198".
  rewrite instr_pre'_eq. iIntros "Hsetup".
  iEval (unfold writeSuccessTransactionsOptionalAddressNoneAt15198Spec)
    in "Hsetup".
  iDestruct "Hsetup" as
    "(%sp & %base & %transaction & %transactions & %processed & %remaining &
      %bytes & %prefix & %suffix & %tail & %Hzero & Hphase)".
  iEval (unfold writeSuccessTransactionPhaseHandoff) in "Hphase".
  iDestruct "Hphase" as
    "(Hmachine & Hprefix & Hsuffix & Hprocessed & Htransaction & Hremaining &
      Hmmio & Htrace & HP & Hinv & Hexit & _)".
  iEval (unfold writeSuccessTransactionsMachine15198) in "Hmachine".
  iDestruct "Hmachine" as
    "(Hsys & Hother & H1 & H2 & H5 & H8 & H9 & H10 & H11 & H18 & H19 & H20 &
      H21 & H22 & H23 & H24 & H25 & H26 & H27 & Hscratch & _)".
  iApply "Hbody15198".
  rewrite /InstrSpecs.Specs.zesu_jalr_same_spec.
  iExists (BV 64 0x16194). iFrame "Hsys H1".
  iSplit; first (iPureIntro; bv_solve).
  have Htarget :
    bv_unsigned
      (bv_or (bv_and ((BV 64 0x16194) + BV 64 18446744073709550088)%bv
        (BV 64 18446744073709551614)) (BV 64 0)) = 0x15b9c
    by bv_solve.
  rewrite Htarget.
  iSpecialize ("HbooleanHidden" with "[]"). { done. }
  iDestruct (bi.intuitionistically_elim with "HbooleanHidden") as "HbooleanReady".
  iEval (rewrite -instr_pre'_eq) in "HbooleanReady".
  iEval (rewrite -instr_pre'_eq) in "Hnext".
  iApply (instr_pre_wand 0x15b9c 0x15b9c true true with "HbooleanReady");
    [done | reflexivity |].
  iIntros "(Hsys & H1 & _)".
  iEval (unfold writeSuccessTransactionOwn) in "Htransaction".
  iDestruct "Htransaction" as
    "(Hdata & Haccess & Hentries & Hblob & Hauth & %Hvalid & _)".
  have Hto : writeSuccessTransactionTo transaction = None.
  { destruct (writeSuccessTransactionTo transaction) as [address|] eqn:Hto.
    - unfold writeSuccessTransactionValid in Hvalid.
      rewrite Hto in Hvalid. naive_solver.
    - done. }
  iEval (unfold writeSuccessTransactionPhaseEvents,
    writeSuccessOptionalAddressEvents; rewrite Hto) in "Htrace".
  iAssert (writeSuccessTransactionOwn transaction)%I
    with "[Hdata Haccess Hentries Hblob Hauth]" as "Htransaction".
  { rewrite /writeSuccessTransactionOwn.
    iFrame "Hdata Haccess Hentries Hblob Hauth". done. }
  iEval (unfold writeSuccessTransactionsScratch150e8) in "Hscratch".
  iDestruct "Hscratch" as "(Hlower & HscratchTail)".
  iDestruct (mem_mapsto_uninit_split 32 with "Hlower") as
    "[Hlower32 HlowerRest]"; first lia.
  have HlowerAddress : bv_unsigned sp - 48 + 32 = bv_unsigned sp - 16
    by lia.
  iEval (rewrite HlowerAddress) in "HlowerRest".
  iDestruct (mem_mapsto_uninit_split 16 with "HlowerRest") as
    "[Hstack Hupper]"; first lia.
  iAssert (((bv_unsigned sp - 16) ↦ₘ? 16 -∗
    writeSuccessTransactionsScratch150e8
      sp base transactions processed transaction)%I)
    with "[Hlower32 Hupper HscratchTail]" as "HscratchFrame".
  { iIntros "HstackNew".
    iAssert ((bv_unsigned sp - 16) ↦ₘ? 120)%I
      with "[HstackNew Hupper]" as "HlowerRest".
    { iApply (mem_mapsto_uninit_combine 16 with "HstackNew"); first lia.
      have HstackAddress : bv_unsigned sp - 16 + 16 = bv_unsigned sp by lia.
      rewrite HstackAddress. iExact "Hupper". }
    iAssert ((bv_unsigned sp - 48) ↦ₘ? 152)%I
      with "[Hlower32 HlowerRest]" as "Hlower".
    { iApply (mem_mapsto_uninit_combine 32 with "Hlower32"); first lia.
      have HlowerEnd : bv_unsigned sp - 48 + 32 = bv_unsigned sp - 16 by lia.
      rewrite HlowerEnd. iExact "HlowerRest". }
    iEval (unfold writeSuccessTransactionsScratch150e8). iFrame. }
  iEval (rewrite !reg_col_cons reg_col_nil) in "Hother".
  iDestruct "Hother" as
    "(H3 & H4 & H6 & H7 & H12 & H13 & H14 & H15 & H16 & H17 & H28 & H29 &
      H30 & H31 & _)".
  iDestruct "H12" as (v12) "(%Hv12 & H12)".
  apply (proj2 (simpl_impl (P := valu_has_shape v12 (BitsShape 64))
    (Ps := ∃ b12 : bv 64, v12 = RVal_Bits b12))) in Hv12.
  destruct Hv12 as (b12 & ->).
  iDestruct "H13" as (v13) "(%Hv13 & H13)".
  apply (proj2 (simpl_impl (P := valu_has_shape v13 (BitsShape 64))
    (Ps := ∃ b13 : bv 64, v13 = RVal_Bits b13))) in Hv13.
  destruct Hv13 as (b13 & ->).
  iDestruct "H14" as (v14) "(%Hv14 & H14)".
  apply (proj2 (simpl_impl (P := valu_has_shape v14 (BitsShape 64))
    (Ps := ∃ b14 : bv 64, v14 = RVal_Bits b14))) in Hv14.
  destruct Hv14 as (b14 & ->).
  iDestruct "H15" as (v15) "(%Hv15 & H15)".
  apply (proj2 (simpl_impl (P := valu_has_shape v15 (BitsShape 64))
    (Ps := ∃ b15 : bv 64, v15 = RVal_Bits b15))) in Hv15.
  destruct Hv15 as (b15 & ->).
  iDestruct "H16" as (v16) "(%Hv16 & H16)".
  apply (proj2 (simpl_impl (P := valu_has_shape v16 (BitsShape 64))
    (Ps := ∃ b16 : bv 64, v16 = RVal_Bits b16))) in Hv16.
  destruct Hv16 as (b16 & ->).
  iDestruct "H17" as (v17) "(%Hv17 & H17)".
  apply (proj2 (simpl_impl (P := valu_has_shape v17 (BitsShape 64))
    (Ps := ∃ b17 : bv 64, v17 = RVal_Bits b17))) in Hv17.
  destruct Hv17 as (b17 & ->).
  iAssert (reg_col ((fun r => (KindReg r, BitsShape 64)) <$>
    tmp_registers))%I with "[H5 H6 H7 H28 H29 H30 H31]" as "Htmp".
  { cbn. iSplitL "H5".
    - iExists (RVal_Bits (BV 64 (mapIoContextAddress defaultMap))).
      iSplit; [iPureIntro; cbn; done | iFrame "H5"].
    - iFrame "H6 H7 H28 H29 H30 H31". }
  iEval (unfold writeSuccessTransactionsInvariant) in "Hinv".
  iDestruct "Hinv" as
    "(HtransactionsEq & HbytesEq & HprefixEq & HsuffixEq & HbytesAppend &
      HbytesLength & HprefixLength & HsuffixLength & HtransactionsBound &
      %Halign & %HlowerBound & %HupperBound & HbaseAlign & HbaseLower &
      HbaseUpper & _)".
  have HstackBound :
      (mapRamBase defaultMap) <= bv_unsigned sp - 16 /\ bv_unsigned sp < (machineRamEnd defaultMap).
  { split; [lia | lia]. }
  iAssert (writeSuccessTransactionsInvariant sp base transactions processed
    (transaction :: remaining) bytes prefix suffix)%I
    with "[HtransactionsEq HbytesEq HprefixEq HsuffixEq HbytesAppend
      HbytesLength HprefixLength HsuffixLength HtransactionsBound HbaseAlign
      HbaseLower HbaseUpper]" as "Hinv".
  { rewrite /writeSuccessTransactionsInvariant.
    iFrame "HtransactionsEq HbytesEq HprefixEq HsuffixEq HbytesAppend
      HbytesLength HprefixLength HsuffixLength HtransactionsBound HbaseAlign
      HbaseLower HbaseUpper".
    repeat iSplit; try iPureIntro; try assumption; done. }
  iAssert
    (writeSuccessTransactionsOptionalAddressNone15198ReturnFrame P sp base
      transaction transactions processed remaining bytes prefix suffix tail)%I
    with "[H3 H4 Hprefix Hsuffix Hprocessed Htransaction Hremaining HP Hinv
      Hexit HscratchFrame]" as "Hframe".
  { rewrite /writeSuccessTransactionsOptionalAddressNone15198ReturnFrame.
    rewrite /writeSuccessTransactions150e8OtherRegShapes.
    rewrite /writeSuccessTransactions150e8OtherRegisters.
    cbn. iFrame. }
  iAssert
    (writeSuccessTransactionsOptionalAddressNone15198CallRet
      sp transaction remaining tail -∗ writeSuccessTransactionsAt1519cSpec P)%I
    with "[Hframe]" as "HadaptWand".
  { iIntros "Hpost".
    iApply (write_success_transactions_optional_address_none_15198_return_adapter
      P sp base transaction transactions processed remaining bytes prefix suffix
      tail with "Hpost [] Hframe").
    iPureIntro. exact Hto. }
  iPoseProof (instr_pre_wand 0x1519c 0x1519c false true with "Hnext")
    as "HretPre"; [done | reflexivity |].
  iSpecialize ("HretPre" with "HadaptWand").
  iClear "Hlookup Hcode Hinstr15198 Hbody15198 HbooleanHidden".
  iEval (unfold zesuEncoderBooleanCallSpec, zesu_c_call).
  iExists sp, (BV 64 0x1519c).
  iEval (rewrite !reg_mapsto_pred_eq /reg_mapsto_pred_def).
  iFrame.
  liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve.
  all: try (iPureIntro; exact HstackBound).
Qed.
