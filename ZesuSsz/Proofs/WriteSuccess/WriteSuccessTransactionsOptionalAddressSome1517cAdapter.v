From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderBooleanCall.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsOptionalAddressSome1517c.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsOptionalAddressSome1517cBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsOptionalAddressSomeHandoff.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsOptionalAddressSome15170Handoff.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsOptionalAddressSome15178Handoff.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsSpec.

Lemma write_success_transactions_optional_address_some_1517c_adapter
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15b9c zesuEncoderBooleanCallSpec -∗
  instr_body 0x15180 (writeSuccessTransactionsOptionalAddressSomePostSpec P) -∗
  instr_body 0x1517c (writeSuccessTransactionsOptionalAddressSomeAt1517cSpec P).
Proof.
  iStartProof.
  iIntros "#Hlookup #Hcode #Hboolean Hnext".
  iPoseProof (write_success_transactions_optional_address_some_1517c_core P with
    "Hlookup Hcode Hboolean Hnext") as "Hcore".
  iEval (rewrite instr_pre'_eq) in "Hcore".
  rewrite instr_pre'_eq.
  iIntros "Hsetup".
  iEval (unfold writeSuccessTransactionsOptionalAddressSomeAt1517cSpec) in "Hsetup".
  iDestruct "Hsetup" as
    "(%sp & %base & %transaction & %transactions & %processed & %remaining &
      %bytes & %prefix & %suffix & %tail & %Hsome & Hphase)".
  iEval (unfold WriteSuccessTransactionsSpec.writeSuccessTransactionPhaseHandoff)
    in "Hphase".
  iDestruct "Hphase" as
    "(Hmachine & Hprefix & Hsuffix & Hprocessed & Htransaction & Hremaining &
      Hmmio & Htrace & HP & Hinv & Hexit & _)".
  iEval (unfold writeSuccessTransactionsMachine1517c) in "Hmachine".
  iDestruct "Hmachine" as
    "(Hsys & Hother & H1 & H2 & H5 & H8 & H9 & H10 & H11 & H12 & H18 & H19 &
      H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27 & Hscratch & _)".
  iEval (unfold WriteSuccessTransactionsSpec.writeSuccessTransactionOwn)
    in "Htransaction".
  iDestruct "Htransaction" as
    "(Hdata & Haccess & Hentries & Hblob & Hauth & %Hvalid & _)".
  have HtoSome : exists address,
      writeSuccessTransactionTo transaction = Some address.
  { destruct (writeSuccessTransactionTo transaction) as [address|] eqn:Hto.
    - eexists. reflexivity.
    - unfold writeSuccessTransactionValid in Hvalid.
      rewrite Hto in Hvalid. exfalso. apply Hsome. naive_solver. }
  iAssert (WriteSuccessTransactionsSpec.writeSuccessTransactionOwn transaction)%I
    with "[Hdata Haccess Hentries Hblob Hauth]" as "Htransaction".
  { rewrite /WriteSuccessTransactionsSpec.writeSuccessTransactionOwn.
    iFrame "Hdata Haccess Hentries Hblob Hauth". done. }
  destruct HtoSome as [address HtoValue].
  iEval (unfold WriteSuccessTransactionsSpec.writeSuccessTransactionPhaseEvents,
    WriteSuccessTransactionsSpec.writeSuccessOptionalAddressEvents;
    rewrite HtoValue) in "Htrace".
  iEval (unfold WriteSuccessTransactionsSpec.writeSuccessTransactionsInvariant)
    in "Hinv".
  iDestruct "Hinv" as
    "(HtransactionsEq & HbytesEq & HprefixEq & HsuffixEq & HbytesAppend &
      HbytesLength & HprefixLength & HsuffixLength & HtransactionsBound &
      %Halign & %HlowerBound & %HupperBound & HbaseAlign & HbaseLower &
      HbaseUpper & _)".
  have HstackLower : (0x20000000 <= bv_unsigned sp - 16)%Z by lia.
  have HstackUpper : (bv_unsigned sp < 0x40000000)%Z by lia.
  iAssert (WriteSuccessTransactionsSpec.writeSuccessTransactionsInvariant
    sp base transactions processed (transaction :: remaining) bytes prefix suffix)%I
    with "[HtransactionsEq HbytesEq HprefixEq HsuffixEq HbytesAppend
      HbytesLength HprefixLength HsuffixLength HtransactionsBound HbaseAlign
      HbaseLower HbaseUpper]" as "Hinv".
  { rewrite /WriteSuccessTransactionsSpec.writeSuccessTransactionsInvariant.
    iFrame "HtransactionsEq HbytesEq HprefixEq HsuffixEq HbytesAppend
      HbytesLength HprefixLength HsuffixLength HtransactionsBound HbaseAlign
      HbaseLower HbaseUpper".
    repeat iSplit; try iPureIntro; try assumption; done. }
  iEval (unfold writeSuccessTransactionsScratch15174,
    writeSuccessTransactionsScratch1516Prefix) in "Hscratch".
  iDestruct "Hscratch" as "(HscratchLow & HscratchTail)".
  iEval (unfold writeSuccessTransactionsScratch1516Prefix) in "HscratchLow".
  iDestruct "HscratchLow" as "(HscratchLow & HscratchPrefixTail)".
  iDestruct (mem_mapsto_uninit_split 32 with "HscratchLow") as
    "[HscratchLower HscratchMiddle]"; first lia.
  have HstackAddress : bv_unsigned sp - 48 + 32 = bv_unsigned sp - 16 by lia.
  iEval (rewrite HstackAddress) in "HscratchMiddle".
  iDestruct (mem_mapsto_uninit_split 16 with "HscratchMiddle") as
    "[Hstack HscratchUpper]"; first lia.
  have HupperAddress : bv_unsigned sp - 16 + 16 = bv_unsigned sp by lia.
  iEval (rewrite HupperAddress) in "HscratchUpper".
  iAssert (((bv_unsigned sp - 16) ↦ₘ? 16 -∗
      writeSuccessTransactionsScratch15174
        sp base transactions processed transaction)%I)
    with "[HscratchLower HscratchUpper HscratchPrefixTail HscratchTail]"
    as "HscratchFrame".
  { iIntros "HreturnedStack".
    iAssert ((bv_unsigned sp - 48) ↦ₘ? 48)%I
      with "[HscratchLower HreturnedStack]" as "HscratchLow48".
    { iApply (mem_mapsto_uninit_combine 32 with "HscratchLower"); first lia.
      rewrite HstackAddress. iExact "HreturnedStack". }
    iAssert ((bv_unsigned sp - 48) ↦ₘ? 152)%I
      with "[HscratchLow48 HscratchUpper]" as "HscratchLow".
    { iApply (mem_mapsto_uninit_combine 48 with "HscratchLow48"); first lia.
      have HscratchEnd : bv_unsigned sp - 48 + 48 = bv_unsigned sp by lia.
      rewrite HscratchEnd. iExact "HscratchUpper". }
    iEval (unfold writeSuccessTransactionsScratch15174,
      writeSuccessTransactionsScratch1516Prefix).
    iFrame "HscratchLow HscratchPrefixTail HscratchTail". }
  iEval (rewrite !reg_col_cons reg_col_nil) in "Hother".
  iDestruct "Hother" as
    "(H3 & H4 & H6 & H7 & H13 & H14 & H15 & H16 & H17 & H28 & H29 & H30 &
      H31 & _)".
  iAssert (reg_col ((fun r => (KindReg r, BitsShape 64)) <$> tmp_registers))%I
    with "[H5 H6 H7 H28 H29 H30 H31]" as "Htmp".
  { rewrite /tmp_registers !reg_col_cons reg_col_nil. iFrame.
    repeat iSplit; iPureIntro; done. }
  iAssert (reg_col ((fun r => (KindReg r, BitsShape 64)) <$>
    ["x12"; "x13"; "x14"; "x15"; "x16"; "x17"]))%I
    with "[H12 H13 H14 H15 H16 H17]" as "Hcaller".
  { rewrite !reg_col_cons reg_col_nil. iFrame; done. }
  iAssert (reg_col
    [(KindReg "x8", ExactShape
        (RVal_Bits (writeSuccessTransactionWord transaction 192)));
     (KindReg "x9", ExactShape
        (RVal_Bits (writeSuccessTransactionWord transaction 16)));
     (KindReg "x18", ExactShape
        (RVal_Bits (writeSuccessTransactionWord transaction 48)));
     (KindReg "x19", ExactShape
        (RVal_Bits (writeSuccessTransactionWord transaction 224)));
     (KindReg "x20", ExactShape
        (RVal_Bits (writeSuccessTransactionWord transaction 56)));
     (KindReg "x21", ExactShape
        (RVal_Bits (writeSuccessTransactionWord transaction 72)));
     (KindReg "x22", ExactShape
        (RVal_Bits (writeSuccessTransactionWord transaction 200)));
     (KindReg "x23", ExactShape
        (RVal_Bits (writeSuccessTransactionWord transaction 24)));
     (KindReg "x24", ExactShape
        (RVal_Bits (writeSuccessTransactionWord transaction 8)));
     (KindReg "x25", ExactShape
        (RVal_Bits (writeSuccessTransactionWord transaction 0)));
     (KindReg "x26", ExactShape
        (RVal_Bits (writeSuccessTransactionWord transaction 184)));
     (KindReg "x27", ExactShape (RVal_Bits
        (bv_zero_extend 64 (writeSuccessTransactionByte transaction 32))))])%I
    with "[H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27]" as "Hsaved".
  { rewrite !reg_col_cons reg_col_nil. iFrame; done. }
  iAssert (writeSuccessTransactionsOptionalAddressSomeFrame P sp base transaction
      transactions processed remaining bytes prefix suffix tail)%I
    with "[Hprefix Hsuffix Hprocessed Htransaction Hremaining HP Hinv Hexit]"
    as "Hframe".
  { rewrite /writeSuccessTransactionsOptionalAddressSomeFrame.
    iFrame "Hprefix Hsuffix Hprocessed Htransaction Hremaining HP Hinv Hexit".
    iSplit; [iPureIntro; rewrite HtoValue; discriminate | done]. }
  iAssert (writeSuccessTransactionsOptionalAddressSomeCallerFrame P sp base
      transaction transactions processed remaining bytes prefix suffix tail)%I
    with "[H3 H4 HscratchFrame Hframe]" as "HcallerFrame".
  { rewrite /writeSuccessTransactionsOptionalAddressSomeCallerFrame.
    rewrite !reg_col_cons reg_col_nil. iFrame; done. }
  iAssert ("x1" ↦ᵣ RVal_Bits (BV 64 0x16178))%I with "[H1]" as "H1Call".
  { replace (BV 64 0x16178) with
      (Z_to_bv 64 0x15178 + BV 64 0x1000)%bv by bv_solve.
    iExact "H1". }
  iApply "Hcore".
  iExists sp, base, transaction, transactions, processed, remaining,
    bytes, prefix, suffix, tail.
  iEval (unfold writeSuccessTransactionsOptionalAddressSomeBooleanSetupSpec).
  iFrame "Hsys Htmp Hcaller Hsaved H1Call H2 H10 H11 Hstack Hmmio Htrace HcallerFrame".
  repeat iSplit; try iPureIntro; try assumption; done.
Qed.
