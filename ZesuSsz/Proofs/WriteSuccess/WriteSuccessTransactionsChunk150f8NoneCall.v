From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import
  Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Experiments.WriteSuccessCallAbi.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderOptionalU64Call.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsChunk150f0Spec.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary150fc.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsChunk150f8TagBridge.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsChunk150f8InvariantBound.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsChunk150f8ScratchRest.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsChunk150f8RawReturn.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsChunk150f8NoneCallEntry.
From IslaTraces.write_success_35 Require Import a150f8_spec.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.
#[local] Typeclasses Opaque writeSuccessTransactions150f0Frame.

#[local] Hint Extern 7
  (FindInContext (FindInstrKind ?address ?later) FICSyntactic) =>
  let reduced := eval vm_compute in address in
  first [ constr_eq address reduced; fail 1
        | change (FindInContext (FindInstrKind reduced later) FICSyntactic);
          typeclasses eauto ] : typeclass_instances.

Lemma write_success_transactions_word_take8_split
    (values : list (bv 8)) (offset : nat) :
  8%nat <= length (drop offset values) ->
  exists tail,
    bv_to_little_endian 8 8
      (bv_unsigned (Z_to_bv 64
        (little_endian_to_bv 8 (take 8 (drop offset values))))) =
    default (BV 8 0) (values !! offset) :: tail.
Proof.
  intros Hlen.
  have Htake : length (take 8 (drop offset values)) = 8%nat.
  { rewrite length_take. rewrite Nat.min_l; lia. }
  have Hround :
      bv_to_little_endian 8 8
        (bv_unsigned (Z_to_bv 64
          (little_endian_to_bv 8 (take 8 (drop offset values))))) =
      take 8 (drop offset values).
  { apply u64_bytes_roundtrip. exact Htake. }
  rewrite Hround.
  destruct (drop offset values) as [|b rest] eqn:Hdrop.
  - cbn in Hlen. lia.
  - have Hlookup : values !! offset = Some b.
    { pose proof (lookup_drop values offset 0) as Hlookup0.
      rewrite Hdrop in Hlookup0. cbn in Hlookup0.
      rewrite Nat.add_0_r in Hlookup0. symmetry. exact Hlookup0. }
    rewrite Hlookup. cbn.
    exists (tl (take 8 (b :: rest))).
    cbn. reflexivity.
Qed.

Lemma write_success_transactions_word_168_split
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction) :
  WriteSuccessTransactionsSpec.writeSuccessTransactionValid transaction ->
  exists tail,
    bv_to_little_endian 8 8
      (bv_unsigned
        (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 168)) =
    WriteSuccessTransactionsSpec.writeSuccessTransactionByte transaction 168 :: tail.
Proof.
  intros Hvalid.
  destruct Hvalid as (Hlength & _).
  apply write_success_transactions_word_take8_split.
  rewrite length_drop Hlength. lia.
Qed.

Lemma write_success_transactions_chunk_150f8_none_call_block
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15bc8 zesuEncoderOptionalU64NoneCallSpec -∗
  instr_body 0x150fc (writeSuccessTransactionsAt150fcFramedSpec P) -∗
  instr_body 0x150f8 (writeSuccessTransactionsAt150f8NoneBlock P sp base
    transaction transactions processed remaining bytes prefix suffix tail).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode #Hoptional Hnext".
  iEval (rewrite /instr_lookup_resources) in "Hlookup".
  iPoseProof ("Hlookup" $! 0x150f8 with "[]") as "#Hinstr150f8".
  { iPureIntro.
    rewrite IslaTraces.write_success_blocks.Index.lookup_a150f8.
    done. }
  iPoseProof (IslaTraces.write_success_35.a150f8_spec.a150f8_spec
    0x150f8 with "Hinstr150f8") as "Hjalr".
  rewrite instr_pre'_eq. iIntros "Hentry".
  iEval (rewrite -instr_pre'_eq) in "Hoptional".
  iEval (unfold writeSuccessTransactionsAt150f8NoneBlock) in "Hentry".
  iDestruct "Hentry" as
    "(%Hchain & #Htag & Hmachine & Hmmio & Htrace & Hframe & _)".
  iDestruct "Htag" as %Htag.
  iEval (unfold writeSuccessTransactionsMachine150f8) in "Hmachine".
  iDestruct "Hmachine" as
    "(Hsys & Hother & H1 & H2 & H8 & H9 & H10 & H18 & H19 & H20 & H21 &
      H22 & H23 & H24 & H25 & H26 & H27 & Hscratch & _)".
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
  iIntros "Hentry".
  iEval (unfold zesuEncoderOptionalU64NoneCallSpec, zesu_c_call).
  iExists sp, (BV 64 0x150fc).
  iDestruct "Hentry" as "(HsysEntry & H1Entry & _)".
  iFrame "HsysEntry".
  iEval (rewrite !reg_col_cons reg_col_nil) in "Hother".
  iDestruct "Hother" as
    "(H3 & H4 & H5 & H6 & H7 & H11 & H12 & H13 & H14 & H15 & H16 & H17 &
      H28 & H29 & H30 & H31 & _)".
  iFrame "H5 H6 H7 H28 H29 H30 H31".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def).
  iEval (simpl).
  iApply bi.emp_sep_1.
  iExists (RVal_Bits (sp + BV 64 1664)%bv).
  iFrame "H10". iExists (sp + BV 64 1664)%bv. iSplit; first done.
  iDestruct "H11" as (v11 Hshape11) "H11".
  apply valu_has_bits_shape in Hshape11 as (b11 & ->).
  iExists (RVal_Bits b11).
  iFrame "H11". iExists b11. iSplit; first done.
  iDestruct "H12" as (v12 Hshape12) "H12".
  apply valu_has_bits_shape in Hshape12 as (b12 & ->).
  iExists (RVal_Bits b12). iFrame "H12". iExists b12. iSplit; first done.
  iDestruct "H13" as (v13 Hshape13) "H13".
  apply valu_has_bits_shape in Hshape13 as (b13 & ->).
  iExists (RVal_Bits b13). iFrame "H13". iExists b13. iSplit; first done.
  iDestruct "H14" as (v14 Hshape14) "H14".
  apply valu_has_bits_shape in Hshape14 as (b14 & ->).
  iExists (RVal_Bits b14). iFrame "H14". iExists b14. iSplit; first done.
  iDestruct "H15" as (v15 Hshape15) "H15".
  apply valu_has_bits_shape in Hshape15 as (b15 & ->).
  iExists (RVal_Bits b15). iFrame "H15". iExists b15. iSplit; first done.
  iDestruct "H16" as (v16 Hshape16) "H16".
  apply valu_has_bits_shape in Hshape16 as (b16 & ->).
  iExists (RVal_Bits b16). iFrame "H16". iExists b16. iSplit; first done.
  iDestruct "H17" as (v17 Hshape17) "H17".
  apply valu_has_bits_shape in Hshape17 as (b17 & ->).
  iExists (RVal_Bits b17). iFrame "H17". iExists b17. iSplit; first done.
  iExists (RVal_Bits (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
    transaction 192)%bv). iFrame "H8".
  iSplit; first (iPureIntro; cbn; done).
  iExists (RVal_Bits (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
    transaction 16)%bv). iFrame "H9".
  iSplit; first (iPureIntro; cbn; done).
  iExists (RVal_Bits (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
    transaction 48)%bv). iFrame "H18".
  iSplit; first (iPureIntro; cbn; done).
  iExists (RVal_Bits (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
    transaction 224)%bv). iFrame "H19".
  iSplit; first (iPureIntro; cbn; done).
  iExists (RVal_Bits (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
    transaction 56)%bv). iFrame "H20".
  iSplit; first (iPureIntro; cbn; done).
  iExists (RVal_Bits (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
    transaction 72)%bv). iFrame "H21".
  iSplit; first (iPureIntro; cbn; done).
  iExists (RVal_Bits (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
    transaction 200)%bv). iFrame "H22".
  iSplit; first (iPureIntro; cbn; done).
  iExists (RVal_Bits (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
    transaction 24)%bv). iFrame "H23".
  iSplit; first (iPureIntro; cbn; done).
  iExists (RVal_Bits (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
    transaction 8)%bv). iFrame "H24".
  iSplit; first (iPureIntro; cbn; done).
  iExists (RVal_Bits (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
    transaction 0)%bv). iFrame "H25".
  iSplit; first (iPureIntro; cbn; done).
  iExists (RVal_Bits (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
    transaction 184)%bv). iFrame "H26".
  iSplit; first (iPureIntro; cbn; done).
  iExists (RVal_Bits (bv_zero_extend 64
    (WriteSuccessTransactionsSpec.writeSuccessTransactionByte transaction 32))%bv).
  iFrame "H27". iSplit; first (iPureIntro; cbn; done).
  iPoseProof (write_success_transactions_scratch_150f8_split
    sp base transactions processed transaction with "Hscratch") as
    "(HscratchRest & Hstack & Hvalue & Htagword)".
  iEval (unfold writeSuccessTransactions150f0Frame) in "Hframe".
  iDestruct "Hframe" as
    "(Hprefix & Hsuffix & Hprocessed & Htransaction & Hremaining & HP &
      Hinvariant & Hexit & _)".
  iPoseProof (write_success_transaction_valid_frame transaction with
    "Htransaction") as "(%Hvalid & Htransaction)".
  destruct Hvalid as (Hlength & _).
  iPoseProof (write_success_transactions_invariant_bound sp base transaction
    transactions processed remaining bytes prefix suffix with "Hinvariant") as
    "(Hinvariant' & %Hmax & %Halign & %Hlower)".
  iAssert (writeSuccessTransactions150f0Frame P sp base transaction
      transactions processed remaining bytes prefix suffix tail)%I
    with "[Hprefix Hsuffix Hprocessed Htransaction Hremaining HP Hinvariant' Hexit]"
    as "Hframe'".
  { rewrite /writeSuccessTransactions150f0Frame. iFrame. }
  have Hdataaddr : bv_unsigned (sp + BV 64 1664)%bv = bv_unsigned sp + 1664
    by bv_solve.
  have Htagaddr : bv_unsigned (sp + BV 64 1664)%bv + 8 = bv_unsigned sp + 1672
    by bv_solve.
  have HtagSplit :
      exists tagTail,
        bv_to_little_endian 8 8
          (bv_unsigned
            (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
              transaction 168)) = BV 8 0 :: tagTail.
  { rewrite <- Htag. apply write_success_transactions_word_take8_split.
    rewrite length_drop Hlength. lia. }
  destruct HtagSplit as (tagTail & HtagSplit).
  iPoseProof (write_success_transactions_split_u64_tag
    (bv_unsigned sp + 1672)
    (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 168)
    (BV 8 0) tagTail with "Htagword") as "HtagSplitRes".
  iSpecialize ("HtagSplitRes" with "[]").
  { iPureIntro. exact HtagSplit. }
  iDestruct "HtagSplitRes" as "(Htagbyte & Htagtail)".
  iAssert (reg_col [(KindReg "x3", BitsShape 64);
                    (KindReg "x4", BitsShape 64)])
    with "[H3 H4]" as "Hcaller34".
  { rewrite /reg_col /=. iFrame. }
  have HtagTailAddr :
      (bv_unsigned sp + 1672 + 1)%Z = bv_unsigned sp + 1673 by lia.
  iEval (rewrite HtagTailAddr) in "Htagtail".
  iPoseProof (write_success_transactions_chunk_150f8_none_call_entry P
    sp base transaction transactions processed remaining bytes prefix suffix tail
    tagTail with "Hnext") as "Hret".
  iSpecialize ("Hret" with "[]").
  { iPureIntro. exact HtagSplit. }
  iSpecialize ("Hret" with "Hcaller34").
  iAssert ("x1" ↦ᵣ RVal_Bits (BV 64 0x150fc))%I
    with "[H1Entry]" as "H1target".
  { replace (BV 64 0x150fc) with (Z_to_bv 64 (86264 + 4))
      by bv_solve; iExact "H1Entry". }
  iFrame "H1target H2".
  iSplit; first (iPureIntro; exact Halign).
  iSplit; first (iPureIntro; bv_solve).
  iSplit; first (iPureIntro; bv_solve).
  iSplit; first (iPureIntro; bv_solve).
  iSplit; first (iPureIntro; split; lia).
  iEval (rewrite <- Hdataaddr) in "Hvalue".
  iEval (rewrite <- Htagaddr) in "Htagbyte".
  iEval (rewrite /WriteSuccessTransactionsSpec.writeSuccessTransactionPhaseEvents) in "Htrace".
  iEval (rewrite Hchain) in "Htrace".
  iFrame "Hstack Hvalue Htagbyte Htrace Hmmio".
  iSplit; first done.
  iSplit; first (iPureIntro; bv_simplify_arith Halign; bv_solve).
  iSplit; first (iPureIntro; lia).
  iSplit; first (iPureIntro; lia).
  iApply (instr_pre_wand 0x150fc 0x150fc true true with "Hret");
    [done | reflexivity |].
  iIntros "Hpost".
  iEval (unfold zesu_c_call_ret) in "Hpost".
  iDestruct "Hpost" as "(HsysPost & HtmpPost & HsavedPost & HrestPost)".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "HrestPost".
  iDestruct "HrestPost" as (r10Post) "(H10Post & HrestPost)".
  iDestruct "HrestPost" as (b10Post) "(%Hr10Post & HrestPost)".
  iDestruct "HrestPost" as (r11Post) "(H11Post & HrestPost)".
  iDestruct "HrestPost" as (b11Post) "(%Hr11Post & H2Post & HstackPost & HQPost)".
  subst r10Post r11Post.
  iEval (unfold zesu_c_call_ret).
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def).
  iFrame "HsysPost HtmpPost HsavedPost H10Post H11Post H2Post HstackPost".
  iExists b10Post. iSplit; first done.
  iExists b11Post. iSplit; first done.
  iDestruct "HQPost" as "(HvaluePost & HtagPost & HmmioPost & HtracePost & _)".
  iEval (rewrite Hdataaddr) in "HvaluePost".
  iEval (rewrite Htagaddr) in "HtagPost".
  iFrame "Hframe' HscratchRest Htagtail HmmioPost HtracePost".
  iFrame "HvaluePost HtagPost".
  Unshelve. all: try prepare_sidecond; try bv_solve; try lia; try iFrame.
Qed.

Lemma write_success_transactions_chunk_150f8_none_call
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15bc8 zesuEncoderOptionalU64NoneCallSpec -∗
  instr_body 0x150fc (writeSuccessTransactionsAt150fcFramedSpec P) -∗
  instr_body 0x150f8 (writeSuccessTransactionsAt150f8NoneSpec P).
Proof.
  iStartProof. iIntros "#Hlookup #Hcode Hoptional Hnext".
  rewrite instr_pre'_eq. iIntros "Hentry".
  iEval (rewrite -instr_pre'_eq) in "Hoptional".
  iEval (rewrite -instr_pre'_eq) in "Hnext".
  rewrite /writeSuccessTransactionsAt150f8NoneSpec.
  iDestruct "Hentry" as
    (sp base transaction transactions processed remaining bytes prefix suffix
      tail) "Hentry".
  iPoseProof (write_success_transactions_chunk_150f8_none_call_block P sp base
    transaction transactions processed remaining bytes prefix suffix tail
    with "Hlookup Hcode Hoptional Hnext") as "Hbody".
  iEval (rewrite instr_pre'_eq) in "Hbody".
  iApply ("Hbody" with "Hentry").
Qed.
