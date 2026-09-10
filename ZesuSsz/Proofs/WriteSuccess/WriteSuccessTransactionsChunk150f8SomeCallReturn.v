From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Experiments.WriteSuccessCallAbi.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsChunk150f0Spec.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary150f0.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary150e8.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary150fc.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsChunk150f8ScratchRest.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsChunk150f8InvariantBound.

Import ListNotations.

Lemma write_success_transactions_some_scratch_combine
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z)
    (transactions processed : list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (tag : bv 8) (tagTail : list (bv 8)) :
  writeSuccessTransactionsScratchRest150f8 sp base transactions processed transaction -∗
  (bv_unsigned sp - 32) ↦ₘ? 32 -∗
  (bv_unsigned sp + 1664) ↦ₘ
    WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 160 -∗
  (bv_unsigned sp + 1672) ↦ₘ tag -∗
  (bv_unsigned sp + 1673) ↦ₘ∗ tagTail -∗
  ⌜bv_to_little_endian 8 8
      (bv_unsigned
        (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 168)) =
      tag :: tagTail⌝ -∗
  writeSuccessTransactionsScratch150e8 sp base transactions processed transaction.
Proof.
  iIntros "Hrest Hstack Hvalue Htag Htail" (Hshape).
  iEval (rewrite <- mem_mapsto_array_singleton) in "Htag".
  have HtagAddr :
      (bv_unsigned sp + 1672 + Z.of_N (8 `div` 8) * 1)%Z =
      bv_unsigned sp + 1673 by cbn; lia.
  iEval (rewrite <- HtagAddr) in "Htail".
  iPoseProof (mem_mapsto_array_app_combine 8%N (bv_unsigned sp + 1672)
    (DfracOwn 1) [tag] tagTail with "Htag Htail") as "HtagArray".
  iPoseProof (mem_mapsto_byte_array_to_mapsto
    (bv_unsigned sp + 1672) (DfracOwn 1) ([tag] ++ tagTail)
    with "HtagArray") as "HtagWord".
  have HtagLen : length ([tag] ++ tagTail) = 8%nat.
  { pose proof (f_equal (@length (bv 8)) Hshape) as Hlen.
    rewrite length_bv_to_little_endian in Hlen; [|lia].
    cbn in Hlen. symmetry. exact Hlen. }
  have HtagRound :
      Z_to_bv 64
        (little_endian_to_bv 8 ([tag] ++ tagTail)) =
      WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 168.
  { pose proof (Z_to_bv_little_endian_to_bv_to_little_endian
      64 8 8
      (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 168)
      ltac:(lia) ltac:(cbn; lia)) as Hround.
    rewrite Hshape in Hround. exact Hround. }
  iEval (rewrite HtagLen HtagRound) in "HtagWord".
  iEval (rewrite /writeSuccessTransactionsScratchRest150f8) in "Hrest".
  iDestruct "Hrest" as
    "(Hlower16 & Hupper104 & Hbase & Hlength & H120 & H128 & H136 & H144 &
      H152 & H160 & H168 & H176 & H184 & H192 & H200 & H208 & H216 & H224 &
      H232 & H240 & H248 & H256 & H264 & H272 & H280 & H1640 & H1648 &
      H1656 & H1660 & H1680 & H1744 & H1745 & _)".
  have HstackAddr : bv_unsigned sp - 48 + 16 = bv_unsigned sp - 32 by lia.
  have HupperAddr : bv_unsigned sp - 48 + 48 = bv_unsigned sp by lia.
  iAssert ((bv_unsigned sp - 48) ↦ₘ? 152)%I
    with "[Hlower16 Hstack Hupper104]" as "Hlower".
  { iAssert ((bv_unsigned sp - 48) ↦ₘ? 48)%I
      with "[Hlower16 Hstack]" as "Hlower48".
    { iApply (mem_mapsto_uninit_combine 16 with "[Hlower16] [Hstack]");
        [lia | iExact "Hlower16" | iEval (rewrite HstackAddr); iExact "Hstack"]. }
    iApply (mem_mapsto_uninit_combine 48 with "[Hlower48] [Hupper104]");
      [lia | iExact "Hlower48" | iEval (rewrite HupperAddr); iExact "Hupper104"]. }
  iEval (rewrite /writeSuccessTransactionsScratch150e8).
  iFrame.
Qed.

Lemma write_success_transactions_150fc_some_raw_return_adapter
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining : list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) (tagTail : list (bv 8)) :
  zesu_c_call_ret 32
    [RVal_Bits (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 192);
     RVal_Bits (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 16);
     RVal_Bits (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 48);
     RVal_Bits (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 224);
     RVal_Bits (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 56);
     RVal_Bits (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 72);
     RVal_Bits (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 200);
     RVal_Bits (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 24);
     RVal_Bits (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 8);
     RVal_Bits (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 0);
     RVal_Bits (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 184);
      RVal_Bits (bv_zero_extend 64
       (WriteSuccessTransactionsSpec.writeSuccessTransactionByte transaction 32))]
    (BV 64 0x150fc) sp
    (fun _ =>
      writeSuccessTransactions150f0Frame P sp base transaction transactions
        processed remaining bytes prefix suffix tail ∗
      writeSuccessTransactionsScratchRest150f8 sp base transactions processed transaction ∗
      (bv_unsigned (sp + BV 64 1664)%bv) ↦ₘ
        WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 160 ∗
      (bv_unsigned (sp + BV 64 1664)%bv + 8) ↦ₘ
        WriteSuccessTransactionsSpec.writeSuccessTransactionByte transaction 168 ∗
      (bv_unsigned sp + 1673) ↦ₘ∗ tagTail ∗
      mmio_range 0x2401a0c0 16 ∗
      spec_trace
        (WriteSuccessTransactionsSpec.writeSuccessTransactionPhaseEvents
          WriteSuccessTransactionsSpec.TransactionNonce sp transaction
      (WriteSuccessTransactionsSpec.writeSuccessTransactionsEvents
            sp remaining tail)) ∗ True) -∗
  ⌜bv_to_little_endian 8 8
      (bv_unsigned
        (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 168)) =
      WriteSuccessTransactionsSpec.writeSuccessTransactionByte transaction 168 :: tagTail⌝ -∗
  reg_col [(KindReg "x3", BitsShape 64); (KindReg "x4", BitsShape 64)] -∗
  writeSuccessTransactionsAt150fcFramedSpec P.
Proof.
  iIntros "Hret" (Hshape) "Hcaller34".
  iEval (unfold zesu_c_call_ret) in "Hret".
  iDestruct "Hret" as "(Hsys & Htmp & Hsaved & Hrest)".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "Hrest".
  iDestruct "Hrest" as (r10) "(H10 & Hrest)".
  iDestruct "Hrest" as (b10) "(%Hr10Bits & Hrest)".
  iDestruct "Hrest" as (r11) "(H11 & Hrest)".
  iDestruct "Hrest" as (b11) "(%Hr11Bits & H2 & Hstack & HQ)".
  subst r10 r11.
  iDestruct "HQ" as
    "(Hframe & HscratchRest & Hvalue & Htag & Htagtail & Hmmio & Htrace & _)".
  iEval (rewrite /reg_col /=) in "Htmp Hsaved Hcaller34".
  iDestruct "Hcaller34" as "(H3 & H4 & _)".
  iDestruct "Htmp" as
    "(H1 & H12 & H13 & H14 & H15 & H16 & H17 & H5 & H6 & H7 & H28 & H29 &
      H30 & H31 & _)".
  iDestruct "Hsaved" as
    "(H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27 & _)".
  iDestruct "H8" as (v8) "(%Hv8 & H8)". subst v8.
  iDestruct "H9" as (v9) "(%Hv9 & H9)". subst v9.
  iDestruct "H18" as (v18) "(%Hv18 & H18)". subst v18.
  iDestruct "H19" as (v19) "(%Hv19 & H19)". subst v19.
  iDestruct "H20" as (v20) "(%Hv20 & H20)". subst v20.
  iDestruct "H21" as (v21) "(%Hv21 & H21)". subst v21.
  iDestruct "H22" as (v22) "(%Hv22 & H22)". subst v22.
  iDestruct "H23" as (v23) "(%Hv23 & H23)". subst v23.
  iDestruct "H24" as (v24) "(%Hv24 & H24)". subst v24.
  iDestruct "H25" as (v25) "(%Hv25 & H25)". subst v25.
  iDestruct "H26" as (v26) "(%Hv26 & H26)". subst v26.
  iDestruct "H27" as (v27) "(%Hv27 & H27)". subst v27.
  iEval (unfold writeSuccessTransactions150f0Frame) in "Hframe".
  iDestruct "Hframe" as
    "(Hprefix & Hsuffix & Hprocessed & Htransaction & Hremaining & HP &
      Hinvariant & Hexit & _)".
  iPoseProof (write_success_transactions_invariant_bound sp base transaction
    transactions processed remaining bytes prefix suffix with "Hinvariant") as
    "(Hinvariant' & %Hmax & %Halign & %Hlower)".
  iAssert (writeSuccessTransactions150f0Frame P sp base transaction
      transactions processed remaining bytes prefix suffix tail)%I
    with "[Hprefix Hsuffix Hprocessed Htransaction Hremaining HP Hinvariant' Hexit]"
    as "Hframe'".
  { rewrite /writeSuccessTransactions150f0Frame. iFrame. }
  have Hdataaddr : bv_unsigned (sp + BV 64 1664)%bv = bv_unsigned sp + 1664
    by bv_simplify_arith; bv_solve.
  have Htagaddr : bv_unsigned (sp + BV 64 1664)%bv + 8 = bv_unsigned sp + 1672
    by bv_simplify_arith; bv_solve.
  iEval (rewrite Hdataaddr) in "Hvalue".
  iEval (rewrite Htagaddr) in "Htag".
  iPoseProof (write_success_transactions_some_scratch_combine
    sp base transactions processed transaction
    (WriteSuccessTransactionsSpec.writeSuccessTransactionByte transaction 168)
    tagTail) as "Hscratch".
  iSpecialize ("Hscratch" with "HscratchRest").
  iSpecialize ("Hscratch" with "Hstack").
  iSpecialize ("Hscratch" with "Hvalue").
  iSpecialize ("Hscratch" with "Htag").
  iSpecialize ("Hscratch" with "Htagtail").
  iSpecialize ("Hscratch" with "[]").
  { iPureIntro. exact Hshape. }
  iExists sp, base, transaction, transactions, processed, remaining,
    bytes, prefix, suffix, tail.
  rewrite /writeSuccessTransactionsMachine150fc
    /writeSuccessTransactionsMachine150f0.
  iFrame "Hsys H2 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27
    Hscratch Hmmio Htrace Hframe'".
  rewrite /writeSuccessTransactions150f0OtherRegShapes /reg_col /=.
  iFrame "H1 H3 H4 H5 H6 H7 H10 H11 H12 H13 H14 H15 H16 H17 H28 H29 H30 H31".
  iFrame.
  repeat iSplit; try iPureIntro; try reflexivity; try assumption; try done.
  Unshelve. all: try prepare_sidecond; try bv_solve; try lia; try iFrame.
Qed.

Lemma write_success_transactions_chunk_150f8_some_call_entry
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining : list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) (tagTail : list (bv 8)) :
  instr_pre'_def false 0x150fc (writeSuccessTransactionsAt150fcFramedSpec P) -∗
  ⌜bv_to_little_endian 8 8
      (bv_unsigned
        (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 168)) =
      WriteSuccessTransactionsSpec.writeSuccessTransactionByte transaction 168 :: tagTail⌝ -∗
  reg_col [(KindReg "x3", BitsShape 64); (KindReg "x4", BitsShape 64)] -∗
  instr_pre (bv_unsigned (BV 64 0x150fc))
    (zesu_c_call_ret 32
      [RVal_Bits (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 192);
       RVal_Bits (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 16);
       RVal_Bits (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 48);
       RVal_Bits (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 224);
       RVal_Bits (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 56);
       RVal_Bits (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 72);
       RVal_Bits (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 200);
       RVal_Bits (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 24);
       RVal_Bits (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 8);
       RVal_Bits (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 0);
       RVal_Bits (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 184);
       RVal_Bits (bv_zero_extend 64
         (WriteSuccessTransactionsSpec.writeSuccessTransactionByte transaction 32))]
      (BV 64 0x150fc) sp
      (fun _ =>
        writeSuccessTransactions150f0Frame P sp base transaction transactions
          processed remaining bytes prefix suffix tail ∗
        writeSuccessTransactionsScratchRest150f8 sp base transactions processed transaction ∗
        (bv_unsigned (sp + BV 64 1664)%bv) ↦ₘ
          (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 160) ∗
        (bv_unsigned (sp + BV 64 1664)%bv + 8) ↦ₘ
          WriteSuccessTransactionsSpec.writeSuccessTransactionByte transaction 168 ∗
        (bv_unsigned sp + 1673) ↦ₘ∗ tagTail ∗
        mmio_range 0x2401a0c0 16 ∗
        spec_trace
          (WriteSuccessTransactionsSpec.writeSuccessTransactionPhaseEvents
            WriteSuccessTransactionsSpec.TransactionNonce sp transaction
            (WriteSuccessTransactionsSpec.writeSuccessTransactionsEvents
              sp remaining tail)) ∗ True)).
Proof.
  iStartProof. iIntros "Hnext" (Hshape) "Hcaller34".
  iEval (rewrite <- instr_pre'_eq) in "Hnext".
  iApply (instr_pre_wand 0x150fc 0x150fc false true with "Hnext");
    [done | reflexivity |].
  iIntros "Hpost".
  iPoseProof (write_success_transactions_150fc_some_raw_return_adapter P
    sp base transaction transactions processed remaining bytes prefix suffix tail
    tagTail with "Hpost") as "Hraw".
  iSpecialize ("Hraw" with "[]"). { iPureIntro. exact Hshape. }
  iSpecialize ("Hraw" with "Hcaller34").
  iExact "Hraw".
Qed.
