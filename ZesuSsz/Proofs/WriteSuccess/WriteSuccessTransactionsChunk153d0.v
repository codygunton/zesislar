Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import
  Index HintsTransactionsLoop HintsBlobHashesLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCalls.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsAuthorizationsAdapter.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary153d0.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15564.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Ltac write_success_constant := vm_compute; repeat split; congruence.

Lemma write_success_fixed_width_count_bound
    (word : bv 64) (count : nat) :
  bv_unsigned word = Z.of_nat count -> (count < 2 ^ 64)%nat.
Proof.
  intro Hcount.
  have Hrange := bv_unsigned_in_range 64 word.
  rewrite Hcount in Hrange.
  unfold bv_modulus in Hrange.
  cbn in Hrange.
  apply (proj2 (Nat2Z.inj_lt count (2 ^ 64))).
  rewrite Nat2Z.inj_pow.
  exact (proj2 Hrange).
Qed.

Lemma write_success_sp_lower_bound (sp : bv 64) :
    ((mapRamBase defaultMap) <= bv_unsigned sp - 48)%Z ->
    ((mapRamBase defaultMap) <= bv_unsigned sp)%Z.
Proof.
  lia.
Qed.

Lemma write_success_transactions_chunk_153d0
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  □ instr_pre 0x153d4 (writeSuccessBlobHashesLoopSpec P) -∗
  instr_body 0x15564 (writeSuccessTransactionsAt15564Spec P) -∗
  instr_body 0x153d0 (writeSuccessTransactionsAt153d0Spec P).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode #Houtput #HblobLoop Hnext".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try (cbn; rewrite ?length_concat ?length_take ?length_drop; lia).
  all: try bv_solve.
  all: try lia.
  (* Keep the handoff resources grouped until the branch split. *)
  Unshelve. all: iIntros "HdataOwn".
  all: iIntros "HtransactionTail".
  all: iIntros "HremainingTail".
  all: iIntros "HPC".
  all: iDestruct "HtransactionTail" as "(HaccessOwn & HtransactionTail)".
  all: iDestruct "HtransactionTail" as "(HaccessEntriesOwn & HtransactionTail)".
  all: iDestruct "HtransactionTail" as "(HblobOwn & HtransactionTail)".
  all: iDestruct "HtransactionTail" as "(HauthOwn & HtransactionTail)".
  all: iDestruct "HtransactionTail" as "(%Hvalid & _)".
  all: iDestruct "HremainingTail" as "(Hremaining & HremainingTail)".
  all: iDestruct "HremainingTail" as "(Hmmio & HremainingTail)".
  all: iDestruct "HremainingTail" as "(Htrace & HremainingTail)".
  all: iDestruct "HremainingTail" as "(HP & HremainingTail)".
  all: iDestruct "HremainingTail" as "(#Hinvariant & HremainingTail)".
  all: iDestruct "HremainingTail" as "(Hexit & _)".
  all: iRename select
    ("x22" ↦ᵣ RVal_Bits
      (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 232))%I
    into "Hx22".
  all: iAssert (⌜WriteSuccessTransactionsSpec.writeSuccessTransactionValid
      transaction⌝)%I with "[]" as "HvalidKeep";
    [ iPureIntro; exact Hvalid | ].
  all: iAssert (WriteSuccessTransactionsSpec.writeSuccessTransactionOwn transaction)
    with "[HdataOwn HaccessOwn HaccessEntriesOwn HblobOwn HauthOwn HvalidKeep]"
    as "Htransaction";
    [ rewrite /WriteSuccessTransactionsSpec.writeSuccessTransactionOwn;
      iFrame "HdataOwn HaccessOwn HaccessEntriesOwn HblobOwn HauthOwn";
      iSplit; [iPureIntro; exact Hvalid | done]
    | ].
  all: iRename select (base ↦ₘ∗ prefix)%I into "Hprefix".
  all: iRename select
    ((base + 288 * length processed) ↦ₘ∗ suffix)%I into "Hsuffix".
  all: iRename select
    (WriteSuccessTransactionsSpec.writeSuccessTransactionsProcessedOwn processed)%I
    into "Hprocessed".
  destruct
    (WriteSuccessTransactionsSpec.writeSuccessTransactionBlobHashes transaction)
    as [|hash hashes] eqn:Hhashes.
  - have Hcount :
        bv_unsigned
          (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
            transaction 232) =
        Z.of_nat
          (length
            (WriteSuccessTransactionsSpec.writeSuccessTransactionBlobHashes
              transaction)).
    { unfold WriteSuccessTransactionsSpec.writeSuccessTransactionValid in Hvalid.
      naive_solver. }
    rewrite Hhashes /= in Hcount.
    have HwordZero :
        WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 232 =
        0%bv.
    { apply bv_eq. rewrite Z_to_bv_unsigned. cbn in Hcount. exact Hcount. }
    iEval (rewrite HwordZero) in "Hx22".
    liARun.
    all: liARun.
    all: try (cbn in H1; congruence).
    all: iRename select (reg_col zesu_ram_sys_regs)%I into "Hsys".
    all: iRename select ("x1" ↦ᵣ RVal_Bits (BV 64 0x153d0))%I into "Hx1".
    all: iRename select ("x2" ↦ᵣ RVal_Bits sp)%I into "Hx2".
    all: iRename select ("x5" ↦ᵣ RVal_Bits _)%I into "Hx5".
    all: iRename select ("x10" ↦ᵣ RVal_Bits (sp - BV 64 16)%bv)%I into "Hx10".
    all: iRename select ("x11" ↦ᵣ RVal_Bits (BV 64 8))%I into "Hx11".
    all: iRename select
      ("x19" ↦ᵣ RVal_Bits
        (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 224))%I
      into "Hx19".
    all: iExists
      (tail, suffix, prefix, bytes, remaining, processed, transactions,
        transaction, base, sp, tt)ₗ.
    all: iRename select (reg_col writeSuccessTransactions153d0OtherRegShapes)%I
      into "Hother".
    all: iEval (rewrite !reg_col_cons reg_col_nil) in "Hother".
    all: iDestruct "Hother" as
      "(H3 & H4 & H6 & H7 & H8 & H9 & H12 & H13 & H14 & H15 & H16 & H17 &
        H18 & H20 & H21 & H23 & H24 & H25 & H26 & H27 & H28 & H29 & H30 & H31 & _)".
    all: iRename select ((bv_unsigned sp - 48) ↦ₘ? 152)%I into "Hlower".
    all: iDestruct (mem_mapsto_uninit_split 16 with "Hlower") as
      "[Hlower16 HlowerRest]"; [lia|].
    all: iDestruct (mem_mapsto_uninit_split 32 with "HlowerRest") as
      "[Hmiddle Hupper104]"; [lia|].
    all: have HmiddleAddress :
      (bv_unsigned sp - 48 + 16 = bv_unsigned sp - 32)%Z by lia.
    all: iEval (rewrite HmiddleAddress) in "Hmiddle".
    all: have Hupper104Address :
      (bv_unsigned sp - 48 + 16 + 32 = bv_unsigned sp)%Z by lia.
    all: iEval (rewrite Hupper104Address) in "Hupper104".
    all: have Hupper104Size : (152 - 16 - 32 = 104)%Z by lia.
    all: iEval (rewrite Hupper104Size) in "Hupper104".
    all: iRename select ((bv_unsigned sp + 280) ↦ₘ? 1616)%I into "Hupper".
    all: iDestruct (mem_mapsto_uninit_split 1400 with "Hupper") as
      "[Hstack1400 HupperRest]"; [lia|].
    all: iDestruct (mem_mapsto_uninit_split 32 with "HupperRest") as
      "[Hstack1680 Hstack1712]"; [lia|].
    all: have Hstack1680Address :
      (bv_unsigned sp + 280 + 1400 = bv_unsigned sp + 1680)%Z by lia.
    all: iEval (rewrite Hstack1680Address) in "Hstack1680".
    all: have Hstack1712Address :
      (bv_unsigned sp + 280 + 1400 + 32 = bv_unsigned sp + 1712)%Z by lia.
    all: iEval (rewrite Hstack1712Address) in "Hstack1712".
    all: have Hstack1712Size : (1616 - 1400 - 32 = 184)%Z by lia.
    all: iEval (rewrite Hstack1712Size) in "Hstack1712".
    all: iRename select
      ((bv_unsigned sp + 104) ↦ₘ Z_to_bv 64 base)%I into "Hm104".
    all: iRename select
      ((bv_unsigned sp + 112) ↦ₘ Z_to_bv 64 (length transactions))%I
      into "Hm112".
    all: iRename select
      ((bv_unsigned sp + 120) ↦ₘ
        bv_zero_extend 64
          (WriteSuccessTransactionsSpec.writeSuccessTransactionByte transaction 285))%I
      into "Hm120".
    all: iRename select
      ((bv_unsigned sp + 128) ↦ₘ
        WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 64)%I
      into "Hm128".
    all: iRename select
      ((bv_unsigned sp + 136) ↦ₘ
        WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 232)%I
      into "Hm136".
    all: iRename select
      ((bv_unsigned sp + 144) ↦ₘ
        WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 88)%I
      into "Hm144".
    all: iRename select
      ((bv_unsigned sp + 152) ↦ₘ
        WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 80)%I
      into "Hm152".
    all: iRename select
      ((bv_unsigned sp + 160) ↦ₘ
        WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 248)%I
      into "Hm160".
    all: iRename select
      ((bv_unsigned sp + 168) ↦ₘ
        WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 240)%I
      into "Hm168".
    all: iRename select
      ((bv_unsigned sp + 176) ↦ₘ
        WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 256)%I
      into "Hm176".
    all: iRename select
      ((bv_unsigned sp + 184) ↦ₘ
        WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 120)%I
      into "Hm184".
    all: iRename select
      ((bv_unsigned sp + 192) ↦ₘ
        WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 112)%I
      into "Hm192".
    all: iRename select
      ((bv_unsigned sp + 200) ↦ₘ
        WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 104)%I
      into "Hm200".
    all: iRename select
      ((bv_unsigned sp + 208) ↦ₘ
        WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 128)%I
      into "Hm208".
    all: iRename select
      ((bv_unsigned sp + 216) ↦ₘ
        WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 96)%I
      into "Hm216".
    all: iRename select
      ((bv_unsigned sp + 224) ↦ₘ
        WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 152)%I
      into "Hm224".
    all: iRename select
      ((bv_unsigned sp + 232) ↦ₘ
        WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 144)%I
      into "Hm232".
    all: iRename select
      ((bv_unsigned sp + 240) ↦ₘ
        WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 136)%I
      into "Hm240".
    all: iRename select
      ((bv_unsigned sp + 248) ↦ₘ Z_to_bv 64 (length processed))%I
      into "Hm248".
    all: iRename select
      ((bv_unsigned sp + 256) ↦ₘ
        WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 208)%I
      into "Hm256".
    all: iRename select
      ((bv_unsigned sp + 264) ↦ₘ
        WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 216)%I
      into "Hm264".
    all: iRename select ((bv_unsigned sp + 272) ↦ₘ? 8)%I into "Hm272".
    all: iRename select ("x22" ↦ᵣ RVal_Bits 0%bv)%I into "Hx22Final".
    all: have Hpointer :
      bv_unsigned
        (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 224) =
      (bv_unsigned
        (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 224) +
       32 * length
           (WriteSuccessTransactionsSpec.writeSuccessTransactionBlobHashes
           transaction))%Z.
    { rewrite Hhashes /=. lia. }
    all: iPoseProof "Hinvariant" as "HfactsCopy".
    all: iDestruct "HfactsCopy" as
      "(%Htransactions & %Hbytes & %Hprefix & %Hsuffix & %HbytesApp &
        %HbytesLength & %HprefixLength & %HsuffixLength & %HtransactionsBound &
        %HspAlign & %HspLower & %HspUpper & %HbaseAlign & %HbaseLower &
        %HbaseUpper & _)".
    all: have HspAlign8 : (bv_unsigned sp `mod` 8 = 0)%Z.
    { have Hneq8 : (8:Z) <> 0%Z.
      { intro Hz. discriminate Hz. }
      apply (proj2 (Z.mod_divide (bv_unsigned sp) 8 Hneq8)).
      have Hdiv16 : (16 | bv_unsigned sp)%Z.
      { have Hneq16 : (16:Z) <> 0%Z.
        { intro Hz. discriminate Hz. }
        apply (proj1 (Z.mod_divide (bv_unsigned sp) 16 Hneq16)).
        exact HspAlign. }
      destruct Hdiv16 as [factor Hfactor].
      exists (2 * factor)%Z.
      rewrite Hfactor.
      ring. }
    all: iAssert (reg_col writeSuccessTransactions15564OtherRegShapes)
      with "[Hx1 Hx5 Hx10 Hx11 H3 H4 H6 H7 H8 H9 H12 H13 H14 H15 H16 H17
        H18 H20 H21 H23 H24 H25 H26 H27 H28 H29 H30 H31]" as "HtargetRegs".
    { rewrite !reg_col_cons reg_col_nil.
      iFrame.
      repeat iSplit; try iPureIntro; try done; try bv_solve. }
    all: iAssert
      (writeSuccessTransactionsMachine15564
        sp base transactions processed transaction)
      with "[Hsys HtargetRegs Hx2 Hx19 Hx22Final Hlower16 Hmiddle Hupper104
        Hm104 Hm112 Hm120 Hm128 Hm136 Hm144 Hm152 Hm160 Hm168 Hm176 Hm184
        Hm192 Hm200 Hm208 Hm216 Hm224 Hm232 Hm240 Hm248 Hm256 Hm264 Hm272
        Hstack1400 Hstack1680 Hstack1712]" as "Hmachine".
    { rewrite /writeSuccessTransactionsMachine15564
        /writeSuccessTransactionsScratch15564
        /writeSuccessTransactionsScratch15564Frame.
      iExists
        (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 224).
      iFrame "Hsys HtargetRegs Hx2 Hx19 Hlower16 Hmiddle Hupper104
        Hx22Final Hm104 Hm112 Hm120 Hm128 Hm136 Hm144 Hm152 Hm160 Hm168
        Hm176 Hm184 Hm192 Hm200 Hm208 Hm216 Hm224 Hm232 Hm240 Hm248 Hm256
        Hm264 Hm272 Hstack1400 Hstack1680 Hstack1712".
      repeat iSplit.
      - iPureIntro. exact HspAlign.
      - iPureIntro. exact HspAlign8.
      - iPureIntro. exact HspLower.
      - iPureIntro. exact HspUpper.
      - iPureIntro. exact Hpointer.
      - done. }
    all: rewrite /WriteSuccessTransactionsSpec.writeSuccessTransactionPhaseHandoff.
    all: rewrite /WriteSuccessTransactionsSpec.writeSuccessTransactionPhaseEvents /=.
    all: iFrame
      "Hmachine Hprefix Hsuffix Hprocessed Htransaction Hremaining Hmmio Htrace
       HP Hinvariant Hexit".
    all: done.
  - have Hcount :
        bv_unsigned
          (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
            transaction 232) =
        Z.of_nat
          (length
            (WriteSuccessTransactionsSpec.writeSuccessTransactionBlobHashes
              transaction)).
    { unfold WriteSuccessTransactionsSpec.writeSuccessTransactionValid in Hvalid.
      naive_solver. }
    have HwordNonzero :
        WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 232 <>
        0%bv.
    { intro Hword. rewrite Hword bv_unsigned_BV in Hcount.
      rewrite Hhashes /= in Hcount. lia. }
    rewrite Hhashes /= in Hcount.
    have HwordCount :
        WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 232 =
        Z_to_bv 64 (Z.of_nat (S (length hashes))).
    { apply bv_eq. rewrite Z_to_bv_unsigned.
      rewrite (bv_wrap_small 64 (Z.of_nat (S (length hashes)))).
      - exact Hcount.
      - have HcountRange := bv_unsigned_in_range 64
          (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 232).
        rewrite Hcount in HcountRange.
        cbn in HcountRange. lia. }
    liARun.
    + exfalso. apply HwordNonzero. exact H1.
    + iExists
        (WriteSuccessTransactionsSpec.writeSuccessTransactionPhaseEvents
           WriteSuccessTransactionsSpec.TransactionMaxFeePerBlobGas sp transaction
           (WriteSuccessTransactionsSpec.writeSuccessTransactionsEvents
              sp remaining tail),
         WriteSuccessTransactionsSpec.writeSuccessTransactionBlobBytes transaction,
         length hashes, O, S (length hashes),
         bv_unsigned
           (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 224),
         tt)ₗ.
      liARun.
    Unshelve.
    all: try prepare_sidecond.
    all: try assumption.
    all: try (cbn; rewrite ?length_concat ?length_take ?length_drop; lia).
    all: try bv_solve.
  all: try exact HwordCount.
  all: try lia.
  all: try iFrame.
  all: exact HwordCount.
  Unshelve.
  iRename select ((bv_unsigned sp + 280) ↦ₘ? 1616)%I into "Hupper".
  iDestruct (mem_mapsto_uninit_split 1400 with "Hupper") as
    "[Hstack1400 HupperRest]"; [lia|].
  iDestruct (mem_mapsto_uninit_split 32 with "HupperRest") as
    "[Hscratch32 Hstack1712]"; [lia|].
  have HscratchAddress :
      (bv_unsigned sp + 280 + 1400 = bv_unsigned sp + 1680)%Z by lia.
  iEval (rewrite HscratchAddress) in "Hscratch32".
  iAssert (WriteSuccessBlobHashesSpec.writeSuccessBlobHashesScratch sp)
    with "[Hscratch32]" as "HblobScratch".
  {
    rewrite /WriteSuccessBlobHashesSpec.writeSuccessBlobHashesScratch.
    iDestruct (mem_mapsto_uninit_split 8 with "Hscratch32") as
      "[H1680 HscratchRest]"; [lia|].
    have H1688Address :
        (bv_unsigned sp + 1680 + 8 = bv_unsigned sp + 1688)%Z by lia.
    iEval (rewrite H1688Address) in "HscratchRest".
    iDestruct (mem_mapsto_uninit_split 8 with "HscratchRest") as
      "[H1688 HscratchRest]"; [lia|].
    have H1696Address :
        (bv_unsigned sp + 1688 + 8 = bv_unsigned sp + 1696)%Z by lia.
    iEval (rewrite H1696Address) in "HscratchRest".
    iDestruct (mem_mapsto_uninit_split 8 with "HscratchRest") as
      "[H1696 H1704]"; [lia|].
    have H1704Address :
        (bv_unsigned sp + 1696 + 8 = bv_unsigned sp + 1704)%Z by lia.
    iEval (rewrite H1704Address) in "H1704".
    iDestruct (mem_mapsto_uninit_to_mapsto with "H1680") as
      (n0 word0 Hn0) "H1680".
    iDestruct (mem_mapsto_uninit_to_mapsto with "H1688") as
      (n1 word1 Hn1) "H1688".
    iDestruct (mem_mapsto_uninit_to_mapsto with "H1696") as
      (n2 word2 Hn2) "H1696".
    iDestruct (mem_mapsto_uninit_to_mapsto with "H1704") as
      (n3 word3 Hn3) "H1704".
    cbn in Hn0, Hn1, Hn2, Hn3.
    subst n0 n1 n2 n3.
    iExists word0, word1, word2, word3.
    iFrame.
  }
  iEval (unfold WriteSuccessTransactionsSpec.writeSuccessTransactionOwn)
    in "Htransaction".
  iDestruct "Htransaction" as
    "(HdataOwn & HaccessOwn & HaccessEntriesOwn & HblobOwn & HauthOwn &
      %HtransactionValid & _)".
  iEval (unfold WriteSuccessTransactionsSpec.writeSuccessByteArrayOwn)
    in "HblobOwn".
  iEval (unfold WriteSuccessTransactionsSpec.writeSuccessTransactionBlobBytes)
    in "HblobOwn".
  iEval (rewrite Hhashes) in "HblobOwn".
  have Hforall :
      Forall (fun hash => length hash = 32%nat)
        (WriteSuccessTransactionsSpec.writeSuccessTransactionBlobHashes transaction).
  { unfold WriteSuccessTransactionsSpec.writeSuccessTransactionValid in HtransactionValid.
    repeat match type of HtransactionValid with
    | _ /\ _ => destruct HtransactionValid as [? HtransactionValid]
    end.
    assumption. }
  have HhashLength : length hash = 32%nat.
  { rewrite Hhashes in Hforall. inversion Hforall. assumption. }
  destruct hash as [|h hash].
  * cbn in HhashLength. lia.
  * iEval (cbn) in "HblobOwn".
  have HblobBytesEq :
      WriteSuccessTransactionsSpec.writeSuccessTransactionBlobBytes transaction =
      h :: hash ++ concat hashes.
  { unfold WriteSuccessTransactionsSpec.writeSuccessTransactionBlobBytes.
    rewrite Hhashes. cbn. reflexivity. }
  iEval (rewrite <- HblobBytesEq) in "HblobOwn".
  have HblobPointer :
      WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 224 =
      WriteSuccessTransactionsSpec.writeSuccessTransactionBlobPointer transaction.
  { unfold WriteSuccessTransactionsSpec.writeSuccessTransactionValid in HtransactionValid.
    naive_solver. }
  iEval (rewrite <- HblobPointer) in "HblobOwn".
  iDestruct "HblobOwn" as "(HblobBytes & %HblobLower & %HblobUpper & _)".
  iFrame "HblobBytes HblobScratch Hmmio Htrace HP".
  iPoseProof "Hinvariant" as "HfactsCopy".
  iDestruct "HfactsCopy" as
    "(%Htransactions & %Hbytes & %HprefixEq & %HsuffixEq & %HbytesApp &
      %HbytesLengthInv & %HprefixLength & %HsuffixLength & %HtransactionsBound &
      %HspAlign & %HspLower & %HspUpper & %HbaseAlign & %HbaseLower &
      %HbaseUpper & _)".
  have Hforall' := Hforall.
  rewrite Hhashes in Hforall'.
  have HblobLength :
      length (WriteSuccessTransactionsSpec.writeSuccessTransactionBlobBytes transaction) =
      (32 * S (length hashes))%nat.
  { unfold WriteSuccessTransactionsSpec.writeSuccessTransactionBlobBytes.
    rewrite Hhashes.
    apply write_success_fixed_lists_concat_length.
    exact Hforall'. }
  have HremainingBound : (S (length hashes) < 2 ^ 64)%nat.
  { apply (write_success_fixed_width_count_bound
      (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 232)
      (S (length hashes))).
    exact Hcount. }
  have HblobUpper' :
      bv_unsigned
        (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 224) +
      length (WriteSuccessTransactionsSpec.writeSuccessTransactionBlobBytes transaction) <
      (machineRamEnd defaultMap).
  { rewrite HblobBytesEq. exact HblobUpper. }
  iAssert
    (WriteSuccessLoopCommon.writeSuccessFixedWidthArrayInvariant
      sp (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 224)
      (bv_unsigned
        (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 224))
      (S (length hashes)) 0 (length hashes)
      (WriteSuccessTransactionsSpec.writeSuccessTransactionBlobBytes transaction))
    with "[]" as "Hfixed".
  { rewrite /WriteSuccessLoopCommon.writeSuccessFixedWidthArrayInvariant.
    repeat iSplit.
    - iPureIntro. cbn. reflexivity.
    - iPureIntro. exact HblobLength.
    - iPureIntro. cbn. ring.
    - iPureIntro. exact HremainingBound.
    - iPureIntro. exact HspAlign.
    - iPureIntro. apply write_success_sp_lower_bound. exact HspLower.
    - iPureIntro. exact HspUpper.
    - iPureIntro. exact HblobLower.
    - iPureIntro. exact HblobUpper'.
    - done. }
  iFrame "Hfixed".
  iFrame.
  iApply (bi.sep_True_2).
  iApply (instr_pre_wand 87396 87396 false true with "Hnext");
    [done | done |].
  iIntros "(%pointer & HsysLoop & HregsLoop & H2Loop & H19Loop & H22Loop &
    HbaseBytesLoop & HblobScratchLoop & HmmioLoop & HtraceLoop & HPLoop &
    %HpointerLoop & _)".
  have HpointerTarget :
      bv_unsigned pointer =
      (bv_unsigned
        (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 224) +
       32 * Z.of_nat
         (length
           (WriteSuccessTransactionsSpec.writeSuccessTransactionBlobHashes transaction)))%Z.
  { rewrite Hhashes. cbn. exact HpointerLoop. }
  iRename select ((bv_unsigned sp - 48) ↦ₘ? 152)%I into "Hlower".
  iDestruct (mem_mapsto_uninit_split 16 with "Hlower") as
    "[Hlower16 HlowerRest]"; [write_success_constant|].
  iDestruct (mem_mapsto_uninit_split 32 with "HlowerRest") as
    "[Hmiddle Hupper104]"; [write_success_constant|].
  have HmiddleAddress :
      (bv_unsigned sp - 48 + 16 = bv_unsigned sp - 32)%Z by ring.
  iEval (rewrite HmiddleAddress) in "Hmiddle".
  have Hupper104Address :
      (bv_unsigned sp - 48 + 16 + 32 = bv_unsigned sp)%Z by ring.
  iEval (rewrite Hupper104Address) in "Hupper104".
  have Hupper104Size : (152 - 16 - 32 = 104)%Z by (vm_compute; reflexivity).
  iEval (rewrite Hupper104Size) in "Hupper104".
  have Hstack1712Address :
      (bv_unsigned sp + 280 + 1400 + 32 = bv_unsigned sp + 1712)%Z by ring.
  iEval (rewrite Hstack1712Address) in "Hstack1712".
  have Hstack1712Size : (1616 - 1400 - 32 = 184)%Z by (vm_compute; reflexivity).
  iEval (rewrite Hstack1712Size) in "Hstack1712".
  iAssert ((bv_unsigned sp + 1680) ↦ₘ? 32)%I
    with "[HblobScratchLoop]" as "Hscratch1680".
  {
    rewrite /WriteSuccessBlobHashesSpec.writeSuccessBlobHashesScratch.
    iEval (unfold WriteSuccessBlobHashesSpec.writeSuccessBlobHashesScratch)
      in "HblobScratchLoop".
    iDestruct "HblobScratchLoop" as
      "(%word0 & %word1 & %word2 & %word3 & H1680 & H1688 & H1696 & H1704 & _)".
    have H1688Address :
        (bv_unsigned sp + 1680 + 8 = bv_unsigned sp + 1688)%Z by ring.
    iEval (rewrite <- H1688Address) in "H1688".
    have H1696Address :
        (bv_unsigned sp + 1680 + 8 + 8 = bv_unsigned sp + 1696)%Z by ring.
    iEval (rewrite <- H1696Address) in "H1696".
    have H1704Address :
        (bv_unsigned sp + 1680 + 8 + 8 + 8 = bv_unsigned sp + 1704)%Z by ring.
    iEval (rewrite <- H1704Address) in "H1704".
    iAssert ((bv_unsigned sp + 1680) ↦ₘ? 8)%I
      with "[H1680]" as "H1680u".
    { iApply (mem_mapsto_mapsto_to_uninit _ _ 64 with "H1680"). }
    iAssert ((bv_unsigned sp + 1680 + 8) ↦ₘ? 8)%I
      with "[H1688]" as "H1688u".
    { iApply (mem_mapsto_mapsto_to_uninit _ _ 64 with "H1688"). }
    iAssert ((bv_unsigned sp + 1680 + 8 + 8) ↦ₘ? 8)%I
      with "[H1696]" as "H1696u".
    { iApply (mem_mapsto_mapsto_to_uninit _ _ 64 with "H1696"). }
    iAssert ((bv_unsigned sp + 1680 + 8 + 8 + 8) ↦ₘ? 8)%I
      with "[H1704]" as "H1704u".
    { iApply (mem_mapsto_mapsto_to_uninit _ _ 64 with "H1704"). }
    iAssert ((bv_unsigned sp + 1680 + 8 + 8) ↦ₘ? 16)%I
      with "[H1696u H1704u]" as "Htail16".
    {
      iApply (mem_mapsto_uninit_combine 8 with "[H1696u] [H1704u]");
        [write_success_constant | iExact "H1696u" | iExact "H1704u"].
    }
    iAssert ((bv_unsigned sp + 1680 + 8) ↦ₘ? 24)%I
      with "[H1688u Htail16]" as "Htail24".
    {
      iApply (mem_mapsto_uninit_combine 8 with "[H1688u] [Htail16]");
        [write_success_constant | iExact "H1688u" | iExact "Htail16"].
    }
    iApply (mem_mapsto_uninit_combine 8 with "[H1680u] [Htail24]");
      [write_success_constant | iExact "H1680u" | iExact "Htail24"].
  }
  iAssert (WriteSuccessTransactionsSpec.writeSuccessByteArrayOwn
      (WriteSuccessTransactionsSpec.writeSuccessTransactionBlobPointer transaction)
      (WriteSuccessTransactionsSpec.writeSuccessTransactionBlobBytes transaction))
    with "[HbaseBytesLoop]" as "HblobOwnRestore".
  {
    rewrite /WriteSuccessTransactionsSpec.writeSuccessByteArrayOwn.
    rewrite HblobBytesEq. cbn.
    rewrite <- HblobPointer.
    iFrame "HbaseBytesLoop".
    iSplit; [iPureIntro; exact HblobLower|].
    iSplit; [iPureIntro; exact HblobUpper|done].
  }
  iAssert (WriteSuccessTransactionsSpec.writeSuccessTransactionOwn transaction)
    with "[HdataOwn HaccessOwn HaccessEntriesOwn HblobOwnRestore HauthOwn HvalidKeep]"
    as "HtransactionRestore".
  {
    rewrite /WriteSuccessTransactionsSpec.writeSuccessTransactionOwn.
    iFrame "HdataOwn HaccessOwn HaccessEntriesOwn HblobOwnRestore HauthOwn".
    iSplit; [iPureIntro; exact Hvalid|done].
  }
  iAssert (reg_col writeSuccessTransactions15564OtherRegShapes)
    with "[HregsLoop]" as "HtargetRegs".
  { iExact "HregsLoop". }
  iRename select ((bv_unsigned sp + 104) ↦ₘ Z_to_bv 64 base)%I into "Hm104".
  iRename select
    ((bv_unsigned sp + 112) ↦ₘ Z_to_bv 64 (length transactions))%I
    into "Hm112".
  iRename select
    ((bv_unsigned sp + 120) ↦ₘ
      bv_zero_extend 64
        (WriteSuccessTransactionsSpec.writeSuccessTransactionByte transaction 285))%I
    into "Hm120".
  iRename select
    ((bv_unsigned sp + 128) ↦ₘ
      WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 64)%I
    into "Hm128".
  iRename select
    ((bv_unsigned sp + 136) ↦ₘ
      WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 232)%I
    into "Hm136".
  iRename select
    ((bv_unsigned sp + 144) ↦ₘ
      WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 88)%I
    into "Hm144".
  iRename select
    ((bv_unsigned sp + 152) ↦ₘ
      WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 80)%I
    into "Hm152".
  iRename select
    ((bv_unsigned sp + 160) ↦ₘ
      WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 248)%I
    into "Hm160".
  iRename select
    ((bv_unsigned sp + 168) ↦ₘ
      WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 240)%I
    into "Hm168".
  iRename select
    ((bv_unsigned sp + 176) ↦ₘ
      WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 256)%I
    into "Hm176".
  iRename select
    ((bv_unsigned sp + 184) ↦ₘ
      WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 120)%I
    into "Hm184".
  iRename select
    ((bv_unsigned sp + 192) ↦ₘ
      WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 112)%I
    into "Hm192".
  iRename select
    ((bv_unsigned sp + 200) ↦ₘ
      WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 104)%I
    into "Hm200".
  iRename select
    ((bv_unsigned sp + 208) ↦ₘ
      WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 128)%I
    into "Hm208".
  iRename select
    ((bv_unsigned sp + 216) ↦ₘ
      WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 96)%I
    into "Hm216".
  iRename select
    ((bv_unsigned sp + 224) ↦ₘ
      WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 152)%I
    into "Hm224".
  iRename select
    ((bv_unsigned sp + 232) ↦ₘ
      WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 144)%I
    into "Hm232".
  iRename select
    ((bv_unsigned sp + 240) ↦ₘ
      WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 136)%I
    into "Hm240".
  iRename select ((bv_unsigned sp + 248) ↦ₘ Z_to_bv 64 (length processed))%I
    into "Hm248".
  iRename select
    ((bv_unsigned sp + 256) ↦ₘ
      WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 208)%I
    into "Hm256".
  iRename select
    ((bv_unsigned sp + 264) ↦ₘ
      WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 216)%I
    into "Hm264".
  iRename select ((bv_unsigned sp + 272) ↦ₘ? 8)%I into "Hm272".
  iAssert
    (writeSuccessTransactionsMachine15564
      sp base transactions processed transaction)
    with "[HsysLoop HtargetRegs H2Loop H19Loop H22Loop Hlower16 Hmiddle Hupper104
      Hm104 Hm112 Hm120 Hm128 Hm136 Hm144 Hm152 Hm160 Hm168 Hm176 Hm184
      Hm192 Hm200 Hm208 Hm216 Hm224 Hm232 Hm240 Hm248 Hm256 Hm264 Hm272
      Hstack1400 Hscratch1680 Hstack1712]" as "Hmachine".
  {
    rewrite /writeSuccessTransactionsMachine15564
      /writeSuccessTransactionsScratch15564
      /writeSuccessTransactionsScratch15564Frame.
    iExists pointer.
    iFrame "HsysLoop HtargetRegs H2Loop H19Loop H22Loop Hlower16 Hmiddle Hupper104
      Hm104 Hm112 Hm120 Hm128 Hm136 Hm144 Hm152 Hm160 Hm168 Hm176 Hm184
      Hm192 Hm200 Hm208 Hm216 Hm224 Hm232 Hm240 Hm248 Hm256 Hm264 Hm272
      Hstack1400 Hscratch1680 Hstack1712".
    repeat iSplit.
    - iPureIntro. exact HspAlign.
    - iPureIntro.
      have Hneq8 : (8:Z) <> 0%Z by discriminate.
      apply (proj2 (Z.mod_divide (bv_unsigned sp) 8 Hneq8)).
      have Hdiv16 : (16 | bv_unsigned sp)%Z.
      { have Hneq16 : (16:Z) <> 0%Z by discriminate.
        apply (proj1 (Z.mod_divide (bv_unsigned sp) 16 Hneq16)).
        exact HspAlign. }
      destruct Hdiv16 as [factor Hfactor].
      exists (2 * factor)%Z. rewrite Hfactor. ring.
    - iPureIntro. exact HspLower.
    - iPureIntro. exact HspUpper.
    - iPureIntro. exact HpointerTarget.
    - done. }
  iExists sp, base, transaction, transactions, processed, remaining,
    bytes, prefix, suffix,
    tail.
  rewrite /WriteSuccessTransactionsSpec.writeSuccessTransactionPhaseHandoff.
  rewrite /WriteSuccessTransactionsSpec.writeSuccessTransactionPhaseEvents /=.
  iFrame "Hmachine Hprefix Hsuffix Hprocessed HtransactionRestore Hremaining
    HmmioLoop HtraceLoop HPLoop Hinvariant Hexit".
Qed.
