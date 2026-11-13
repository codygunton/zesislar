Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import List ZArith.
From stdpp Require Import base list bitvector.definitions.
Require Import ZesuMachineMap.Machine.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.ParentHeader.
Require Import ZesuSsz.Contracts.ParentHeaderRootFacts.
Require Import ZesuSsz.Contracts.NextUint64BlockEntries.
Require Import ZesuSsz.Contracts.NextUint64Selected.
Require Import ZesuSsz.Contracts.NextUint64Contract.
Require Import ZesuSsz.Contracts.NextUint64CallSpec2.
Require Import ZesuSsz.Contracts.NextUint64DomainRanges.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Contracts.AbiBytes.
Import ListNotations.
Open Scope Z_scope.
Open Scope stdpp_scope.

(* The slice is two 64-bit words; the contract states it as 16 bytes. *)
Lemma nextUint64_word_to_bytes `{!islaG Sigma} (address : Z) (word : bv 64) :
  address ↦ₘ word -∗ address ↦ₘ∗ word64Bytes (bv_unsigned word).
Proof.
  iIntros "Hword".
  iDestruct (mem_mapsto_mapsto_to_byte_array_len 8 address _ word with "Hword")
    as "Hbytes".
  rewrite nextUint64Word64BytesEncoding. iExact "Hbytes".
Qed.

Lemma nextUint64_bytes_to_word `{!islaG Sigma} (address value : Z) :
  address ↦ₘ∗ word64Bytes value -∗ address ↦ₘ Z_to_bv 64 value.
Proof.
  iIntros "Hbytes".
  iDestruct (mem_mapsto_byte_array_to_mapsto_len 8 address _ (word64Bytes value)
    with "Hbytes") as "Hword"; [reflexivity |].
  rewrite -nextUint64Word64BytesEncoding little_endian_to_bv_to_little_endian;
    [| lia].
  have -> : Z_to_bv (8 * N.of_nat 8) (value `mod` 2 ^ (8 * Z.of_N 8)) =
    Z_to_bv 64 value.
  { apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
    cbn. apply Z.mod_mod. lia. }
  iExact "Hword".
Qed.

Lemma nextUint64_words_to_slice `{!islaG Sigma} (address : Z)
    (pointer length : bv 64) :
  address ↦ₘ pointer -∗ (address + 8) ↦ₘ length -∗
  address ↦ₘ∗ nextUint64SliceImage (bv_unsigned pointer) (bv_unsigned length).
Proof.
  iIntros "Hpointer Hlength". unfold nextUint64SliceImage.
  iDestruct (nextUint64_word_to_bytes with "Hpointer") as "Hpointer".
  iDestruct (nextUint64_word_to_bytes with "Hlength") as "Hlength".
  have Hnext : address + 8 = address + Z.of_N (8 `div` 8) * Z.of_nat 8
    by cbn; lia.
  iEval (rewrite Hnext) in "Hlength".
  iApply (mem_mapsto_array_app_combine_at 8 address _ _ _ 8
    with "Hpointer Hlength").
  reflexivity.
Qed.

Lemma nextUint64_slice_to_words `{!islaG Sigma} (address pointer length : Z) :
  address ↦ₘ∗ nextUint64SliceImage pointer length -∗
  address ↦ₘ Z_to_bv 64 pointer ∗ (address + 8) ↦ₘ Z_to_bv 64 length.
Proof.
  iIntros "Hslice". unfold nextUint64SliceImage.
  iDestruct (mem_mapsto_array_app with "Hslice") as "[Hpointer Hlength]".
  have Hnext : address + Z.of_N (8 `div` 8) *
      Z.of_nat (length (word64Bytes pointer)) = address + 8
    by cbn; lia.
  iEval (rewrite Hnext) in "Hlength".
  iSplitL "Hpointer"; by iApply nextUint64_bytes_to_word.
Qed.

(* nextUint64CallSpec2 follows from the compositional theorem
   NextUint64ContractCorrect: the call boundary supplies its entry, and its
   exit supplies the return boundary. *)
Lemma nextUint64CallSpec2_correct `{!islaG Sigma} `{!threadG} :
  NextUint64ContractCorrect ->
  nextUint64SelectedCode -∗ instr_body nextUint64Entry nextUint64CallSpec2.
Proof.
  intros Hcontract.
  iStartProof. iIntros "Hcode".
  rewrite instr_pre'_eq /instr_pre'_def /=.
  iIntros "Hspec".
  iEval (unfold nextUint64CallSpec2) in "Hspec".
  zesu_unpack_call "Hspec".
  subst r10 r11 r12 r13 r14 r15 r16 r17.
  iDestruct "Hrest" as (inputPointer inputLength inputEndBits input)
    "(Hend & Hfree & HsliceP & HsliceL & Hinput & Hresult & %Hlength & %Hdomain & Hret)".
  destruct (valu_has_bits_shape r8 64 Hr8) as [b8 ->].
  destruct (valu_has_bits_shape r9 64 Hr9) as [b9 ->].
  destruct (valu_has_bits_shape r18 64 Hr18) as [b18 ->].
  destruct (valu_has_bits_shape r19 64 Hr19) as [b19 ->].
  destruct (valu_has_bits_shape r20 64 Hr20) as [b20 ->].
  destruct (valu_has_bits_shape r21 64 Hr21) as [b21 ->].
  destruct (valu_has_bits_shape r22 64 Hr22) as [b22 ->].
  destruct (valu_has_bits_shape r23 64 Hr23) as [b23 ->].
  destruct (valu_has_bits_shape r24 64 Hr24) as [b24 ->].
  destruct (valu_has_bits_shape r25 64 Hr25) as [b25 ->].
  destruct (valu_has_bits_shape r26 64 Hr26) as [b26 ->].
  destruct (valu_has_bits_shape r27 64 Hr27) as [b27 ->].
  iEval (cbn [lookup_total list_lookup_total]) in "HsliceP HsliceL Hresult Hret".
  iDestruct (nextUint64_words_to_slice with "HsliceP HsliceL") as "Hslice".
  set (base := {| nextInputPointer := bv_unsigned inputPointer;
    nextInputBytes := input;
    nextSlicePointer := bv_unsigned b11;
    nextResultPointer := bv_unsigned b10;
    nextStackPointer := bv_unsigned sp;
    nextReturnAddress := bv_unsigned ret;
    nextSavedS0 := b8; nextSavedS1 := b9; nextSavedS2 := b18;
    nextSavedS3 := b19; nextSavedS4 := b20 |}).
  set (params := {| nextUint64Base := base;
    nextUint64InputEnd := bv_unsigned inputEndBits;
    nextUint64SavedX21 := b21; nextUint64SavedX22 := b22;
    nextUint64SavedX23 := b23; nextUint64SavedX24 := b24;
    nextUint64SavedX25 := b25; nextUint64SavedX26 := b26;
    nextUint64SavedX27 := b27 |}).
  have Hretalign : bv_unsigned ret `mod` 4 = 0.
  { pose proof (f_equal (@bv_unsigned 2) Hret2) as Hbits.
    rewrite bv_extract_unsigned in Hbits.
    change (bv_unsigned ret `mod` 4 = 0) in Hbits.
    exact Hbits. }
  have Hrange : 0 <= bv_unsigned ret < word64Modulus.
  { pose proof (bv_unsigned_in_range 64 ret) as Hrange.
    change (0 <= bv_unsigned ret < word64Modulus) in Hrange.
    exact Hrange. }
  have HactualDomain : nextUint64BoundaryDomain params.
  { unfold nextUint64BoundaryDomain in Hdomain |- *.
    cbn in Hdomain |- *.
    destruct Hdomain as [Hlayout Hrest].
    split; [| exact Hrest].
    unfold nextUint64EntryLayout in Hlayout |- *.
    clear - Hlayout Hrange Hretalign.
    repeat split; first [tauto | lia]. }
  pose proof (Hcontract (bv_unsigned ret) Sigma islaG0 H) as Hcorrect.
  unfold IslarisContractSpec in Hcorrect.
  cbn [nextUint64ContractModel nextUint64ContractResources] in Hcorrect.
  iPoseProof (Hcorrect with "Hcode") as "Hbody".
  iSpecialize ("Hbody" $! params).
  iEval (rewrite {1}instr_pre'_eq /instr_pre'_def /=) in "Hbody".
  iApply "Hbody".
  iAssert (reg_col (nextUint64SysRegs params)) with "[Hsys Hend Hfree]"
    as "Hsys".
  { rewrite /nextUint64SysRegs decodeItemSysRegs_exact /reg_col big_sepL_app.
    fold (reg_col (machine_static_sys_regs defaultMap)).
    iFrame "Hsys". rewrite reg_col_cons.
    iSplitL "Hend".
    { iExists (RVal_Bits inputEndBits).
      cbn. rewrite Z_to_bv_bv_unsigned. iFrame. done. }
    iExact "Hfree". }
  iEval (rewrite /tmp_registers !reg_col_cons reg_col_nil) in "Htmp".
  iDestruct "Htmp" as "(T5 & T6 & T7 & T28 & T29 & T30 & T31 & _)".
  iDestruct "T5" as (v5 Hshape5) "R5".
  destruct (valu_has_bits_shape v5 64 Hshape5) as [b5 ->].
  iDestruct "T6" as (v6 Hshape6) "R6".
  destruct (valu_has_bits_shape v6 64 Hshape6) as [b6 ->].
  iDestruct "T7" as (v7 Hshape7) "R7".
  destruct (valu_has_bits_shape v7 64 Hshape7) as [b7 ->].
  iDestruct "T28" as (v28 Hshape28) "R28".
  destruct (valu_has_bits_shape v28 64 Hshape28) as [b28 ->].
  iDestruct "T29" as (v29 Hshape29) "R29".
  destruct (valu_has_bits_shape v29 64 Hshape29) as [b29 ->].
  iDestruct "T30" as (v30 Hshape30) "R30".
  destruct (valu_has_bits_shape v30 64 Hshape30) as [b30 ->].
  iDestruct "T31" as (v31 Hshape31) "R31".
  destruct (valu_has_bits_shape v31 64 Hshape31) as [b31 ->].
  (* The caller's 112 bytes are the callee's 96-byte frame above the
     16-byte frame of its decodeItem call. *)
  iDestruct (mem_mapsto_uninit_split 16 with "Hstack") as "[Hlow Hhigh]";
    [lia |].
  have Hhigh : bv_unsigned sp - 112 + 16 = bv_unsigned sp - 96 by lia.
  have Hsize : (112 - 16 : Z) = 96 by reflexivity.
  iEval (rewrite Hhigh Hsize) in "Hhigh".
  iEval (rewrite -Hlength) in "Hslice".
  iSplitR "Hret".
  { unfold nextUint64ContractEntry, nextUint64BoundaryEntry,
      nextUint64EntryAt800d6274, nextUint64Registers.
    cbn [nextUint64Base nextUint64InputEnd nextUint64SavedX21 nextUint64SavedX22
      nextUint64SavedX23 nextUint64SavedX24 nextUint64SavedX25 nextUint64SavedX26
      nextUint64SavedX27 nextInputPointer nextInputBytes nextSlicePointer
      nextResultPointer nextStackPointer nextReturnAddress nextSavedS0
      nextSavedS1 nextSavedS2 nextSavedS3 nextSavedS4 params base].
    iSplitR "".
    2: { iSplit; [done | done]. }
    iExists b5, b6, b7, b10, b11, b12, b13, b14, b15, b16, b17, b28, b29, b30, b31.
    rewrite !Z_to_bv_bv_unsigned.
    iFrame "Hsys R1 R2 R5 R6 R7 R8 R9 R10 R11 R12 R13 R14 R15 R16 R17
      R18 R19 R20 R21 R22 R23 R24 R25 R26 R27 R28 R29 R30 R31
      Hinput Hslice Hresult Hhigh Hlow".
    iPureIntro.
    split; [exact HactualDomain |].
    repeat split; reflexivity. }
  iApply (instr_pre_wand (bv_unsigned ret) (bv_unsigned ret)
    true true with "Hret"); [done | reflexivity |].
  iIntros "Hpost".
  iDestruct "Hpost" as (result [_ [_ Hmeaning]]) "Hexit".
  iEval (unfold nextUint64ContractExit, nextUint64Registers) in "Hexit".
  iDestruct "Hexit" as (f5 f6 f7 f10 f11 f12 f13 f14 f15 f16 f17 f28 f29 f30 f31)
    "(Hsys & R1 & R2 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 &
      R15 & R16 & R17 & R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 &
      R27 & R28 & R29 & R30 & R31 & Hinput & Hslice & Hresult & Hhigh & Hlow & _)".
  iEval (cbn [nextUint64Base nextUint64InputEnd nextUint64SavedX21
    nextUint64SavedX22 nextUint64SavedX23 nextUint64SavedX24 nextUint64SavedX25
    nextUint64SavedX26 nextUint64SavedX27 nextInputPointer nextInputBytes
    nextSlicePointer nextResultPointer nextStackPointer nextReturnAddress
    nextSavedS0 nextSavedS1 nextSavedS2 nextSavedS3 nextSavedS4 params base])
    in "R1 R2 R8 R9 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27 Hinput Hslice
      Hresult Hhigh Hlow".
  iEval (rewrite !Z_to_bv_bv_unsigned) in "R1 R2".
  iEval (rewrite /nextUint64SysRegs decodeItemSysRegs_exact /reg_col big_sepL_app)
    in "Hsys".
  iDestruct "Hsys" as "[Hstatic Hdynamic]".
  iEval (cbn [nextUint64CalleeBase decodeItemInputEnd nextUint64InputEnd params])
    in "Hdynamic".
  iDestruct "Hdynamic" as "[Hend Hfree]".
  iDestruct "Hend" as (endval Hendeq) "Hend".
  cbn in Hendeq. subst endval.
  iEval (rewrite Z_to_bv_bv_unsigned) in "Hend".
  have Hlow : bv_unsigned sp - 96 - 16 = bv_unsigned sp - 112 by lia.
  iEval (rewrite Hlow) in "Hlow".
  iEval (rewrite -Hhigh -Hsize) in "Hhigh".
  iDestruct (mem_mapsto_uninit_combine 16 with "Hlow Hhigh") as "Hstack";
    [lia |].
  unfold machine_call_ret.
  iSplitL "Hstatic"; [iExact "Hstatic" |].
  iSplitL "R1 R12 R13 R14 R15 R16 R17 R5 R6 R7 R28 R29 R30 R31".
  { rewrite /tmp_registers /= !reg_col_cons reg_col_nil.
    iSplitL "R1". { iExists (RVal_Bits ret). iFrame. done. }
    iSplitL "R12". { iExists (RVal_Bits f12). iFrame. done. }
    iSplitL "R13". { iExists (RVal_Bits f13). iFrame. done. }
    iSplitL "R14". { iExists (RVal_Bits f14). iFrame. done. }
    iSplitL "R15". { iExists (RVal_Bits f15). iFrame. done. }
    iSplitL "R16". { iExists (RVal_Bits f16). iFrame. done. }
    iSplitL "R17". { iExists (RVal_Bits f17). iFrame. done. }
    iSplitL "R5". { iExists (RVal_Bits f5). iFrame. done. }
    iSplitL "R6". { iExists (RVal_Bits f6). iFrame. done. }
    iSplitL "R7". { iExists (RVal_Bits f7). iFrame. done. }
    iSplitL "R28". { iExists (RVal_Bits f28). iFrame. done. }
    iSplitL "R29". { iExists (RVal_Bits f29). iFrame. done. }
    iSplitL "R30". { iExists (RVal_Bits f30). iFrame. done. }
    iSplitL "R31". { iExists (RVal_Bits f31). iFrame. done. }
    done. }
  iSplitL "R8 R9 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27".
  { rewrite /= !reg_col_cons reg_col_nil.
    iSplitL "R8". { iExists (RVal_Bits b8). iFrame. done. }
    iSplitL "R9". { iExists (RVal_Bits b9). iFrame. done. }
    iSplitL "R18". { iExists (RVal_Bits b18). iFrame. done. }
    iSplitL "R19". { iExists (RVal_Bits b19). iFrame. done. }
    iSplitL "R20". { iExists (RVal_Bits b20). iFrame. done. }
    iSplitL "R21". { iExists (RVal_Bits b21). iFrame. done. }
    iSplitL "R22". { iExists (RVal_Bits b22). iFrame. done. }
    iSplitL "R23". { iExists (RVal_Bits b23). iFrame. done. }
    iSplitL "R24". { iExists (RVal_Bits b24). iFrame. done. }
    iSplitL "R25". { iExists (RVal_Bits b25). iFrame. done. }
    iSplitL "R26". { iExists (RVal_Bits b26). iFrame. done. }
    iSplitL "R27". { iExists (RVal_Bits b27). iFrame. done. }
    done. }
  rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
  iExists (RVal_Bits f10). iFrame "R10". iExists f10.
  iSplit; [done|].
  iExists (RVal_Bits f11). iFrame "R11". iExists f11.
  iSplit; [done|].
  iFrame "R2 Hstack".
  iDestruct (nextUint64_slice_to_words with "Hslice") as "[HsliceP HsliceL]".
  iExists result. iFrame "Hend Hfree Hinput HsliceP HsliceL Hresult".
  iPureIntro. split; [| exact I].
  unfold nextUint64RootResult in Hmeaning |- *.
  cbn in Hmeaning |- *. exact Hmeaning.
Qed.

Lemma nextUint64CallSpec2_boxed `{!islaG Sigma} `{!threadG} :
  NextUint64ContractCorrect ->
  nextUint64SelectedCode -∗ □ instr_pre nextUint64Entry nextUint64CallSpec2.
Proof.
  intros Hcontract.
  rewrite /ZesuSsz.Contracts.NextUint64Selected.nextUint64SelectedCode.
  iIntros "#Hcode". iModIntro.
  iApply instr_pre_to_body. iNext.
  iApply (nextUint64CallSpec2_correct Hcontract). iExact "Hcode".
Qed.
