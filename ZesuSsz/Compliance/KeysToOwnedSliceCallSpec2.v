Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import List ZArith.
From stdpp Require Import base list bitvector.definitions.
Require Import ZesuMachineMap.Machine.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Generated.Stock.Symbols.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Contracts.AbiBytes.
Require Import ZesuSsz.Contracts.ZiskRuntime.
Require Import ZesuSsz.Contracts.AltFlAllocPremises.
Require Import ZesuSsz.Contracts.ZiskMemcpyPremise.
Require Import ZesuSsz.Contracts.ArrayListContract.
Require Import ZesuSsz.Contracts.KeysToOwnedSliceSelected.
Require Import ZesuSsz.Contracts.KeysToOwnedSliceContract.
Require Import ZesuSsz.Contracts.KeysToOwnedSliceCallSpec2.
Require Import ZesuSsz.Compliance.ArrayListBridges.
Import ListNotations.
Open Scope Z_scope.
Open Scope stdpp_scope.

(* The template is a spec only in this proof of its correctness; callers use the
   sealed public spec of ZesuSsz/Interfaces/KeysToOwnedSlice.v. *)
#[local] Instance : LithiumUnfold (@keysToOwnedSliceCallSpecDefinition) := I.
Global Typeclasses Opaque keysToOwnedSliceCallSpecDefinition.

(* The system registers of the call boundary as the contract's collection. *)
Lemma keysToOwnedSlice_sys_regs_intro `{!islaG Sigma} `{!threadG} (inputEnd : bv 64) :
  reg_col (machine_sys_regs decodeItemCallMap) -∗
  "zisk_input_end" ↦ᵣ RVal_Bits inputEnd -∗
  reg_col [(KindReg "zisk_free_input", BitsShape 64)] -∗
  reg_col (arrayListSysRegs inputEnd).
Proof.
  iIntros "Hsys Hend Hfree".
  rewrite /arrayListSysRegs /reg_col big_sepL_app.
  fold (reg_col (machine_static_sys_regs defaultMap)).
  fold (reg_col [(KindReg "zisk_input_end", ExactShape (RVal_Bits inputEnd));
    (KindReg "zisk_free_input", BitsShape 64)]).
  iFrame "Hsys". rewrite reg_col_cons.
  iSplitL "Hend"; [iExists (RVal_Bits inputEnd); cbn; iFrame; done|].
  iExact "Hfree".
Qed.

Lemma keysToOwnedSlice_sys_regs_elim `{!islaG Sigma} `{!threadG} (inputEnd : bv 64) :
  reg_col (arrayListSysRegs inputEnd) -∗
  reg_col (machine_sys_regs decodeItemCallMap) ∗
  "zisk_input_end" ↦ᵣ RVal_Bits inputEnd ∗
  reg_col [(KindReg "zisk_free_input", BitsShape 64)].
Proof.
  iIntros "Hsys".
  rewrite /arrayListSysRegs /reg_col big_sepL_app.
  iDestruct "Hsys" as "[$ Hdynamic]".
  fold (reg_col [(KindReg "zisk_input_end", ExactShape (RVal_Bits inputEnd));
    (KindReg "zisk_free_input", BitsShape 64)]).
  rewrite reg_col_cons.
  iDestruct "Hdynamic" as "[Hend $]".
  iDestruct "Hend" as (v Hv) "Hend". cbn in Hv. subst v. iExact "Hend".
Qed.

(* The template keysToOwnedSliceCallSpecDefinition follows from the
   compositional theorem KeysToOwnedSliceContractCorrect: the call boundary
   supplies its entry, and its exit supplies the return boundary.
   ZesuSsz/Interfaces/KeysToOwnedSliceCorrect.v carries it over to the sealed
   public spec. *)
Lemma keysToOwnedSliceCallSpecDefinition_correct `{!islaG Sigma} `{!threadG} :
  KeysToOwnedSliceContractCorrect ->
  keysToOwnedSliceContractCode -∗
  instr_body sym_array_list_Aligned_32_u8_null_toOwnedSlice keysToOwnedSliceCallSpecDefinition.
Proof.
  intros Hcontract.
  iStartProof. iIntros "Hcode".
  rewrite instr_pre'_eq /instr_pre'_def /=.
  iIntros "Hspec".
  iEval (unfold keysToOwnedSliceCallSpecDefinition) in "Hspec".
  zesu_unpack_call "Hspec".
  subst r10 r11 r12 r13 r14 r15 r16 r17.
  iDestruct "Hrest" as (inputEndBits context state resultBefore scratchBefore)
    "(Hend & Hfree & Hheader & Hbuffer & Hresult & Hscratch & Hobject & Hvtable & Hheap &
      %Hdomain & Hret)".
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
  iEval (cbn [lookup_total list_lookup_total]) in "Hheader Hresult Hobject Hret".
  cbn [lookup_total list_lookup_total] in Hdomain.
  have Hretalign : (4 | bv_unsigned ret).
  { pose proof (f_equal (@bv_unsigned 2) Hret2) as Hbits.
    rewrite bv_extract_unsigned in Hbits.
    apply Z.mod_divide; [lia|]. exact Hbits. }
  have Hsp16 : (16 | bv_unsigned sp) by (apply Z.mod_divide; [lia|exact Hspalign]).
  pose proof (Hcontract (bv_unsigned ret) Sigma islaG0 H) as Hcorrect.
  unfold IslarisContractSpec in Hcorrect.
  cbn [keysToOwnedSliceContractModel toOwnedSliceModel toOwnedSliceResources
    islarisContractResources islarisContractAllows islarisCode islarisEntry islarisExit]
    in Hcorrect.
  iPoseProof (Hcorrect with "Hcode") as "Hbody".
  iSpecialize ("Hbody" $! (keysToOwnedSliceCallArgs [b10; b11; b12; b13; b14; b15; b16; b17]
    sp ret inputEndBits
    {| savedX8 := b8; savedX9 := b9; savedX18 := b18; savedX19 := b19;
       savedX20 := b20; savedX21 := b21; savedX22 := b22; savedX23 := b23;
       savedX24 := b24; savedX25 := b25; savedX26 := b26; savedX27 := b27 |}
    context state resultBefore scratchBefore)).
  iEval (rewrite {1}instr_pre'_eq /instr_pre'_def /=) in "Hbody".
  iApply "Hbody".
  iDestruct (keysToOwnedSlice_sys_regs_intro with "Hsys Hend Hfree") as "Hsys".
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
  iSplitR "Hret".
  { iSplit; [done|].
    rewrite /toOwnedSliceEntry /keysToOwnedSliceCallArgs.
    cbn [toOwnedResultPointer toOwnedListPointer toOwnedAllocatorPointer toOwnedAllocatorContext
      toOwnedList toOwnedResultBefore toOwnedScratchBefore toOwnedStackPointer toOwnedInputEnd
      toOwnedReturnAddress toOwnedSaved lookup_total list_lookup_total].
    iExists b5, b6, b7, b13, b14, b15, b16, b17, b28, b29, b30, b31.
    rewrite arrayListSavedRegisters_unfold. cbn [savedX8 savedX9 savedX18 savedX19
      savedX20 savedX21 savedX22 savedX23 savedX24 savedX25 savedX26 savedX27].
    iFrame.
    iPureIntro. split; [|exact I].
    destruct Hdomain as (Hwf & Hres & Hres8 & Hlst & Hlst8 & Halc & Halc8 & Hrb & Hsb & Hctx).
    unfold toOwnedSliceDomain, arrayListStackLayout; cbn.
    change (mapRamBase decodeItemCallMap) with (mapRamBase defaultMap) in Hstackbounds.
    change (machineRamEnd decodeItemCallMap) with (machineRamEnd defaultMap) in Hstackbounds.
    split_and!; try assumption; lia. }
  iApply (instr_pre_wand (bv_unsigned ret) (bv_unsigned ret)
    true true with "Hret"); [done | reflexivity |].
  iIntros "Hpost".
  iDestruct "Hpost" as (outcome [_ [_ Hallows]]) "Hexit".
  iEval (rewrite /toOwnedSliceExit /keysToOwnedSliceCallArgs /toOwnedSliceScratchAfter) in "Hexit".
  iEval (cbn [toOwnedResultPointer toOwnedListPointer toOwnedAllocatorPointer toOwnedAllocatorContext
      toOwnedList toOwnedResultBefore toOwnedScratchBefore toOwnedStackPointer toOwnedInputEnd
      toOwnedReturnAddress toOwnedSaved lookup_total list_lookup_total]) in "Hexit".
  iDestruct "Hexit" as (f5 f6 f7 f10 f11 f12 f13 f14 f15 f16 f17 f28 f29 f30 f31)
    "(Hsys & R1 & R2 & R5 & R6 & R7 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17 &
      R28 & R29 & R30 & R31 & Hsaved & Hheader & Hlist & Hslice & Hresult & Hscratch &
      Hobject & Hvtable & Hheap & Hstack & _)".
  iDestruct (keysToOwnedSlice_sys_regs_elim with "Hsys") as "(Hstatic & Hend & Hfree)".
  iEval (rewrite arrayListSavedRegisters_unfold) in "Hsaved".
  iDestruct "Hsaved" as "(R8 & R9 & R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27)".
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
  iExists outcome. iFrame.
  iPureIntro. split; [|exact I]. exact Hallows.
Qed.
