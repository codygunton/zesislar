Require Import ZesuSsz.Automation.All.
Require Export ZesuSsz.Contracts.DecodeItemCallSpec.
From Coq Require Import List ZArith.
From stdpp Require Import base list bitvector.definitions.
Require Import isla.riscv64.riscv64.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Automation.Calls.
Require Import ZesuSsz.Contracts.DecodeItemCompositional.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Compliance.DecodeItemCompositionalCompliance.
Import ListNotations.
Open Scope Z_scope.
Open Scope stdpp_scope.

Lemma decodeItemCallSpec_correct `{!islaG Sigma} `{!threadG} :
  decodeItemSelectedCode -∗ instr_body decodeItemEntry decodeItemCallSpec.
Proof.
  iStartProof. iIntros "Hcode".
  rewrite instr_pre'_eq /instr_pre'_def /=.
  iIntros "Hspec".
  iEval (unfold decodeItemCallSpec) in "Hspec".
  zesu_unpack_call "Hspec".
  subst r10 r11 r12 r13 r14 r15 r16 r17.
  iDestruct "Hrest" as (input before inputEndBits)
    "(Hend & Hfree & Hinput & Hbefore & %Hdomain & Hret)".
  cbn [decodeItemCallDataArgs] in Hdomain.
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
  set (base := {| decodeItemOutputPointer := bv_unsigned b10;
    decodeItemInputPointer := bv_unsigned b11;
    decodeItemInputLength := bv_unsigned b12;
    decodeItemInputBytes := input; decodeItemBeforeStorage := before;
    decodeItemStackPointer := bv_unsigned sp;
    decodeItemReturnAddress := bv_unsigned ret;
    decodeItemSavedFramePointer := b8; decodeItemInputEnd := bv_unsigned inputEndBits |}).
  set (saved := {| decodeItemSavedX9 := b9;
    decodeItemSavedX18 := b18; decodeItemSavedX19 := b19;
    decodeItemSavedX20 := b20; decodeItemSavedX21 := b21;
    decodeItemSavedX22 := b22; decodeItemSavedX23 := b23;
    decodeItemSavedX24 := b24; decodeItemSavedX25 := b25;
    decodeItemSavedX26 := b26; decodeItemSavedX27 := b27 |}).
  set (args := {| decodeItemCompositionalBase := base;
    decodeItemCompositionalSaved := saved |}).
  pose proof (decodeItemSelectedComplianceCompositional
    (bv_unsigned ret) Sigma islaG0 H) as Hcorrect.
  unfold IslarisContractSpec in Hcorrect.
  cbn [decodeItemSelectedModelCompositional decodeItemResourcesCompositional]
    in Hcorrect.
  iPoseProof (Hcorrect with "Hcode") as "Hbody".
  iSpecialize ("Hbody" $! args).
  iEval (rewrite {1}instr_pre'_eq /instr_pre'_def /=) in "Hbody".
  iApply "Hbody".
  have Hretalign : bv_unsigned ret `mod` 4 = 0.
  { pose proof (f_equal (@bv_unsigned 2) Hret2) as Hbits.
    rewrite bv_extract_unsigned in Hbits.
    change (bv_unsigned ret `mod` 4 = 0) in Hbits.
    exact Hbits. }
  have HactualDomain : decodeItemDomainAt (bv_unsigned ret)
      decodeItemC1BDomain base.
  { split; [reflexivity|].
    pose proof (bv_unsigned_in_range 64 ret) as Hrange.
    change (0 <= bv_unsigned ret < word64Modulus) in Hrange.
    unfold decodeItemC1BDomain, decodeItemArgsWellFormed,
      decodeItemEntryLayout in Hdomain |- *.
    unfold decodeItemCallDataArgs in Hdomain.
    cbn in Hdomain.
    subst base. cbn.
    clear - Hdomain Hrange Hretalign.
    naive_solver. }
  iAssert (reg_col (decodeItemSysRegs base)) with "[Hsys Hend Hfree]"
    as "Hsys".
  { rewrite decodeItemSysRegs_exact /reg_col big_sepL_app.
    fold (reg_col (machine_static_sys_regs defaultMap)).
    fold (reg_col [(KindReg "zisk_input_end", ExactShape
      (RVal_Bits (Z_to_bv 64 (decodeItemInputEnd base))));
      (KindReg "zisk_free_input", BitsShape 64)]).
    iFrame "Hsys". rewrite reg_col_cons.
    iSplitL "Hend".
    { iExists (RVal_Bits inputEndBits).
      subst base. cbn. rewrite Z_to_bv_bv_unsigned. iFrame. done. }
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
  iEval (cbn [lookup_total list_lookup_total]) in "Hinput Hbefore Hret".
  subst args base saved.
  iSplitR "Hret".
  { unfold decodeItemEntryResourcesCompositional, decodeItemEntryResources,
      decodeItemUntouchedRegisters, decodeItemOtherCallerRegisters,
      decodeItemOtherCalleeRegisters.
    cbn [decodeItemCompositionalBase decodeItemCompositionalSaved decodeItemOutputPointer decodeItemInputPointer decodeItemInputLength decodeItemInputBytes decodeItemBeforeStorage decodeItemStackPointer decodeItemReturnAddress decodeItemSavedFramePointer decodeItemInputEnd decodeItemSavedX9 decodeItemSavedX18 decodeItemSavedX19 decodeItemSavedX20 decodeItemSavedX21 decodeItemSavedX22 decodeItemSavedX23 decodeItemSavedX24 decodeItemSavedX25 decodeItemSavedX26 decodeItemSavedX27].
    iSplitL "Hsys R10 R11 R12 R13 R14 R15 R16 R1 R2 R8 Hinput Hbefore Hstack".
    { iExists b13, b14, b15, b16.
      rewrite !Z_to_bv_bv_unsigned.
      iFrame "Hsys R10 R11 R12 R13 R14 R15 R16 R2 R1 R8 Hinput Hbefore Hstack".
      iPureIntro. split; [exact HactualDomain | exact I]. }
    iSplitL "R5 R6 R7 R17 R28 R29 R30 R31".
    { iExists b5, b6, b7, b17, b28, b29, b30, b31. iFrame. }
    iFrame. }
  iApply (instr_pre_wand (bv_unsigned ret) (bv_unsigned ret)
    true true with "Hret"); [done | reflexivity |].
  iIntros "Hpost".
  iDestruct "Hpost" as (after [HreturnedDomain Hmeaning]) "Hexit".
  iEval (unfold decodeItemExitResourcesCompositional,
    decodeItemExitResourcesRegisters, decodeItemUntouchedRegisters) in "Hexit".
  iDestruct "Hexit" as "[[Hbase Hreturned] [Hother Hsaved]]".
  iEval (unfold decodeItemExitResources) in "Hbase".
  iEval (cbn [decodeItemCompositionalBase decodeItemCompositionalSaved decodeItemOutputPointer decodeItemInputPointer decodeItemInputLength decodeItemInputBytes decodeItemBeforeStorage decodeItemStackPointer decodeItemReturnAddress decodeItemSavedFramePointer decodeItemInputEnd decodeItemSavedX9 decodeItemSavedX18 decodeItemSavedX19 decodeItemSavedX20 decodeItemSavedX21 decodeItemSavedX22 decodeItemSavedX23 decodeItemSavedX24 decodeItemSavedX25 decodeItemSavedX26 decodeItemSavedX27]) in "Hbase".
  iEval (rewrite !Z_to_bv_bv_unsigned) in "Hbase".
  iDestruct "Hbase" as
    "(Hsys & R2 & R1 & R8 & Hinput & Hafter & Hstack & _)".
  iEval (unfold decodeItemReturnedCallerRegisters) in "Hreturned".
  iDestruct "Hreturned" as (f10 f11 f12 f13 f14 f15 f16)
    "(R10 & R11 & R12 & R13 & R14 & R15 & R16)".
  iEval (unfold decodeItemOtherCallerRegisters) in "Hother".
  iDestruct "Hother" as (f5 f6 f7 f17 f28 f29 f30 f31)
    "(R5 & R6 & R7 & R17 & R28 & R29 & R30 & R31)".
  iEval (unfold decodeItemOtherCalleeRegisters) in "Hsaved".
  iEval (cbn [decodeItemCompositionalBase decodeItemCompositionalSaved decodeItemOutputPointer decodeItemInputPointer decodeItemInputLength decodeItemInputBytes decodeItemBeforeStorage decodeItemStackPointer decodeItemReturnAddress decodeItemSavedFramePointer decodeItemInputEnd decodeItemSavedX9 decodeItemSavedX18 decodeItemSavedX19 decodeItemSavedX20 decodeItemSavedX21 decodeItemSavedX22 decodeItemSavedX23 decodeItemSavedX24 decodeItemSavedX25 decodeItemSavedX26 decodeItemSavedX27]) in "Hsaved".
  iDestruct "Hsaved" as
    "(R9 & R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27)".
  iEval (rewrite decodeItemSysRegs_exact /reg_col big_sepL_app) in "Hsys".
  iDestruct "Hsys" as "[Hstatic Hdynamic]".
  iEval (cbn [decodeItemCompositionalBase decodeItemCompositionalSaved decodeItemOutputPointer decodeItemInputPointer decodeItemInputLength decodeItemInputBytes decodeItemBeforeStorage decodeItemStackPointer decodeItemReturnAddress decodeItemSavedFramePointer decodeItemInputEnd decodeItemSavedX9 decodeItemSavedX18 decodeItemSavedX19 decodeItemSavedX20 decodeItemSavedX21 decodeItemSavedX22 decodeItemSavedX23 decodeItemSavedX24 decodeItemSavedX25 decodeItemSavedX26 decodeItemSavedX27]) in "Hdynamic".
  iDestruct "Hdynamic" as "[Hend Hfree]".
  iDestruct "Hend" as (endval Hendeq) "Hend".
  cbn in Hendeq. subst endval.
  iEval (rewrite Z_to_bv_bv_unsigned) in "Hend".
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
  iExists after. iFrame "Hend Hfree Hinput Hafter".
  iPureIntro. split; [exact Hmeaning | exact I].
Qed.



Lemma decodeItemCallSpec_boxed `{!islaG Sigma} `{!threadG} :
  decodeItemSelectedCode -∗ □ instr_pre 0x800d6960 decodeItemCallSpec.
Proof.
  rewrite /ZesuSsz.Contracts.DecodeItemSelected.decodeItemSelectedCode.
  iIntros "#Hcode". iModIntro.
  iApply instr_pre_to_body. iNext.
  iApply decodeItemCallSpec_correct. iExact "Hcode".
Qed.
