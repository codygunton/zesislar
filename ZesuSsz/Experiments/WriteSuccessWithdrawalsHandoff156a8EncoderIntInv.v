From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslaMemoryOperational.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15698.
Require Import ZesuSsz.Experiments.WriteSuccessSegment1569c.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156a0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156a4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156a8.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156ac.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156b0.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsEncoderIntCallerFacts.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntContext.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156a8EncoderIntState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyAfter.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyEndpointPreservation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694Entry.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694InvMemcpy.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694InvMemcpyMemory.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694InvMemcpyState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694InvMemcpySupport.

Open Scope Z_scope.

Lemma writeSuccessWithdrawals156a8EncoderIntInv args sp pointer base total processed
    remaining withdrawal allBytes prefix current suffix scratch encoderScratch
    registerFrame memoryFrame priorLog state regs global :
  Inv_15694 args sp pointer base total processed remaining withdrawal allBytes
    prefix current suffix scratch encoderScratch registerFrame memoryFrame priorLog state ->
  writeSuccessWithdrawalsPrefixAfter state.1 sp pointer = writeSuccess101d4Before regs global ->
  Inv_encoder_int (writeSuccessWithdrawalsIndexValue withdrawal) sp
    (Z_to_bv 64 0x156b4) encoderScratch
    (writeSuccessWithdrawalsEncoderInt156b4State regs global sp pointer current withdrawal).2.(seq_mem)
    priorLog
    (writeSuccessWithdrawalsEncoderInt156b4State regs global sp pointer current withdrawal, priorLog).
Proof.
  intros Hinv Hentry.
  have Htable : writeSuccessWithdrawalsInstructionTable global.
  { have Hmemcpy := writeSuccessWithdrawalsPrefix15694InvMemcpy args sp pointer
      base total processed remaining withdrawal allBytes prefix current suffix
      scratch encoderScratch registerFrame memoryFrame priorLog state Hinv.
    rewrite Hentry in Hmemcpy. unfold Inv_memcpy in Hmemcpy. cbn in Hmemcpy. tauto. }
  have Hglobal : global = state.1.2.
  { pose proof (f_equal snd Hentry) as H. cbn in H.
    symmetry. exact H. }
  have HstateFacts : writeSuccessWithdrawalsOperationalRegisterFacts state.1.1.(seq_regs) by
    (unfold Inv_15694 in Hinv; tauto).
  have HendFacts := writeSuccessWithdrawals156a8RegsFacts regs global sp pointer current.
  have HprefixFacts : writeSuccessWithdrawalsOperationalRegisterFacts regs.
  { have Hmemcpy := writeSuccessWithdrawalsPrefix15694InvMemcpy args sp pointer
      base total processed remaining withdrawal allBytes prefix current suffix scratch
      encoderScratch registerFrame memoryFrame priorLog state Hinv.
    rewrite Hentry in Hmemcpy. unfold Inv_memcpy in Hmemcpy. cbn in Hmemcpy. tauto. }
  specialize (HendFacts HprefixFacts).
  have Hlength : length current = 48%nat by (unfold Inv_15694 in Hinv; tauto).
  destruct (writeSuccessWithdrawalsPrefix15694MemcpyMemory args sp pointer base total
    processed remaining withdrawal allBytes prefix current suffix scratch encoderScratch
    registerFrame memoryFrame priorLog state Hinv) as
    (_ & _ & HhighRange & _ & _ & HhighLower & HhighUpper & _ & HhighBacked & _).
  have Hmemory := writeSuccessMemcpyBytesAfterMemory
    (writeSuccess101d4Regs regs) global pointer (sp + BV 64 1744)%bv
    (Z_to_bv 64 0) current 0 ltac:(reflexivity) ltac:(lia).
  specialize (Hmemory ltac:(rewrite Hlength; cbn; lia)).
  have Haddress := writeSuccessWithdrawalsPrefixDestinationUnsigned sp
    ltac:(unfold Inv_15694 in Hinv; tauto).
  have Hmemory' :
      (writeSuccessWithdrawalsEncoderInt156b4State regs global sp pointer current withdrawal).2.(seq_mem) =
      write_mem_list global.(seq_mem)
        (Z_to_bv 64 (bv_unsigned (sp + BV 64 1744)%bv)) current.
  { unfold writeSuccessWithdrawalsEncoderInt156b4State, writeSuccess156b0After,
      writeSuccess156acRegs, writeSuccess156a8Regs, writeSuccess15694Local,
      writeSuccessWithdrawals156a8Global, writeSuccessMemcpyEndpointGlobal,
      writeSuccessMemcpyLoopAfter. cbn. rewrite Hmemory.
    replace ((sp + BV 64 1744)%bv + Z_to_bv 64 0)%bv with
      (Z_to_bv 64 (bv_unsigned (sp + BV 64 1744)%bv)) by
      (apply bv_eq; bv_solve). reflexivity. }
  have HlowRead : read_mem_list global.(seq_mem) (bv_unsigned sp - 16) 16%N = Some encoderScratch.
  { rewrite Hglobal. unfold Inv_15694 in Hinv. tauto. }
  have Hdisjoint : islaMemoryRangesDisjoint
      (bv_unsigned (sp + BV 64 1744)%bv) (length current)
      (bv_unsigned sp - 16) 16.
  { unfold islaMemoryRangesDisjoint. right. rewrite Haddress. lia. }
  have HlowAfter : read_mem_list
      (writeSuccessWithdrawalsEncoderInt156b4State regs global sp pointer current withdrawal).2.(seq_mem)
      (bv_unsigned sp - 16) 16%N = Some encoderScratch.
  { rewrite Hmemory'. change (read_mem_list
      (write_mem_list global.(seq_mem)
        (Z_to_bv 64 (bv_unsigned (sp + BV 64 1744)%bv)) current)
      (bv_unsigned sp - 16) (N.of_nat 16) = Some encoderScratch).
    eapply read_mem_list_write_mem_list_disjoint;
      [exact HhighRange|exact Hdisjoint|exact HlowRead]. }
  have Hdom : dom
      (writeSuccessWithdrawalsEncoderInt156b4State regs global sp pointer current withdrawal).2.(seq_mem) =
      dom state.1.2.(seq_mem).
  { have HhighBackedGlobal : forall location,
        bv_unsigned (sp + BV 64 1744)%bv <= location <
          bv_unsigned (sp + BV 64 1744)%bv + Z.of_nat (length current) ->
        is_Some (global.(seq_mem) !! Z_to_bv 64 location).
    { intros location Hlocation. rewrite Hglobal.
      apply HhighBacked. exact Hlocation. }
    rewrite Hmemory'. rewrite write_mem_list_dom;
      [rewrite Hglobal; reflexivity|exact HhighRange|exact HhighBackedGlobal]. }
  destruct (writeSuccessEncoderIntCaller156b4 global Htable) as (HretAlign & HretCode).
  unfold Inv_encoder_int.
  split; first (apply writeSuccessWithdrawalsEncoderInt156b4Boundary; exact Htable).
  split; first reflexivity.
  split.
  { unfold writeSuccessWithdrawalsConcretePc.
    unfold writeSuccessWithdrawalsEncoderInt156b4State, writeSuccess156b0After,
      writeSuccess15694Local. cbn. rewrite lookup_insert.
    destruct writeSuccess156b0ValuesExact as (_ & _ & _ & Htarget).
    rewrite Htarget. native_compute. reflexivity. }
  split; first apply writeSuccessWithdrawalsEncoderInt156b4RegsX1.
  split.
  { apply writeSuccessWithdrawalsEncoderInt156b4RegsX2.
    have Hmemcpy := writeSuccessWithdrawalsPrefix15694InvMemcpy args sp pointer base
      total processed remaining withdrawal allBytes prefix current suffix scratch
      encoderScratch registerFrame memoryFrame priorLog state Hinv.
    rewrite Hentry in Hmemcpy. unfold Inv_memcpy in Hmemcpy. cbn in Hmemcpy.
    (* x2 is preserved by the exact prefix updates. *)
    have HstateSp : state.1.1.(seq_regs) !! "x2" = Some (RVal_Bits sp) by
      (unfold Inv_15694 in Hinv; tauto).
    have HprefixSp : (writeSuccessWithdrawalsPrefixAfter state.1 sp pointer).1.(seq_regs)
        !! "x2" = Some (RVal_Bits sp).
    { unfold writeSuccessWithdrawalsPrefixAfter, writeSuccessWithdrawalsPrefixStatea4,
        writeSuccessWithdrawalsPrefixStatea0, writeSuccessWithdrawalsPrefixState9c,
        writeSuccessWithdrawalsPrefixState98, writeSuccess156a4After,
        writeSuccess156a0After, writeSuccess1569cAfter, writeSuccess15698After,
        writeSuccess15694After, writeSuccess15694Local. cbn.
      rewrite writeSuccess156a4RegsLookupOther; try discriminate.
      rewrite writeSuccess156a0RegsLookupOther; try discriminate.
      rewrite writeSuccess1569cRegsLookupOther; try discriminate.
      rewrite writeSuccess15698RegsLookupOther; try discriminate.
      unfold writeSuccess15694Regs.
      repeat (rewrite lookup_insert_ne; last discriminate). exact HstateSp. }
    rewrite Hentry in HprefixSp. exact HprefixSp. }
  split; first apply writeSuccessWithdrawalsEncoderInt156b4RegsX10.
  split; first exact HretAlign.
  split.
  { destruct HretCode as [returnTrace Hreturn]. exists returnTrace.
    unfold writeSuccessWithdrawalsEncoderInt156b4State, writeSuccess156b0After,
      writeSuccess15694Local. cbn. rewrite writeSuccessWithdrawals156a8Instrs.
    exact Hreturn. }
  split.
  { have Halign16 : bv_unsigned sp `mod` 16 = 0 by (unfold Inv_15694 in Hinv; tauto).
    apply Z.mod_divide; [lia|]. apply Z.mod_divide in Halign16; [|lia].
    destruct Halign16 as [factor Hfactor]. exists (2 * factor). lia. }
  split; first (unfold Inv_15694 in Hinv; tauto).
  split.
  { have HspUpper : bv_unsigned sp + 1792 < 0x40000000 by
      (unfold Inv_15694 in Hinv; tauto). lia. }
  split; first exact HlowAfter.
  split.
  { have HspLower : 0x20000000 <= bv_unsigned sp - 16 by
      (unfold Inv_15694 in Hinv; tauto).
    unfold islaMemoryRange. split; [lia|].
    pose proof (bv_unsigned_in_range 64 sp). unfold bv_modulus in *. cbn in *. lia. }
  split.
  { intros location Hlocation.
    apply (writeSuccessReadMemListBacked
      (writeSuccessWithdrawalsEncoderInt156b4State regs global sp pointer
        current withdrawal).2.(seq_mem)
      (bv_unsigned sp - 16) 16 encoderScratch HlowAfter location).
    lia. }
  split; first (split; [reflexivity|intros; reflexivity]).
  split.
  { unfold writeSuccessWithdrawalsInstructionTable in Htable |- *.
    intros pc trace Hsource.
    change ((writeSuccessWithdrawals156a8Global regs global sp pointer current).(seq_instrs) !! Z_to_bv 64 pc = Some trace).
    rewrite writeSuccessWithdrawals156a8Instrs. apply Htable. exact Hsource. }
  split; first (apply writeSuccessWithdrawalsEncoderInt156b4RegsFacts; exact HendFacts).
  split.
  { rewrite Hdom. unfold Inv_15694 in Hinv. tauto. }
  reflexivity.
Qed.

Print Assumptions writeSuccessWithdrawals156a8EncoderIntInv.
