From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
From IslaTraces.write_success_01 Require Import instrs.
From IslaTraces.write_success_02 Require Import instrs.
From IslaTraces.write_success_09 Require Import a14d7c_spec.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Experiments.WriteSuccessCallAbi.
Require Import ZesuSsz.Experiments.WriteSuccessCalls.
Require Import ZesuSsz.Experiments.WriteSuccessHeaderSpec.
Require Import ZesuSsz.Experiments.WriteSuccessLoadBlockAdapter.
Require Import ZesuSsz.Experiments.WriteSuccessLoadBlockWithFrame.
Require Import ZesuSsz.Experiments.WriteSuccessLoadHeader.
Require Import ZesuSsz.Experiments.WriteSuccessPrologueSpec.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Experiments.WriteSuccessValueBlock.
Require Import ZesuSsz.Experiments.WriteSuccessValueTransactionsEntry.

Import ListNotations.

Local Instance : LithiumUnfold (@writeSuccessLoadAdapterWithFrameSpec) := I.
Local Instance : LithiumUnfold (@writeSuccessLoadRegisterResources) := I.
Local Instance : LithiumUnfold (@writeSuccessLoadMemoryResources) := I.

Definition writeSuccessCallerOutputEventsWithFrame
    (data size : bv 64) (tail : spec) : spec :=
  scons (SWriteMem (BV 64 0x2401a0c0) data)
    (scons (SWriteMem (BV 64 0x2401a0c8) size) tail).

Definition writeSuccessLoadResidual `{!islaG Sigma} (sp : bv 64)
  (sourceBytes : list (bv 8)) (events : spec) (P : iProp Sigma) :
    iProp Sigma :=
  ((bv_unsigned sp + 312) ↦ₘ∗ sourceBytes ∗
   (bv_unsigned sp + 1032) ↦ₘ? 864 ∗
   mmio_range 0x2401a0c0 16 ∗ spec_trace events ∗ P ∗ True)%I.

Definition writeSuccessAtLoadWithFrame `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (sourceBytes : list (bv 8)) (events : spec)
    (P : iProp Sigma) : iProp Sigma :=
  (∃ (decoded b10 b11 : bv 64) (loaded : list (bv 64))
      (s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : bv 64),
    writeSuccessLoadRegisterResources sp decoded b10 b11
      [RVal_Bits s1; RVal_Bits s2; RVal_Bits s3; RVal_Bits s4;
       RVal_Bits s5; RVal_Bits s6; RVal_Bits s7; RVal_Bits s8;
       RVal_Bits s9; RVal_Bits s10; RVal_Bits s11] ∗
    writeSuccessLoadMemoryWithFrame sp decoded loaded
      [RVal_Bits s1; RVal_Bits s2; RVal_Bits s3; RVal_Bits s4;
       RVal_Bits s5; RVal_Bits s6; RVal_Bits s7; RVal_Bits s8;
       RVal_Bits s9; RVal_Bits s10; RVal_Bits s11] ∗
    writeSuccessLoadResidual sp sourceBytes events P)%I.

Global Instance : LithiumUnfold (@writeSuccessLoadResidual) := I.
Global Instance : LithiumUnfold (@writeSuccessAtLoadWithFrame) := I.

Definition writeSuccessAtLoadHeaderWithFrame `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (sourceBytes : list (bv 8)) (events : spec)
    (P : iProp Sigma) : iProp Sigma :=
  (∃ (decoded b10 b11 : bv 64) (loaded : list (bv 64))
      (s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : bv 64),
    writeSuccessLoadRegisterResources sp decoded b10 b11
      [RVal_Bits s1; RVal_Bits s2; RVal_Bits s3; RVal_Bits s4;
       RVal_Bits s5; RVal_Bits s6; RVal_Bits s7; RVal_Bits s8;
       RVal_Bits s9; RVal_Bits s10; RVal_Bits s11] ∗
    (bv_unsigned decoded + 720) ↦ₘ∗ loaded ∗
    bv_unsigned sp ↦ₘ? 312 ∗
    ⌜length loaded = 16%nat⌝ ∗
    ⌜bv_unsigned decoded `mod` 8 = 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned decoded + 720⌝ ∗
    ⌜bv_unsigned decoded + 848 < 0x40000000⌝ ∗
    ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned sp⌝ ∗
    ⌜bv_unsigned sp + 312 < 0x40000000⌝ ∗
    writeSuccessLoadResidual sp sourceBytes events P)%I.

Global Instance : LithiumUnfold (@writeSuccessAtLoadHeaderWithFrame) := I.

Definition writeSuccessLoadHeaderRemainder
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (sourceBytes : list (bv 8))
    (values : list (bv 64)) (payload : list (bv 8))
    (tail : spec) (base : Z) (transactions : list writeSuccessTransaction)
    (transactionBytes : list (bv 8)) : iProp Sigma :=
  (reg_col writeSuccessLoadHeaderExtraRegisters ∗
   (bv_unsigned sp - 48) ↦ₘ? 48 ∗
   bv_unsigned (writeSuccessValueWord values 4) ↦ₘ∗ payload ∗
   base ↦ₘ∗ transactionBytes ∗
   writeSuccessTransactionsOwn transactions ∗
   instr_pre writeSuccessTransactionsLoopExitAddress
     (writeSuccessTransactionsLoopExit sp base transactions transactionBytes tail
       (writeSuccessValueTransactionsContinuation values payload P)) ∗
   writeSuccessTransactionsInvariant sp base transactions [] transactions
     transactionBytes [] transactionBytes ∗
   ⌜length sourceBytes = 720%nat⌝ ∗
   ⌜bytes_of_u64s values = take 592 sourceBytes⌝ ∗
   ⌜length values = 74%nat⌝ ∗
   ⌜bv_unsigned (writeSuccessValueWord values 5) = length payload⌝ ∗
   ⌜writeSuccessValueWord values 7 = Z_to_bv 64 base⌝ ∗
   ⌜writeSuccessValueWord values 8 =
      Z_to_bv 64 (Z.of_nat (length transactions))⌝ ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
   ⌜0x20000000 <= bv_unsigned sp - 48⌝ ∗
   ⌜bv_unsigned sp + 1896 < 0x40000000⌝ ∗ P ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessLoadHeaderRemainder) := I.

(** The public entry owns this heap.  Code proofs supply the register frame,
    loop-exit continuation, and final continuation separately. *)
Definition writeSuccessLoadHeaderHeapResources
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (sourceBytes : list (bv 8))
    (values : list (bv 64)) (payload : list (bv 8))
    (base : Z) (transactions : list writeSuccessTransaction)
    (transactionBytes : list (bv 8)) : iProp Sigma :=
  ((bv_unsigned sp - 48) ↦ₘ? 48 ∗
   bv_unsigned (writeSuccessValueWord values 4) ↦ₘ∗ payload ∗
   base ↦ₘ∗ transactionBytes ∗
   writeSuccessTransactionsOwn transactions ∗
   writeSuccessTransactionsInvariant sp base transactions [] transactions
     transactionBytes [] transactionBytes ∗
   ⌜length sourceBytes = 720%nat⌝ ∗
   ⌜bytes_of_u64s values = take 592 sourceBytes⌝ ∗
   ⌜length values = 74%nat⌝ ∗
   ⌜bv_unsigned (writeSuccessValueWord values 5) = length payload⌝ ∗
   ⌜writeSuccessValueWord values 7 = Z_to_bv 64 base⌝ ∗
   ⌜writeSuccessValueWord values 8 =
      Z_to_bv 64 (Z.of_nat (length transactions))⌝ ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
   ⌜0x20000000 <= bv_unsigned sp - 48⌝ ∗
   ⌜bv_unsigned sp + 1896 < 0x40000000⌝ ∗ True)%I.

Global Instance : LithiumUnfold
    (@writeSuccessLoadHeaderHeapResources) := I.

Lemma write_success_load_header_remainder_pack
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (sourceBytes : list (bv 8))
    (values : list (bv 64)) (payload : list (bv 8))
    (tail : spec) (base : Z) (transactions : list writeSuccessTransaction)
    (transactionBytes : list (bv 8)) :
  reg_col writeSuccessLoadHeaderExtraRegisters -∗
  writeSuccessLoadHeaderHeapResources sp sourceBytes values payload base
    transactions transactionBytes -∗
  instr_pre writeSuccessTransactionsLoopExitAddress
    (writeSuccessTransactionsLoopExit sp base transactions transactionBytes tail
      (writeSuccessValueTransactionsContinuation values payload P)) -∗
  P -∗
  writeSuccessLoadHeaderRemainder P sp sourceBytes values payload tail base
    transactions transactionBytes.
Proof.
  rewrite /writeSuccessLoadHeaderHeapResources
    /writeSuccessLoadHeaderRemainder.
  iIntros "Hextra Hheap Hexit HP".
  iDestruct "Hheap" as
    "(Hlower & Hpayload & Harray & Hown & Hinvariant & %HsourceLength &
      %HvaluesBytes & %HvaluesLength & %HpayloadLength & %HbaseEq &
      %HcountEq & %Halign16 & %Halign8 & %HlowerBound & %HupperBound & _)".
  iFrame.
  repeat iSplit; try iPureIntro; try assumption; done.
Qed.

Lemma write_success_load_header_remainder_unpack
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (sourceBytes : list (bv 8))
    (values : list (bv 64)) (payload : list (bv 8))
    (tail : spec) (base : Z) (transactions : list writeSuccessTransaction)
    (transactionBytes : list (bv 8)) :
  writeSuccessLoadHeaderRemainder P sp sourceBytes values payload tail base
      transactions transactionBytes -∗
  reg_col writeSuccessLoadHeaderExtraRegisters ∗
  writeSuccessLoadHeaderHeapResources sp sourceBytes values payload base
      transactions transactionBytes ∗
  instr_pre writeSuccessTransactionsLoopExitAddress
    (writeSuccessTransactionsLoopExit sp base transactions transactionBytes tail
      (writeSuccessValueTransactionsContinuation values payload P)) ∗
  P.
Proof.
  rewrite /writeSuccessLoadHeaderHeapResources
    /writeSuccessLoadHeaderRemainder.
  iIntros "(Hextra & Hlower & Hpayload & Harray & Hown & Hexit &
    Hinvariant & %HsourceLength & %HvaluesBytes & %HvaluesLength &
    %HpayloadLength & %HbaseEq & %HcountEq & %Halign16 & %Halign8 &
    %HlowerBound & %HupperBound & HP & _)".
  iFrame.
  repeat iSplit; try iPureIntro; try assumption; done.
Qed.

Lemma write_success_at_load_with_frame_to_header
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (sourceBytes : list (bv 8))
    (values : list (bv 64)) (payload : list (bv 8))
    (tail : spec) (base : Z) (transactions : list writeSuccessTransaction)
    (transactionBytes : list (bv 8)) :
  writeSuccessAtLoadWithFrame sp sourceBytes
    (writeSuccessHeaderEvents sp
      (writeSuccessValueEvents sp values
        (writeSuccessTransactionsEvents sp transactions tail)))
    (writeSuccessLoadHeaderRemainder P sp sourceBytes values payload tail base
      transactions transactionBytes) ⊢
  writeSuccessLoadHeaderSpec P sp sourceBytes values payload tail base
    transactions transactionBytes.
Proof.
  rewrite /writeSuccessAtLoadWithFrame /writeSuccessLoadResidual
    /writeSuccessLoadMemoryWithFrame
    /writeSuccessLoadHeaderRemainder /writeSuccessLoadHeaderSpec
    /writeSuccessLoadHeaderResidual.
  iIntros "Hload".
  iDestruct "Hload" as
    (decoded b10 b11 loaded s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
    "(Hregisters & Hmemory & Hresidual)".
  iDestruct "Hmemory" as
    "(Hloaded & Hstack & %HloadedLength & %HdecodedAlign & %HdecodedMin &
      %HdecodedMax & %HspAlign & %HspMin & %HspMax & Hret)".
  iDestruct "Hresidual" as
    "(Hsource & Hdestination & Hmmio & Htrace & Hremainder & _)".
  iDestruct "Hremainder" as
    "(Hextra & Hlower & Hpayload & Harray & Hown & Hexit & Hinvariant &
      %HsourceLength & %HvaluesBytes & %HvaluesLength & %HpayloadLength &
      %HbaseEq & %HcountEq & %Halign16 & %Halign8 & %HlowerBound &
      %HupperBound & HP & _)".
  iExists decoded, b10, b11, loaded, s1, s2, s3, s4, s5, s6, s7, s8, s9,
    s10, s11.
  iFrame.
  repeat iSplit; try iPureIntro; try assumption.
Qed.

Lemma write_success_at_load_header_with_frame_to_header
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (sourceBytes : list (bv 8))
    (values : list (bv 64)) (payload : list (bv 8))
    (tail : spec) (base : Z) (transactions : list writeSuccessTransaction)
    (transactionBytes : list (bv 8)) :
  writeSuccessAtLoadHeaderWithFrame sp sourceBytes
    (writeSuccessHeaderEvents sp
      (writeSuccessValueEvents sp values
        (writeSuccessTransactionsEvents sp transactions tail)))
    (writeSuccessLoadHeaderRemainder P sp sourceBytes values payload tail base
      transactions transactionBytes) ⊢
  writeSuccessLoadHeaderSpec P sp sourceBytes values payload tail base
    transactions transactionBytes.
Proof.
  rewrite /writeSuccessAtLoadHeaderWithFrame /writeSuccessLoadResidual
    /writeSuccessLoadHeaderRemainder /writeSuccessLoadHeaderSpec
    /writeSuccessLoadHeaderResidual.
  iIntros "Hload".
  iDestruct "Hload" as
    (decoded b10 b11 loaded s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
    "(Hregisters & Hloaded & Hstack & %HloadedLength & %HdecodedAlign &
      %HdecodedMin & %HdecodedMax & %HspAlign & %HspMin & %HspMax &
      Hresidual)".
  iDestruct "Hresidual" as
    "(Hsource & Hdestination & Hmmio & Htrace & Hremainder & _)".
  iDestruct "Hremainder" as
    "(Hextra & Hlower & Hpayload & Harray & Hown & Hexit & Hinvariant &
      %HsourceLength & %HvaluesBytes & %HvaluesLength & %HpayloadLength &
      %HbaseEq & %HcountEq & %Halign16 & %Halign8 & %HlowerBound &
      %HupperBound & HP & _)".
  iExists decoded, b10, b11, loaded, s1, s2, s3, s4, s5, s6, s7, s8, s9,
    s10, s11.
  iFrame.
  repeat iSplit; try iPureIntro; try assumption.
Qed.

Lemma Z_to_nat_add_sub_base_with_frame (base offset : Z) :
  Z.to_nat (base + offset - base) = Z.to_nat offset.
Proof. f_equal. lia. Qed.

Lemma Z_to_nat_offset_sub_with_frame (base high low : Z) :
  Z.to_nat (base + high - (base + low)) = Z.to_nat (high - low).
Proof. f_equal. lia. Qed.

#[local] Hint Rewrite Z_to_nat_add_sub_base_with_frame
  Z_to_nat_offset_sub_with_frame : write_success_frame_offsets.

Ltac run_write_success_to_load_with_frame :=
  lazymatch goal with
  | |- instr_body 0x14d80 _ => idtac
  | _ =>
      first
        [ progress iEval (unfold zesuMemcpyCallSpec, zesu_c_call)
        | progress iEval (unfold zesuWriteOutputCallSpec, zesu_c_call)
        | liAStep ];
      run_write_success_to_load_with_frame
  end.

Ltac expose_decoded_memory decoded decodedBytes :=
  first
    [ iRename select (bv_unsigned decoded ↦ₘ∗ decodedBytes)%I
        into "HdecodedMemory"
    | liAStep; expose_decoded_memory decoded decodedBytes ].

Ltac expose_decoded_length decodedBytes :=
  lazymatch goal with
  | _ : length decodedBytes = _ |- _ => idtac
  | _ => liAStep; expose_decoded_length decodedBytes
  end.

Lemma write_success_to_load_with_frame
    `{!islaG Sigma} `{!threadG}
    (sp decoded ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : bv 64)
    (decodedBytes : list (bv 8)) (tail : spec) (P : iProp Sigma)
    (Hdecoded : bv_unsigned decoded = (bv_unsigned sp + 0x20)%Z)
    (Hspalign : bv_extract 0 4 sp = BV 4 0)
    (Hspmin : (0x20000880 <= bv_unsigned sp)%Z)
    (Hspmax : (bv_unsigned sp + 0x7d0 < 0x40000000)%Z) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_02.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x101d4 zesuMemcpyCallSpec -∗
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  instr_pre 0x14d80
    (writeSuccessAtLoadHeaderWithFrame (sp - 2000) (take 720 decodedBytes)
      (writeSuccessCallerOutputEventsWithFrame
        (BV 64 0x179c5) (BV 64 6) tail) P) -∗
  instr_body 0x14d7c
    (write_success_prologue_exit sp decoded ra s0 s1 s2 s3 s4 s5 s6 s7
       s8 s9 s10 s11
       ((bv_unsigned sp - 0x7d0) ↦ₘ? 1896 ∗
        bv_unsigned decoded ↦ₘ∗ decodedBytes ∗
        mmio_range 0x2401a0c0 16 ∗
        spec_trace (writeSuccessCallerOutputEventsWithFrame
          (BV 64 0x179c5) (BV 64 6) tail) ∗
        P ∗ ⌜length decodedBytes = 848%nat⌝ ∗
        ⌜(0x20000000 <= bv_unsigned decoded)%Z⌝ ∗
        ⌜(bv_unsigned decoded + 848 < 0x40000000)%Z⌝ ∗
        True)%I).
Proof.
  move => *.
  iStartProof.
  iIntros
    "_ #Hlookup #HspecCode #HmemcpyCode #HoutputCode #Hmemcpy #Houtput
      Hnext".
  iEval (rewrite /instr_lookup_resources) in "Hlookup".
  iPoseProof ("Hlookup" $! 0x14d7c with "[]") as "#Hinstr14d7c".
  { iPureIntro. rewrite IslaTraces.write_success_blocks.Index.lookup_a14d7c.
    done. }
  iPoseProof (IslaTraces.write_success_09.a14d7c_spec.a14d7c_spec
    0x14d7c with "Hinstr14d7c") as "Hjalr".
  rewrite instr_pre'_eq. iIntros "Hentry".
  iEval (rewrite -instr_pre'_eq) in "Hmemcpy".
  iEval (rewrite -instr_pre'_eq) in "Hnext".
  iEval (unfold write_success_prologue_exit) in "Hentry".
  iDestruct "Hentry" as
    "(Hsys & Hother & H1 & H2 & H8 & H9 & H18 & H19 & H20 & H21 & H22 &
      H23 & H24 & H25 & H26 & H27 & H10 & H11 & H12 & Hsaved & Hpayload & _)".
  iDestruct "Hpayload" as
    "(Hframe & HdecodedMemory & Hmmio & Htrace & HP & %HdecodedLength &
      %HdecodedMin & %HdecodedMax & _)".
  assert (Hdecoded_bv : decoded = (sp + BV 64 32)%bv).
  { apply bv_eq. rewrite bv_add_unsigned bv_wrap_small.
    - exact Hdecoded.
    - pose proof (bv_unsigned_in_range 64 sp).
      change (0 <= bv_unsigned sp + 32 < 18446744073709551616)%Z. lia. }
  subst decoded.
  assert (Hdecoded720 :
    Z.to_nat (bv_unsigned (sp + 32) + 720 - bv_unsigned (sp + 32)) =
      720%nat).
  { replace (bv_unsigned (sp + 32) + 720 - bv_unsigned (sp + 32))%Z
      with 720%Z by lia. reflexivity. }
  have HspSub2000 :
      bv_unsigned (sp - 2000) = (bv_unsigned sp - 2000)%Z.
  { rewrite bv_sub_unsigned bv_wrap_small.
    - reflexivity.
    - pose proof (bv_unsigned_in_range 64 sp).
      change (0 <= bv_unsigned sp - 2000 < 18446744073709551616)%Z. lia. }
  have HspSub1688 :
      bv_unsigned (sp - 1688) = (bv_unsigned sp - 1688)%Z.
  { rewrite bv_sub_unsigned bv_wrap_small.
    - reflexivity.
    - pose proof (bv_unsigned_in_range 64 sp).
      change (0 <= bv_unsigned sp - 1688 < 18446744073709551616)%Z. lia. }
  have HspMod16 : bv_unsigned sp `mod` 16 = 0.
  { apply (f_equal bv_unsigned) in Hspalign.
    rewrite bv_extract_0_unsigned in Hspalign.
    unfold bv_wrap, bv_modulus in Hspalign. cbn in Hspalign.
    exact Hspalign. }
  iDestruct (mem_mapsto_uninit_split 312 with "Hframe") as
    "[HloadStack HcopyFrame]"; [lia |].
  iDestruct (mem_mapsto_uninit_split 720 with "HcopyFrame") as
    "[HcopyDestination HheaderDestination]"; [lia |].
  have HcopyAddress :
      (bv_unsigned sp - 2000 + 312)%Z = bv_unsigned (sp - 1688).
  { rewrite HspSub1688. lia. }
  have HheaderAddress :
      (bv_unsigned sp - 2000 + 312 + 720)%Z =
        (bv_unsigned (sp - 2000) + 1032)%Z.
  { rewrite HspSub2000. lia. }
  iEval (rewrite -HspSub2000) in "HloadStack".
  iEval (rewrite HcopyAddress) in "HcopyDestination".
  iEval (rewrite HheaderAddress) in "HheaderDestination".
  have HdecodedRegionBound : (720 + 128 <= length decodedBytes)%nat by lia.
  pose proof (mem_mapsto_array_region 8%N (bv_unsigned (sp + 32))
    (DfracOwn 1) decodedBytes 720 128 HdecodedRegionBound) as HsplitLemma.
  iAssert (
    bv_unsigned (sp + 32) ↦ₘ∗ take 720 decodedBytes ∗
    (bv_unsigned (sp + 32) + 720) ↦ₘ∗
      take 128 (drop 720 decodedBytes) ∗
    (bv_unsigned (sp + 32) + 848) ↦ₘ∗ drop 848 decodedBytes)%I
    with "[HdecodedMemory]" as "Hsplit".
  { iApply HsplitLemma. iExact "HdecodedMemory". }
  iDestruct "Hsplit" as
    "[HdecodedPrefix [HdecodedTail HdecodedSuffix]]".
  set (decodedTail := take 128 (drop 720 decodedBytes)).
  set (decodedWords := u64s_of_bytes 16 decodedTail).
  have HdecodedTailLength : length decodedTail = 128%nat.
  { rewrite /decodedTail length_take length_drop. lia. }
  have HdecodedWordsBytes : bytes_of_u64s decodedWords = decodedTail.
  { apply bytes_of_u64s_of_bytes. exact HdecodedTailLength. }
  iEval (rewrite -HdecodedWordsBytes) in "HdecodedTail".
  iDestruct (mem_mapsto_bytes_to_u64_array with "HdecodedTail") as
    "HdecodedWords".
  iEval (cbn) in "HdecodedWords".
  iApply "Hjalr".
  rewrite /InstrSpecs.Specs.zesu_jalr_same_spec.
  iExists (BV 64 0xfd78).
  iFrame "Hsys H1".
  iSplit; first (iPureIntro; bv_solve).
  have Htarget :
      bv_unsigned
        (bv_or (bv_and ((BV 64 0xfd78) + BV 64 1116)%bv
          (BV 64 18446744073709551614)) (BV 64 0)) = 0x101d4
    by bv_solve.
  rewrite Htarget.
  iApply (instr_pre_wand 0x101d4 0x101d4 true true with "Hmemcpy");
    [done | done |].
  iIntros "HcallEntry".
  iDestruct "HcallEntry" as "(HsysEntry & H1Entry & _)".
  iEval (unfold zesuMemcpyCallSpec, zesu_c_call).
  iExists (sp - 2000)%bv, (BV 64 0x14d80).
  iEval (rewrite /writeSuccessOtherRegShapes /writeSuccessOtherRegisters
    !reg_col_cons reg_col_nil) in "Hother".
  iDestruct "Hother" as
    "(H3 & H4 & H5 & H6 & H7 & H13 & H14 & H15 & H16 & H17 & H28 & H29 &
      H30 & H31 & _)".
  iEval (rewrite /tmp_registers !reg_col_cons reg_col_nil).
  iSplitL "HsysEntry"; first iExact "HsysEntry".
  iSplitL "H5 H6 H7 H28 H29 H30 H31"; first iFrame.
  iDestruct "H13" as (v13 Hv13) "H13".
  apply valu_has_bits_shape in Hv13 as (b13 & ->).
  iDestruct "H14" as (v14 Hv14) "H14".
  apply valu_has_bits_shape in Hv14 as (b14 & ->).
  iDestruct "H15" as (v15 Hv15) "H15".
  apply valu_has_bits_shape in Hv15 as (b15 & ->).
  iDestruct "H16" as (v16 Hv16) "H16".
  apply valu_has_bits_shape in Hv16 as (b16 & ->).
  iDestruct "H17" as (v17 Hv17) "H17".
  apply valu_has_bits_shape in Hv17 as (b17 & ->).
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def).
  iExists (RVal_Bits (sp - 1688)%bv). iFrame "H10".
  iExists (sp - 1688)%bv. iSplit; first done.
  iExists (RVal_Bits (sp + 32)%bv). iFrame "H11".
  iExists (sp + 32)%bv. iSplit; first done.
  iExists (RVal_Bits (BV 64 720)). iFrame "H12".
  iExists (BV 64 720). iSplit; first done.
  iExists (RVal_Bits b13). iFrame "H13". iExists b13. iSplit; first done.
  iExists (RVal_Bits b14). iFrame "H14". iExists b14. iSplit; first done.
  iExists (RVal_Bits b15). iFrame "H15". iExists b15. iSplit; first done.
  iExists (RVal_Bits b16). iFrame "H16". iExists b16. iSplit; first done.
  iExists (RVal_Bits b17). iFrame "H17". iExists b17. iSplit; first done.
  iExists (RVal_Bits (sp + 32)%bv). iFrame "H8". iSplit; first done.
  iExists (RVal_Bits s1). iFrame "H9". iSplit; first done.
  iExists (RVal_Bits s2). iFrame "H18". iSplit; first done.
  iExists (RVal_Bits s3). iFrame "H19". iSplit; first done.
  iExists (RVal_Bits s4). iFrame "H20". iSplit; first done.
  iExists (RVal_Bits s5). iFrame "H21". iSplit; first done.
  iExists (RVal_Bits s6). iFrame "H22". iSplit; first done.
  iExists (RVal_Bits s7). iFrame "H23". iSplit; first done.
  iExists (RVal_Bits s8). iFrame "H24". iSplit; first done.
  iExists (RVal_Bits s9). iFrame "H25". iSplit; first done.
  iExists (RVal_Bits s10). iFrame "H26". iSplit; first done.
  iExists (RVal_Bits s11). iFrame "H27". iSplit; first done.
  iAssert ("x1" ↦ᵣ RVal_Bits (BV 64 0x14d80))%I
    with "[H1Entry]" as "H1target".
  { replace (BV 64 0x14d80) with (Z_to_bv 64 (85372 + 4))
      by bv_solve; iExact "H1Entry". }
  iFrame "H1target H2".
  Unshelve.
  iSplit.
  { iPureIntro. rewrite HspSub2000 Zminus_mod HspMod16.
    all: try lia; try vm_compute. }
  iSplit; first (iPureIntro; bv_solve).
  iSplit; first (iPureIntro; bv_solve).
  iSplit; first (iPureIntro; bv_solve).
  iSplit; first (iPureIntro; rewrite HspSub2000; lia).
  rewrite mem_mapsto_uninit_0.
  iSplit.
  { iPureIntro. pose proof (bv_unsigned_in_range 64 (sp - 2000)%bv). lia. }
  iExists (take 720 decodedBytes).
  iFrame "HdecodedPrefix HcopyDestination".
  repeat iSplit; try iPureIntro; try lia; try assumption; try bv_solve.
  all: try (cbn; rewrite length_take HdecodedLength; lia).
  all: try (change (720 <= length (take 720 decodedBytes))%nat;
    rewrite length_take HdecodedLength; lia).
  all: try (change (720 <= Z.of_nat (length (take 720 decodedBytes)))%Z;
    rewrite length_take HdecodedLength; lia).
  iApply (instr_pre_wand with "Hnext");
    [done | done |].
  iIntros "Hpost".
  iEval (unfold zesu_c_call_ret) in "Hpost".
  iDestruct "Hpost" as
    "(HsysPost & HcallerPost & HsavedPost & HrestPost)".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "HrestPost".
  iDestruct "HrestPost" as (r10Post) "(H10Post & HrestPost)".
  iDestruct "HrestPost" as (b10Post) "(%Hr10Post & HrestPost)".
  iDestruct "HrestPost" as (r11Post) "(H11Post & HrestPost)".
  iDestruct "HrestPost" as
    (b11Post) "(%Hr11Post & H2Post & HzeroPost & HQPost)".
  subst r10Post r11Post.
  iEval (rewrite mem_mapsto_uninit_0) in "HzeroPost".
  iDestruct "HzeroPost" as "[%HzeroPost _]".
  iDestruct "HQPost" as "(HsourcePost & HcopyPost & _)".
  iEval (cbn) in "HsourcePost HcopyPost".
  iEval (unfold writeSuccessAtLoadHeaderWithFrame).
  iExists (sp + 32)%bv, b10Post, b11Post, decodedWords,
    s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11.
  iSplitL "HsysPost HcallerPost HsavedPost H10Post H11Post H2Post".
  { iEval (unfold writeSuccessLoadRegisterResources). iFrame. }
  iFrame "HdecodedWords HloadStack".
  repeat iSplit; try iPureIntro; try assumption; try lia.
  all: try (apply bv_add_32_mod_8_zero; assumption).
  all: try (rewrite <- HspSub2000;
    apply bv_sub_2000_mod_8_zero; assumption).
  all: try (rewrite /decodedWords /u64s_of_bytes length_fmap length_reshape
    length_replicate; done).
  have HresSourceAddress :
      bv_unsigned (sp - 1688) = (bv_unsigned (sp - 2000) + 312)%Z.
  { rewrite HspSub1688 HspSub2000. lia. }
  have HcopyLength : Z.to_nat (bv_unsigned (BV 64 720)) = 720%nat
    by vm_compute.
  have HheaderLength : (1896 - 312 - 720)%Z = 864%Z by lia.
  iEval (rewrite HresSourceAddress HcopyLength) in "HcopyPost".
  iEval (rewrite take_take) in "HcopyPost".
  iEval (cbn) in "HcopyPost".
  iEval (rewrite HheaderLength) in "HheaderDestination".
  iEval (unfold writeSuccessLoadResidual).
  iFrame "HcopyPost HheaderDestination Hmmio Htrace HP".
Qed.
