Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCalls.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactEncoderBytes.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactEncoderIntCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactHeaderBlock.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactHeaderSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactValueBlock.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactValueSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessHeaderSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeContract.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPayloadCall.

Definition writeSuccessExactHeaderValueFrame `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) (sp : bv 64) (bytes : list (bv 8)) :
    iProp Sigma :=
  ((bv_unsigned sp + 312) ↦ₘ∗ bytes ∗
   (bv_unsigned sp + 1624) ↦ₘ? 272 ∗
   writeSuccessNativeStaticResources ∗ P)%I.

Global Instance : LithiumUnfold (@writeSuccessExactHeaderValueFrame) := I.

Definition writeSuccessExactHeaderValueTransition `{!islaG Sigma}
    `{!threadG} (P : iProp Sigma) (sp : bv 64)
    (bytes : list (bv 8)) (values : list (bv 64))
    (payload : list (bv 8)) (tail : spec) : iProp Sigma :=
  ((bv_unsigned sp - 48) ↦ₘ? 48 ∗
   bv_unsigned (writeSuccessExactValueWord values 4) ↦ₘ∗ payload ∗
   ⌜length values = 74%nat⌝ ∗
   ⌜bytes_of_u64s values = take 592 bytes⌝ ∗
   ⌜bv_unsigned (writeSuccessExactValueWord values 5) = length payload⌝ ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 48⌝ ∗
   ⌜bv_unsigned sp + 1896 < (machineRamEnd defaultMap)⌝ ∗ P ∗
   instr_pre 0x14f04
     (writeSuccessExactValuePost sp values payload tail
       (writeSuccessExactHeaderValueFrame P sp bytes)))%I.

Global Instance : LithiumUnfold (@writeSuccessExactHeaderValueTransition) := I.

Lemma writeSuccessExactHeaderPost_to_value `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) (sp : bv 64) (bytes : list (bv 8))
    (values : list (bv 64)) (payload : list (bv 8)) (tail : spec) :
  writeSuccessExactHeaderPost sp bytes
    (writeSuccessExactValueEvents sp values payload tail)
    (writeSuccessNativeStaticResources ∗
      writeSuccessExactHeaderValueTransition P sp bytes values payload tail) -∗
  writeSuccessExactValueSpec
    (writeSuccessExactHeaderValueFrame P sp bytes).
Proof.
  iIntros "Hpost".
  iPoseProof (writeSuccessExactHeaderPost_to_standard with
    "Hpost") as "Hstandard".
  rewrite /writeSuccessHeaderPost.
  iDestruct "Hstandard" as
    "(Hsys & Hregs & H2 & Hgap & Hbytes & Hcopy & Hhigh & Hmmio & Htrace &
      Hresources & _)".
  iDestruct "Hresources" as "[Hstatic Htransition]".
  rewrite /writeSuccessExactHeaderValueTransition.
  iDestruct "Htransition" as
    "(Hlow & Hpayload & %HvaluesLength & %HvaluesBytes & %HpayloadLength &
      %Halign16 & %Halign8 & %Hmin & %Hmax & HP & Hnext)".
  iPoseProof (writeSuccessExactValueMemory_from_bytes sp bytes values
    HvaluesLength HvaluesBytes with "Hcopy") as "HvalueMemory".
  rewrite /writeSuccessExactValueSpec.
  iExists sp, values, payload, tail.
  iFrame "Hsys Hregs H2 Hlow Hgap HvalueMemory Hpayload Hmmio Htrace".
  repeat iSplit; try iPureIntro; try assumption; try iFrame.
Qed.

Print Assumptions writeSuccessExactHeaderPost_to_value.

Lemma writeSuccessHeaderPost_to_exact `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (bytes : list (bv 8)) (tail : spec) (P : iProp Sigma) :
  length bytes = 720%nat ->
  writeSuccessHeaderPost sp bytes tail P -∗
  writeSuccessExactHeaderPost sp bytes tail P.
Proof.
  intros Hlength. iIntros "Hpost".
  rewrite /writeSuccessHeaderPost /writeSuccessExactHeaderPost.
  iDestruct "Hpost" as
    "(Hsys & Hregs & H2 & Hgap & Hbytes & Hcopy & Hhigh & Hmmio & Htrace &
      HP & _)".
  iDestruct (mem_mapsto_array_app 8%N (bv_unsigned sp + 1032)
    (DfracOwn 1) (take 524 (take 592 bytes))
    (drop 524 (take 592 bytes)) with "[Hcopy]") as "[Hprefix Hrest]".
  { rewrite take_drop. iFrame. }
  have HprefixLength : length (take 524 (take 592 bytes)) = 524%nat.
  { rewrite !length_take Hlength. done. }
  iEval (rewrite HprefixLength /=) in "Hrest".
  iEval (replace (bv_unsigned sp + 1032 + 524) with
    (bv_unsigned sp + 1556) by lia) in "Hrest".
  iDestruct (mem_mapsto_array_app 8%N (bv_unsigned sp + 1556)
    (DfracOwn 1) (take 32 (drop 524 (take 592 bytes)))
    (drop 32 (drop 524 (take 592 bytes))) with "[Hrest]")
    as "[Hmiddle Hsuffix]".
  { rewrite take_drop. iFrame. }
  have HmiddleLength :
      length (take 32 (drop 524 (take 592 bytes))) = 32%nat.
  { rewrite length_take length_drop !length_take Hlength. done. }
  iEval (rewrite HmiddleLength /=) in "Hsuffix".
  iEval (rewrite drop_drop Nat.add_comm) in "Hsuffix".
  iEval (replace (bv_unsigned sp + 1556 + 32) with
    (bv_unsigned sp + 1588) by lia) in "Hsuffix".
  rewrite /writeSuccessHeaderPayload.
  iFrame. iPureIntro. exact Hlength.
Qed.

Print Assumptions writeSuccessHeaderPost_to_exact.

Definition writeSuccessExactHeaderValueSpec `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) (sp : bv 64) (bytes : list (bv 8))
    (values : list (bv 64)) (payload : list (bv 8)) (tail : spec) :
    iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ reg_col writeSuccessHeaderRegShapes ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   (bv_unsigned sp + 104) ↦ₘ? 16 ∗
   (bv_unsigned sp + 312) ↦ₘ∗ bytes ∗
   (bv_unsigned sp + 1032) ↦ₘ? 864 ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace (writeSuccessExactHeaderEvents sp bytes
     (writeSuccessExactValueEvents sp values payload tail)) ∗
   ⌜length bytes = 720%nat⌝ ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp + 1896 < (machineRamEnd defaultMap)⌝ ∗
   writeSuccessNativeStaticResources ∗
   writeSuccessExactHeaderValueTransition P sp bytes values payload tail ∗
   True)%I.

Global Instance : LithiumUnfold (@writeSuccessExactHeaderValueSpec) := I.

Lemma write_success_exact_header_value `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) (sp : bv 64) (bytes : list (bv 8))
    (values : list (bv 64)) (payload : list (bv 8)) (tail : spec) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x101d4 zesuMemcpyCallSpec -∗
  □ instr_pre 0x10190 zesuWriteOutputPayloadCallSpec -∗
  □ instr_pre 0x15d10 zesuEncoderIntPayloadCallSpec -∗
  □ instr_pre 0x15c6c encoderBytesExactCallSpec -∗
  instr_body 0x14e00
    (writeSuccessExactHeaderValueSpec P sp bytes values payload tail).
Proof.
  iStartProof.
  iIntros "#Hlookup #Hcode #Hmemcpy #Houtput #Hint #Hbytes".
  iPoseProof (write_success_exact_value_block
    (writeSuccessExactHeaderValueFrame P sp bytes) with
    "Hlookup Hcode Houtput Hint Hbytes") as "Hvalue".
  iPoseProof (write_success_exact_header_block
    (writeSuccessExactHeaderValueTransition P sp bytes values payload tail)
    with "Hlookup Hcode Hmemcpy Houtput") as "Hheader".
  iApply (instr_pre_wand 0x14e00 0x14e00 false false with "Hheader");
    [done | reflexivity |].
  iIntros "Hentry".
  iEval (rewrite /writeSuccessExactHeaderValueSpec) in "Hentry".
  iDestruct "Hentry" as
    "(Hsys & Hregs & H2 & Hgap & Hsource & Hdestination & Hmmio & Htrace &
      %Hlength & %Halign & %Hmin & %Hmax & Hstatic & Htransition & _)".
  iAssert (instr_pre 0x14e88
      (writeSuccessHeaderPost sp bytes
        (writeSuccessExactValueEvents sp values payload tail)
        (writeSuccessNativeStaticResources ∗
          writeSuccessExactHeaderValueTransition P sp bytes values payload tail)))%I
    with "[Hvalue]" as "HvaluePre".
  { iApply instr_pre_to_body. iNext.
    iApply (instr_pre_wand 0x14e88 0x14e88 false false with "Hvalue");
      [done | reflexivity |].
    iIntros "Hpost".
    iApply writeSuccessExactHeaderPost_to_value.
    iApply (writeSuccessHeaderPost_to_exact sp bytes _ _ Hlength with "Hpost"). }
  rewrite /writeSuccessExactHeaderSpec /writeSuccessHeaderBeforeCopySpec.
  iExists sp, bytes,
    (writeSuccessExactValueEvents sp values payload tail).
  iFrame "Hsys Hregs H2 Hgap Hsource Hdestination Hmmio Htrace Htransition
    Hstatic HvaluePre".
  repeat iSplit; try iPureIntro; try assumption; try iFrame.
Qed.

Print Assumptions write_success_exact_header_value.
