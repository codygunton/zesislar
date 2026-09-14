Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeSuffixBytes15920.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeSuffixBytesCompose.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderBytesCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessSuffixHashes15750Branch.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessInstrBodyAdapters.
From IslaTraces.write_success_blocks Require Import Index.

Import ListNotations.

(** The aggregate exit keeps all five descriptor resources.  The old
    0x15930 suffix contract exposes descriptor five in registers and keeps
    descriptors one through four in its continuation frame. *)
Definition writeSuccessSuffixBytesAggregateExitAt15930
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp d1 s1 d2 s2 d3 s3 d4 s4 d5 s5 oldS0 oldS1 : bv 64)
      (b1 b2 b3 b4 b5 : list (bv 8)) (tail : spec),
    writeSuccessSuffixAt15930
      (writeSuccessSuffixBytesP5 sp d1 s1 d2 s2 d3 s3 d4 s4 d5 s5
        b1 b2 b3 b4 b5 P))%I.

Global Instance : LithiumUnfold
  (@writeSuccessSuffixBytesAggregateExitAt15930) := I.

(** The zero branch supplies the system register collection and x8.  This
    frame carries the remaining aggregate entry resources. *)
Definition writeSuccessSuffixBytesAggregateEntryZeroFrame
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp d1 s1 d2 s2 d3 s3 d4 s4 d5 s5 oldS1 : bv 64)
      (b1 b2 b3 b4 b5 : list (bv 8)) (tail : spec),
    "x1" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x5" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    "x6" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    "x9" ↦ᵣ RVal_Bits oldS1 ∗
    "x10" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    "x11" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    (bv_unsigned sp - 48) ↦ₘ? 48 ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗
    spec_trace
      (writeOutputEventsAny (sp - BV 64 48)%bv (BV 64 8)
        (writeOutputEventsAny d1 s1
          (writeOutputEventsAny (sp - BV 64 48)%bv (BV 64 8)
            (writeOutputEventsAny d2 s2
              (writeOutputEventsAny (sp - BV 64 48)%bv (BV 64 8)
                (writeOutputEventsAny d3 s3
                  (writeOutputEventsAny (sp - BV 64 48)%bv (BV 64 8)
                    (writeOutputEventsAny d4 s4
                      (writeOutputEventsAny (sp - BV 64 48)%bv (BV 64 8)
                        (writeOutputEventsAny d5 s5 tail)))))))))) ∗
    bv_unsigned d1 ↦ₘ∗ b1 ∗ ⌜bv_unsigned s1 = length b1⌝ ∗
    bv_unsigned d2 ↦ₘ∗ b2 ∗ ⌜bv_unsigned s2 = length b2⌝ ∗
    bv_unsigned d3 ↦ₘ∗ b3 ∗ ⌜bv_unsigned s3 = length b3⌝ ∗
    bv_unsigned d4 ↦ₘ∗ b4 ∗ ⌜bv_unsigned s4 = length b4⌝ ∗
    bv_unsigned d5 ↦ₘ∗ b5 ∗ ⌜bv_unsigned s5 = length b5⌝ ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 48⌝ ∗
    ⌜bv_unsigned sp < (machineRamEnd defaultMap)⌝ ∗
    ⌜bv_unsigned sp + 1896 < (machineRamEnd defaultMap)⌝ ∗
    reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
      writeSuccessSuffixBytesCarrierOtherRegisters) ∗
    (bv_unsigned sp + 920) ↦ₘ d1 ∗ (bv_unsigned sp + 928) ↦ₘ s1 ∗
    (bv_unsigned sp + 936) ↦ₘ d2 ∗ (bv_unsigned sp + 944) ↦ₘ s2 ∗
    (bv_unsigned sp + 952) ↦ₘ d3 ∗ (bv_unsigned sp + 960) ↦ₘ s3 ∗
    (bv_unsigned sp + 968) ↦ₘ d4 ∗ (bv_unsigned sp + 976) ↦ₘ s4 ∗
    (bv_unsigned sp + 984) ↦ₘ d5 ∗ (bv_unsigned sp + 992) ↦ₘ s5 ∗ P ∗ True)%I.

Global Instance : LithiumUnfold
  (@writeSuccessSuffixBytesAggregateEntryZeroFrame) := I.

Lemma write_success_suffix_bytes_aggregate_entry_from_15750_zero
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  writeSuccessSuffixHashes15750ZeroState
      (writeSuccessSuffixBytesAggregateEntryZeroFrame P) -∗
  writeSuccessSuffixBytesAggregateEntry P.
Proof.
  iIntros "Hstate".
  iEval (rewrite /writeSuccessSuffixHashes15750ZeroState) in "Hstate".
  iDestruct "Hstate" as "(Hsys & H8 & Hframe)".
  iEval (rewrite /writeSuccessSuffixBytesAggregateEntryZeroFrame) in "Hframe".
  iDestruct "Hframe" as
    (sp d1 s1 d2 s2 d3 s3 d4 s4 d5 s5 oldS1
      b1 b2 b3 b4 b5 tail)
    "(H1 & H2 & H5 & H6 & H9 & H10 & H11 & Hstack & Hmmio & Htrace &
      Hdata1 & Hlen1 & Hdata2 & Hlen2 & Hdata3 & Hlen3 & Hdata4 & Hlen4 &
      Hdata5 & Hlen5 & Hspmod & Hlow & Hhigh & Hbound & Hregs & HframeData1 &
      HframeSize1 & HframeData2 & HframeSize2 & HframeData3 & HframeSize3 &
      HframeData4 & HframeSize4 & HframeData5 & HframeSize5 & HP & _)".
  rewrite /writeSuccessSuffixBytesAggregateEntry.
  iExists sp, d1, s1, d2, s2, d3, s3, d4, s4, d5, s5,
    (BV 64 0), oldS1, b1, b2, b3, b4, b5, tail.
  iFrame.
  all: lazymatch goal with |- ?G => fail "zero adapter residual" G end.
Qed.

Lemma write_success_suffix_bytes_aggregate_exit_to_15930
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  writeSuccessSuffixBytesAggregateExit P -∗
  writeSuccessSuffixBytesAggregateExitAt15930 P.
Proof.
  iIntros "Hexit".
  iEval (rewrite /writeSuccessSuffixBytesAggregateExit) in "Hexit".
  iDestruct "Hexit" as
    (sp d1 s1 d2 s2 d3 s3 d4 s4 d5 s5 oldS0 oldS1
      b1 b2 b3 b4 b5 tail)
    "(Hsys & H1 & H2 & H5 & H6 & H8 & H9 & H10 & H11 & Hstack & Hmmio &
      Htrace & Hdata1 & Hlen1 & Hdata2 & Hlen2 & Hdata3 & Hlen3 & Hdata4 &
      Hlen4 & Hdata5 & Hlen5 & Hspmod & Hlow & Hhigh & Hbound & Hregs &
      HframeData1 & HframeSize1 & HframeData2 & HframeSize2 & HframeData3 &
      HframeSize3 & HframeData4 & HframeSize4 & HframeData5 & HframeSize5 &
      HP & _)".
  rewrite /writeSuccessSuffixBytesAggregateExitAt15930.
  iExists sp, d1, s1, d2, s2, d3, s3, d4, s4, d5, s5,
    oldS0, oldS1, b1, b2, b3, b4, b5, tail.
  iEval (rewrite /writeSuccessSuffixAt15930
    /writeSuccessSuffixBytes15920Frame
    /writeSuccessSuffixBytesP5
    /writeSuccessSuffixBytesDescriptor) .
  have Haddr928 : bv_unsigned sp + 920 + 8 = bv_unsigned sp + 928 by lia.
  have Haddr944 : bv_unsigned sp + 936 + 8 = bv_unsigned sp + 944 by lia.
  have Haddr960 : bv_unsigned sp + 952 + 8 = bv_unsigned sp + 960 by lia.
  have Haddr976 : bv_unsigned sp + 968 + 8 = bv_unsigned sp + 976 by lia.
  have Haddr992 : bv_unsigned sp + 984 + 8 = bv_unsigned sp + 992 by lia.
  rewrite Haddr928 Haddr944 Haddr960 Haddr976.
  iFrame.
  all: lazymatch goal with |- ?G => fail "adapter residual" G end.
Qed.

Lemma write_success_native_suffix_bytes_15750_zero_segment
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15c6c zesuEncoderBytesCallSpec -∗
  instr 0x15750 (Some IslaTraces.write_success_102.a15750.a15750) -∗
  instr_body 0x15930 (writeSuccessSuffixBytesAggregateExitAt15930 P) -∗
  instr_body 0x15750
    (writeSuccessSuffixHashes15750ZeroState
      (writeSuccessSuffixBytesAggregateEntryZeroFrame P)).
Proof.
  iStartProof.
  iIntros "#Hlookup #Hcode #Hbytes Hbranch Hnext".
  iPoseProof (write_success_suffix_bytes_aggregate_exit_to_15930 P) as
    "HexitWand".
  iPoseProof (instr_body_wand_adapter 0x15930
    (writeSuccessSuffixBytesAggregateExitAt15930 P)
    (writeSuccessSuffixBytesAggregateExit P)
    with "HexitWand Hnext") as "HnextAgg".
  iPoseProof (write_success_native_suffix_bytes_158e0_to_15930 P
    with "Hlookup Hcode Hbytes HnextAgg") as "Hbody158e0".
  iPoseProof (instr_pre_to_body 0x158e0
    (writeSuccessSuffixBytesAggregateEntry P) with "Hbody158e0") as
    "HpreAggregate".
  iApply (write_success_suffix_hashes_15750_zero_state
    (writeSuccessSuffixBytesAggregateEntryZeroFrame P) with "Hbranch").
  iApply (instr_pre_wand 0x158e0 0x158e0 true true
    (writeSuccessSuffixBytesAggregateEntry P)
    (writeSuccessSuffixHashes15750ZeroState
      (writeSuccessSuffixBytesAggregateEntryZeroFrame P))
    with "HpreAggregate"); [done | reflexivity |].
  iApply (write_success_suffix_bytes_aggregate_entry_from_15750_zero P).
Qed.
