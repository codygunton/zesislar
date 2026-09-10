Require Import ZesuSsz.Automation.All.
From IslaTraces.write_success_blocks Require Import Index.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderBytesCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.

Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeSuffixBytes158e0Carrier.

Import ListNotations.

Definition writeSuccessSuffixBytesCarrierOtherRegisters : list string :=
  ["x3"; "x4"; "x7"; "x12"; "x13"; "x14"; "x15"; "x16"; "x17";
   "x18"; "x19"; "x20"; "x21"; "x22"; "x23"; "x24"; "x25";
   "x26"; "x27"; "x28"; "x29"; "x30"; "x31"].

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Definition writeSuccessSuffixBytesAggregateEntry `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp d1 s1 d2 s2 d3 s3 d4 s4 d5 s5 oldS0 oldS1 : bv 64)
      (b1 b2 b3 b4 b5 : list (bv 8)) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x5" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    "x6" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    "x8" ↦ᵣ RVal_Bits oldS0 ∗ "x9" ↦ᵣ RVal_Bits oldS1 ∗
    "x10" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    "x11" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    (bv_unsigned sp - 48) ↦ₘ? 48 ∗ mmio_range 0x2401a0c0 16 ∗
    spec_trace
      (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
        (writeOutputEvents d1 s1
          (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
            (writeOutputEvents d2 s2
              (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
                (writeOutputEvents d3 s3
                  (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
                    (writeOutputEvents d4 s4
                      (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
                        (writeOutputEvents d5 s5 tail)))))))))) ∗
    bv_unsigned d1 ↦ₘ∗ b1 ∗ ⌜bv_unsigned s1 = length b1⌝ ∗
    bv_unsigned d2 ↦ₘ∗ b2 ∗ ⌜bv_unsigned s2 = length b2⌝ ∗
    bv_unsigned d3 ↦ₘ∗ b3 ∗ ⌜bv_unsigned s3 = length b3⌝ ∗
    bv_unsigned d4 ↦ₘ∗ b4 ∗ ⌜bv_unsigned s4 = length b4⌝ ∗
    bv_unsigned d5 ↦ₘ∗ b5 ∗ ⌜bv_unsigned s5 = length b5⌝ ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned sp - 48⌝ ∗
    ⌜bv_unsigned sp < 0x40000000⌝ ∗
    ⌜bv_unsigned sp + 1896 < 0x40000000⌝ ∗
    reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
      writeSuccessSuffixBytesCarrierOtherRegisters) ∗
    (bv_unsigned sp + 920) ↦ₘ d1 ∗ (bv_unsigned sp + 928) ↦ₘ s1 ∗
    (bv_unsigned sp + 936) ↦ₘ d2 ∗ (bv_unsigned sp + 944) ↦ₘ s2 ∗
    (bv_unsigned sp + 952) ↦ₘ d3 ∗ (bv_unsigned sp + 960) ↦ₘ s3 ∗
    (bv_unsigned sp + 968) ↦ₘ d4 ∗ (bv_unsigned sp + 976) ↦ₘ s4 ∗
    (bv_unsigned sp + 984) ↦ₘ d5 ∗ (bv_unsigned sp + 992) ↦ₘ s5 ∗ P ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessSuffixBytesAggregateEntry) := I.

Definition writeSuccessSuffixBytesAggregateExit `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp d1 s1 d2 s2 d3 s3 d4 s4 d5 s5 oldS0 oldS1 : bv 64)
      (b1 b2 b3 b4 b5 : list (bv 8)) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits (BV 64 0x15930) ∗ "x2" ↦ᵣ RVal_Bits sp ∗
    "x5" ↦ᵣ RVal_Bits (BV 64 0x2401a0b8) ∗
    "x6" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    "x8" ↦ᵣ RVal_Bits oldS0 ∗ "x9" ↦ᵣ RVal_Bits oldS1 ∗
    "x10" ↦ᵣ RVal_Bits d5 ∗ "x11" ↦ᵣ RVal_Bits s5 ∗
    (bv_unsigned sp - 48) ↦ₘ? 48 ∗ mmio_range 0x2401a0c0 16 ∗
    spec_trace tail ∗
    bv_unsigned d1 ↦ₘ∗ b1 ∗ ⌜bv_unsigned s1 = length b1⌝ ∗
    bv_unsigned d2 ↦ₘ∗ b2 ∗ ⌜bv_unsigned s2 = length b2⌝ ∗
    bv_unsigned d3 ↦ₘ∗ b3 ∗ ⌜bv_unsigned s3 = length b3⌝ ∗
    bv_unsigned d4 ↦ₘ∗ b4 ∗ ⌜bv_unsigned s4 = length b4⌝ ∗
    bv_unsigned d5 ↦ₘ∗ b5 ∗ ⌜bv_unsigned s5 = length b5⌝ ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned sp - 48⌝ ∗
    ⌜bv_unsigned sp < 0x40000000⌝ ∗
    ⌜bv_unsigned sp + 1896 < 0x40000000⌝ ∗
    reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
      writeSuccessSuffixBytesCarrierOtherRegisters) ∗
    (bv_unsigned sp + 920) ↦ₘ d1 ∗ (bv_unsigned sp + 928) ↦ₘ s1 ∗
    (bv_unsigned sp + 936) ↦ₘ d2 ∗ (bv_unsigned sp + 944) ↦ₘ s2 ∗
    (bv_unsigned sp + 952) ↦ₘ d3 ∗ (bv_unsigned sp + 960) ↦ₘ s3 ∗
    (bv_unsigned sp + 968) ↦ₘ d4 ∗ (bv_unsigned sp + 976) ↦ₘ s4 ∗
    (bv_unsigned sp + 984) ↦ₘ d5 ∗ (bv_unsigned sp + 992) ↦ₘ s5 ∗ P ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessSuffixBytesAggregateExit) := I.

Definition writeSuccessSuffixBytesDescriptor `{!islaG Sigma} `{!threadG}
    (sp data size : bv 64) (bytes : list (bv 8)) (offset : Z) : iProp Sigma :=
  ((bv_unsigned sp + offset) ↦ₘ data ∗
   (bv_unsigned sp + offset + 8) ↦ₘ size ∗
   bv_unsigned data ↦ₘ∗ bytes ∗ ⌜bv_unsigned size = length bytes⌝)%I.

Definition writeSuccessSuffixBytesP1 `{!islaG Sigma} `{!threadG}
    (sp d1 s1 d2 s2 d3 s3 d4 s4 d5 s5 : bv 64)
    (b1 b2 b3 b4 b5 : list (bv 8)) (P : iProp Sigma) : iProp Sigma :=
  (writeSuccessSuffixBytesDescriptor sp d2 s2 b2 936 ∗
   writeSuccessSuffixBytesDescriptor sp d3 s3 b3 952 ∗
   writeSuccessSuffixBytesDescriptor sp d4 s4 b4 968 ∗
   writeSuccessSuffixBytesDescriptor sp d5 s5 b5 984 ∗ P)%I.

Definition writeSuccessSuffixBytesP2 `{!islaG Sigma} `{!threadG}
    (sp d1 s1 d2 s2 d3 s3 d4 s4 d5 s5 : bv 64)
    (b1 b2 b3 b4 b5 : list (bv 8)) (P : iProp Sigma) : iProp Sigma :=
  (writeSuccessSuffixBytesDescriptor sp d1 s1 b1 920 ∗
   writeSuccessSuffixBytesDescriptor sp d3 s3 b3 952 ∗
   writeSuccessSuffixBytesDescriptor sp d4 s4 b4 968 ∗
   writeSuccessSuffixBytesDescriptor sp d5 s5 b5 984 ∗ P)%I.

Definition writeSuccessSuffixBytesP3 `{!islaG Sigma} `{!threadG}
    (sp d1 s1 d2 s2 d3 s3 d4 s4 d5 s5 : bv 64)
    (b1 b2 b3 b4 b5 : list (bv 8)) (P : iProp Sigma) : iProp Sigma :=
  (writeSuccessSuffixBytesDescriptor sp d1 s1 b1 920 ∗
   writeSuccessSuffixBytesDescriptor sp d2 s2 b2 936 ∗
   writeSuccessSuffixBytesDescriptor sp d4 s4 b4 968 ∗
   writeSuccessSuffixBytesDescriptor sp d5 s5 b5 984 ∗ P)%I.

Definition writeSuccessSuffixBytesP4 `{!islaG Sigma} `{!threadG}
    (sp d1 s1 d2 s2 d3 s3 d4 s4 d5 s5 : bv 64)
    (b1 b2 b3 b4 b5 : list (bv 8)) (P : iProp Sigma) : iProp Sigma :=
  (writeSuccessSuffixBytesDescriptor sp d1 s1 b1 920 ∗
   writeSuccessSuffixBytesDescriptor sp d2 s2 b2 936 ∗
   writeSuccessSuffixBytesDescriptor sp d3 s3 b3 952 ∗
   writeSuccessSuffixBytesDescriptor sp d5 s5 b5 984 ∗ P)%I.

Definition writeSuccessSuffixBytesP5 `{!islaG Sigma} `{!threadG}
    (sp d1 s1 d2 s2 d3 s3 d4 s4 d5 s5 : bv 64)
    (b1 b2 b3 b4 b5 : list (bv 8)) (P : iProp Sigma) : iProp Sigma :=
  (writeSuccessSuffixBytesDescriptor sp d1 s1 b1 920 ∗
   writeSuccessSuffixBytesDescriptor sp d2 s2 b2 936 ∗
   writeSuccessSuffixBytesDescriptor sp d3 s3 b3 952 ∗
   writeSuccessSuffixBytesDescriptor sp d4 s4 b4 968 ∗ P)%I.

Lemma write_success_suffix_bytes_exit_adapter
    `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma)
    (sp d1 s1 d2 s2 d3 s3 d4 s4 d5 s5 oldS0 oldS1 : bv 64)
    (b1 b2 b3 b4 b5 : list (bv 8)) (tail : spec) :
  writeSuccessSuffixBytesAt15930Carrier sp
      (writeSuccessSuffixBytesP5 sp d1 s1 d2 s2 d3 s3 d4 s4 d5 s5
        b1 b2 b3 b4 b5 P) -∗
  writeSuccessSuffixBytesAggregateExit P.
Proof.
  iIntros "H".
  iEval (rewrite /writeSuccessSuffixBytesAt15930Carrier /writeSuccessSuffixBytesCarrierState).
  iDestruct "H" as
    "(%data & %size & %oldS0' & %oldS1' & %bytes & %tail' & H)".
  iEval (rewrite /writeSuccessSuffixBytesP5) in "H".
  iEval (rewrite /writeSuccessSuffixBytesDescriptor) in "H".
  iEval (rewrite /writeSuccessSuffixBytesCarrierExactReg
    /writeSuccessSuffixBytesCarrierShapeReg
    /writeSuccessSuffixBytesCarrierOtherRegisters) in "H".
  rewrite /writeSuccessSuffixBytesAggregateExit.
  iExists sp, d1, s1, d2, s2, d3, s3, d4, s4, data, size,
    oldS0', oldS1', b1, b2, b3, b4, bytes, tail'.
  have Haddr928 : bv_unsigned sp + 920 + 8 = bv_unsigned sp + 928 by lia.
  have Haddr944 : bv_unsigned sp + 936 + 8 = bv_unsigned sp + 944 by lia.
  have Haddr960 : bv_unsigned sp + 952 + 8 = bv_unsigned sp + 960 by lia.
  have Haddr976 : bv_unsigned sp + 968 + 8 = bv_unsigned sp + 976 by lia.
  have Haddr992 : bv_unsigned sp + 984 + 8 = bv_unsigned sp + 992 by lia.
  have Haddr992' : bv_unsigned sp + (984 + 8) = bv_unsigned sp + 992 by lia.
  iEval (rewrite Haddr928 Haddr944 Haddr960 Haddr976 Haddr992') in "H".
  iEval (rewrite /writeSuccessSuffixBytesCarrierOtherRegisters).
  iDestruct "H" as
    "(Hsys & H1 & H2 & H5 & H6 & H8 & H9 & H10 & H11 & Hstack & Hmmio &
      Htrace & Hdata & Hlen & Hspmod & Hlow & Hhigh & Hbound & Hregs &
      HframeData & HframeSize & Hdesc & _)".
  iDestruct "Hdesc" as
    "(Hdesc1 & Hdesc2 & Hdesc3 & Hdesc4 & HP)".
  iDestruct "Hdesc1" as "(Hd1 & Hs1 & Hb1 & Hl1)".
  iDestruct "Hdesc2" as "(Hd2 & Hs2 & Hb2 & Hl2)".
  iDestruct "Hdesc3" as "(Hd3 & Hs3 & Hb3 & Hl3)".
  iDestruct "Hdesc4" as "(Hd4 & Hs4 & Hb4 & Hl4)".
  iFrame.
Qed.

Lemma write_success_suffix_bytes_rotate_158f0
    `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma)
    (sp d1 s1 d2 s2 d3 s3 d4 s4 d5 s5 oldS0 oldS1 : bv 64)
    (b1 b2 b3 b4 b5 : list (bv 8)) (tail : spec) :
  writeSuccessSuffixBytesAt158f0CarrierExactData sp d1 s1 oldS0 oldS1 b1
      (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
        (writeOutputEvents d2 s2
          (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
            (writeOutputEvents d3 s3
              (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
                (writeOutputEvents d4 s4
                  (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
                    (writeOutputEvents d5 s5 tail))))))))
      (writeSuccessSuffixBytesP1 sp d1 s1 d2 s2 d3 s3 d4 s4 d5 s5
        b1 b2 b3 b4 b5 P) -∗
  writeSuccessSuffixBytesAt15900CarrierData sp d2 s2 oldS0 oldS1 b2
      (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
        (writeOutputEvents d2 s2
          (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
            (writeOutputEvents d3 s3
              (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
                (writeOutputEvents d4 s4
                  (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
                    (writeOutputEvents d5 s5 tail))))))))
      (writeSuccessSuffixBytesP2 sp d1 s1 d2 s2 d3 s3 d4 s4 d5 s5
        b1 b2 b3 b4 b5 P).
Proof.
  iIntros "H".
  iEval (rewrite /writeSuccessSuffixBytesAt158f0CarrierExactData
    /writeSuccessSuffixBytesCarrierExactState) in "H".
  iEval (rewrite /writeSuccessSuffixBytesP1) in "H".
  iEval (rewrite /writeSuccessSuffixBytesDescriptor
    /writeSuccessSuffixBytesCarrierExactReg
    /writeSuccessSuffixBytesCarrierShapeReg
    /writeSuccessSuffixBytesCarrierOtherRegisters) in "H".
  iEval (rewrite /writeSuccessSuffixBytesAt15900CarrierData
    /writeSuccessSuffixBytesCarrierDataState).
  iEval (rewrite /writeSuccessSuffixBytesP2 /writeSuccessSuffixBytesDescriptor).
  iEval (rewrite /writeSuccessSuffixBytesCarrierExactReg
    /writeSuccessSuffixBytesCarrierShapeReg
    /writeSuccessSuffixBytesCarrierOtherRegisters).
  have Haddr928 : bv_unsigned sp + 920 + 8 = bv_unsigned sp + 928 by lia.
  have Haddr944 : bv_unsigned sp + 936 + 8 = bv_unsigned sp + 944 by lia.
  iDestruct "H" as
    "(Hsys & H1 & H2 & H5 & H6 & H8 & H9 & H10 & H11 & Hstack & Hmmio &
      Htrace & Hdata & Hlen & Hspmod & Hlow & Hhigh & Hbound & Hregs & HframeData &
      HframeSize & Hdesc & _)".
  iDestruct "Hdesc" as "(Hdesc2 & Hdesc3 & Hdesc4 & Hdesc5 & HP)".
  iDestruct "Hdesc2" as "(Hd2 & Hs2 & Hb2 & Hl2)".
  iDestruct "Hdesc3" as "(Hd3 & Hs3 & Hb3 & Hl3)".
  iDestruct "Hdesc4" as "(Hd4 & Hs4 & Hb4 & Hl4)".
  iDestruct "Hdesc5" as "(Hd5 & Hs5 & Hb5 & Hl5)".
  iAssert (("x1" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝))%I)
    with "[H1]" as "H1shape".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists (RVal_Bits (BV 64 0x158f0)). iFrame. iPureIntro. bv_solve. }
  iAssert (("x5" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝))%I)
    with "[H5]" as "H5shape".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists (RVal_Bits (BV 64 0x2401a0b8)). iFrame. iPureIntro. bv_solve. }
  iAssert (("x10" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝))%I)
    with "[H10]" as "H10shape".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists (RVal_Bits d1). iFrame. iPureIntro. bv_solve. }
  iAssert (("x11" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝))%I)
    with "[H11]" as "H11shape".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists (RVal_Bits s1). iFrame. iPureIntro. bv_solve. }
  have Haddr928L : bv_unsigned sp + 920 + 8 = bv_unsigned sp + 928 by lia.
  have Haddr928R : bv_unsigned sp + (920 + 8) = bv_unsigned sp + 928 by lia.
  have Haddr944L : bv_unsigned sp + 936 + 8 = bv_unsigned sp + 944 by lia.
  have Haddr944R : bv_unsigned sp + (936 + 8) = bv_unsigned sp + 944 by lia.
  iEval (rewrite Haddr928R) in "HframeSize".
  iEval (rewrite Haddr944L) in "Hs2".
  iEval (rewrite Haddr928L Haddr944R).
  iFrame.
Qed.

Lemma write_success_suffix_bytes_rotate_15900
    `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma)
    (sp d1 s1 d2 s2 d3 s3 d4 s4 d5 s5 oldS0 oldS1 : bv 64)
    (b1 b2 b3 b4 b5 : list (bv 8)) (tail : spec) :
  writeSuccessSuffixBytesAt15900CarrierExactData sp d2 s2 oldS0 oldS1 b2
      (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
        (writeOutputEvents d3 s3
          (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
            (writeOutputEvents d4 s4
              (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
                (writeOutputEvents d5 s5 tail))))))
      (writeSuccessSuffixBytesP2 sp d1 s1 d2 s2 d3 s3 d4 s4 d5 s5
        b1 b2 b3 b4 b5 P) -∗
  writeSuccessSuffixBytesAt15910CarrierData sp d3 s3 oldS0 oldS1 b3
      (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
        (writeOutputEvents d3 s3
          (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
            (writeOutputEvents d4 s4
              (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
                (writeOutputEvents d5 s5 tail))))))
      (writeSuccessSuffixBytesP3 sp d1 s1 d2 s2 d3 s3 d4 s4 d5 s5
        b1 b2 b3 b4 b5 P).
Proof.
  iIntros "H".
  iEval (rewrite /writeSuccessSuffixBytesAt15900CarrierExactData
    /writeSuccessSuffixBytesCarrierExactState) in "H".
  iEval (rewrite /writeSuccessSuffixBytesP2 /writeSuccessSuffixBytesDescriptor) in "H".
  iEval (rewrite /writeSuccessSuffixBytesAt15910CarrierData
    /writeSuccessSuffixBytesCarrierDataState).
  iEval (rewrite /writeSuccessSuffixBytesP3 /writeSuccessSuffixBytesDescriptor).
  iDestruct "H" as
    "(Hsys & H1 & H2 & H5 & H6 & H8 & H9 & H10 & H11 & Hstack & Hmmio &
      Htrace & Hdata & Hlen & Hspmod & Hlow & Hhigh & Hbound & Hregs & HframeData &
      HframeSize & Hdesc & _)".
  iDestruct "Hdesc" as "(Hdesc1 & Hdesc3 & Hdesc4 & Hdesc5 & HP)".
  iDestruct "Hdesc1" as "(Hd1 & Hs1 & Hb1 & Hl1)".
  iDestruct "Hdesc3" as "(Hd3 & Hs3 & Hb3 & Hl3)".
  iDestruct "Hdesc4" as "(Hd4 & Hs4 & Hb4 & Hl4)".
  iDestruct "Hdesc5" as "(Hd5 & Hs5 & Hb5 & Hl5)".
  iAssert (("x1" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝))%I)
    with "[H1]" as "H1shape".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists (RVal_Bits (BV 64 0x15900)). iFrame. iPureIntro. bv_solve. }
  iAssert (("x5" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝))%I)
    with "[H5]" as "H5shape".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists (RVal_Bits (BV 64 0x2401a0b8)). iFrame. iPureIntro. bv_solve. }
  iAssert (("x10" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝))%I)
    with "[H10]" as "H10shape".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists (RVal_Bits d2). iFrame. iPureIntro. bv_solve. }
  iAssert (("x11" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝))%I)
    with "[H11]" as "H11shape".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists (RVal_Bits s2). iFrame. iPureIntro. bv_solve. }
  have Haddr944L : bv_unsigned sp + 936 + 8 = bv_unsigned sp + 944 by lia.
  have Haddr944R : bv_unsigned sp + (936 + 8) = bv_unsigned sp + 944 by lia.
  have Haddr960L : bv_unsigned sp + 952 + 8 = bv_unsigned sp + 960 by lia.
  have Haddr960R : bv_unsigned sp + (952 + 8) = bv_unsigned sp + 960 by lia.
  iEval (rewrite Haddr944R) in "HframeSize".
  iEval (rewrite Haddr960L) in "Hs3".
  iEval (rewrite Haddr944L Haddr960R).
  iFrame.
  all: match goal with |- ?G => idtac G end.
Qed.

Lemma write_success_suffix_bytes_rotate_15910
    `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma)
    (sp d1 s1 d2 s2 d3 s3 d4 s4 d5 s5 oldS0 oldS1 : bv 64)
    (b1 b2 b3 b4 b5 : list (bv 8)) (tail : spec) :
  writeSuccessSuffixBytesAt15910CarrierExactData sp d3 s3 oldS0 oldS1 b3
      (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
        (writeOutputEvents d4 s4
          (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
            (writeOutputEvents d5 s5 tail))))
      (writeSuccessSuffixBytesP3 sp d1 s1 d2 s2 d3 s3 d4 s4 d5 s5
        b1 b2 b3 b4 b5 P) -∗
  writeSuccessSuffixBytesAt15920CarrierData sp d4 s4 oldS0 oldS1 b4
      (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
        (writeOutputEvents d4 s4
          (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
            (writeOutputEvents d5 s5 tail))))
      (writeSuccessSuffixBytesP4 sp d1 s1 d2 s2 d3 s3 d4 s4 d5 s5
        b1 b2 b3 b4 b5 P).
Proof.
  iIntros "H".
  iEval (rewrite /writeSuccessSuffixBytesAt15910CarrierExactData
    /writeSuccessSuffixBytesCarrierExactState) in "H".
  iEval (rewrite /writeSuccessSuffixBytesP3 /writeSuccessSuffixBytesDescriptor) in "H".
  iEval (rewrite /writeSuccessSuffixBytesAt15920CarrierData
    /writeSuccessSuffixBytesCarrierDataState).
  iEval (rewrite /writeSuccessSuffixBytesP4 /writeSuccessSuffixBytesDescriptor).
  iDestruct "H" as
    "(Hsys & H1 & H2 & H5 & H6 & H8 & H9 & H10 & H11 & Hstack & Hmmio &
      Htrace & Hdata & Hlen & Hspmod & Hlow & Hhigh & Hbound & Hregs & HframeData &
      HframeSize & Hdesc & _)".
  iDestruct "Hdesc" as "(Hdesc1 & Hdesc2 & Hdesc4 & Hdesc5 & HP)".
  iDestruct "Hdesc1" as "(Hd1 & Hs1 & Hb1 & Hl1)".
  iDestruct "Hdesc2" as "(Hd2 & Hs2 & Hb2 & Hl2)".
  iDestruct "Hdesc4" as "(Hd4 & Hs4 & Hb4 & Hl4)".
  iDestruct "Hdesc5" as "(Hd5 & Hs5 & Hb5 & Hl5)".
  iAssert (("x1" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝))%I)
    with "[H1]" as "H1shape".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists (RVal_Bits (BV 64 0x15910)). iFrame. iPureIntro. bv_solve. }
  iAssert (("x5" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝))%I)
    with "[H5]" as "H5shape".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists (RVal_Bits (BV 64 0x2401a0b8)). iFrame. iPureIntro. bv_solve. }
  iAssert (("x10" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝))%I)
    with "[H10]" as "H10shape".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists (RVal_Bits d3). iFrame. iPureIntro. bv_solve. }
  iAssert (("x11" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝))%I)
    with "[H11]" as "H11shape".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists (RVal_Bits s3). iFrame. iPureIntro. bv_solve. }
  have Haddr960L : bv_unsigned sp + 952 + 8 = bv_unsigned sp + 960 by lia.
  have Haddr960R : bv_unsigned sp + (952 + 8) = bv_unsigned sp + 960 by lia.
  have Haddr976L : bv_unsigned sp + 968 + 8 = bv_unsigned sp + 976 by lia.
  have Haddr976R : bv_unsigned sp + (968 + 8) = bv_unsigned sp + 976 by lia.
  iEval (rewrite Haddr960R) in "HframeSize".
  iEval (rewrite Haddr976L) in "Hs4".
  iEval (rewrite Haddr960L Haddr976R).
  iFrame.
Qed.

Lemma write_success_suffix_bytes_rotate_15920
    `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma)
    (sp d1 s1 d2 s2 d3 s3 d4 s4 d5 s5 oldS0 oldS1 : bv 64)
    (b1 b2 b3 b4 b5 : list (bv 8)) (tail : spec) :
  writeSuccessSuffixBytesAt15920CarrierExactData sp d4 s4 oldS0 oldS1 b4
      (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
        (writeOutputEvents d5 s5 tail))
      (writeSuccessSuffixBytesP4 sp d1 s1 d2 s2 d3 s3 d4 s4 d5 s5
        b1 b2 b3 b4 b5 P) -∗
  writeSuccessSuffixBytesAt15930CarrierShape sp
      (writeSuccessSuffixBytesP5 sp d1 s1 d2 s2 d3 s3 d4 s4 d5 s5
        b1 b2 b3 b4 b5 P).
Proof.
  iIntros "H".
  iEval (rewrite /writeSuccessSuffixBytesAt15920CarrierExactData
    /writeSuccessSuffixBytesCarrierExactState) in "H".
  iEval (rewrite /writeSuccessSuffixBytesP4 /writeSuccessSuffixBytesDescriptor) in "H".
  iEval (rewrite /writeSuccessSuffixBytesAt15930CarrierShape /writeSuccessSuffixBytesCarrierState).
  iEval (rewrite /writeSuccessSuffixBytesP5 /writeSuccessSuffixBytesDescriptor).
  iExists d5, s5, oldS0, oldS1, b5, tail.
  iDestruct "H" as
    "(Hsys & H1 & H2 & H5 & H6 & H8 & H9 & H10 & H11 & Hstack & Hmmio &
      Htrace & Hdata & Hlen & Hspmod & Hlow & Hhigh & Hbound & Hregs & HframeData &
      HframeSize & Hdesc & _)".
  iDestruct "Hdesc" as "(Hdesc1 & Hdesc2 & Hdesc3 & Hdesc5 & HP)".
  iDestruct "Hdesc1" as "(Hd1 & Hs1 & Hb1 & Hl1)".
  iDestruct "Hdesc2" as "(Hd2 & Hs2 & Hb2 & Hl2)".
  iDestruct "Hdesc3" as "(Hd3 & Hs3 & Hb3 & Hl3)".
  iDestruct "Hdesc5" as "(Hd5 & Hs5 & Hb5 & Hl5)".
  iAssert (("x1" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝))%I)
    with "[H1]" as "H1shape".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists (RVal_Bits (BV 64 0x15920)). iFrame. iPureIntro. bv_solve. }
  iAssert (("x5" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝))%I)
    with "[H5]" as "H5shape".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists (RVal_Bits (BV 64 0x2401a0b8)). iFrame. iPureIntro. bv_solve. }
  iAssert (("x10" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝))%I)
    with "[H10]" as "H10shape".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists (RVal_Bits d4). iFrame. iPureIntro. bv_solve. }
  iAssert (("x11" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝))%I)
    with "[H11]" as "H11shape".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists (RVal_Bits s4). iFrame. iPureIntro. bv_solve. }
  have Haddr976L : bv_unsigned sp + 968 + 8 = bv_unsigned sp + 976 by lia.
  have Haddr976R : bv_unsigned sp + (968 + 8) = bv_unsigned sp + 976 by lia.
  have Haddr992L : bv_unsigned sp + 984 + 8 = bv_unsigned sp + 992 by lia.
  have Haddr992R : bv_unsigned sp + (984 + 8) = bv_unsigned sp + 992 by lia.
  iEval (rewrite Haddr976R) in "HframeSize".
  iEval (rewrite Haddr992L) in "Hs5".
  iEval (rewrite Haddr976L Haddr992R).
  iFrame.
Qed.

Lemma write_success_native_suffix_bytes_158e0_to_15930
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15c6c zesuEncoderBytesCallSpec -∗
  instr_body 0x15930 (writeSuccessSuffixBytesAggregateExit P) -∗
  instr_body 0x158e0 (writeSuccessSuffixBytesAggregateEntry P).
Proof.
  iStartProof.
  iIntros "#Hlookup #Hcode #Hbytes Hnext".
  rewrite instr_pre'_eq. iIntros "Hentry".
  iEval (rewrite -instr_pre'_eq) in "Hnext Hbytes".
  iEval (rewrite /writeSuccessSuffixBytesAggregateEntry) in "Hentry".
  iDestruct "Hentry" as
    "(%sp & %d1 & %s1 & %d2 & %s2 & %d3 & %s3 & %d4 & %s4 & %d5 & %s5 &
      %oldS0 & %oldS1 & %b1 & %b2 & %b3 & %b4 & %b5 & %tail & Hentry)".
  set P1 := writeSuccessSuffixBytesP1 sp d1 s1 d2 s2 d3 s3 d4 s4 d5 s5
    b1 b2 b3 b4 b5 P.
  set P2 := writeSuccessSuffixBytesP2 sp d1 s1 d2 s2 d3 s3 d4 s4 d5 s5
    b1 b2 b3 b4 b5 P.
  set P3 := writeSuccessSuffixBytesP3 sp d1 s1 d2 s2 d3 s3 d4 s4 d5 s5
    b1 b2 b3 b4 b5 P.
  set P4 := writeSuccessSuffixBytesP4 sp d1 s1 d2 s2 d3 s3 d4 s4 d5 s5
    b1 b2 b3 b4 b5 P.
  set P5 := writeSuccessSuffixBytesP5 sp d1 s1 d2 s2 d3 s3 d4 s4 d5 s5
    b1 b2 b3 b4 b5 P.
  iPoseProof (instr_pre_wand 0x15930 0x15930 false false
    (writeSuccessSuffixBytesAggregateExit P)
    (writeSuccessSuffixBytesAt15930Carrier sp P5)
    with "Hnext") as "Hnext5"; [done | done |].
  iSpecialize ("Hnext5" with "[]").
  { iApply (write_success_suffix_bytes_exit_adapter P sp d1 s1 d2 s2 d3 s3
      d4 s4 d5 s5 oldS0 oldS1 b1 b2 b3 b4 b5 tail). }
  iPoseProof (write_success_suffix_bytes_15920_carrier sp P5
    with "Hlookup Hcode Hbytes Hnext5") as "Hbody5".
  iPoseProof (instr_pre_wand 0x15920 0x15920 false false
    (writeSuccessSuffixBytesAt15930CarrierShape sp P5)
    (writeSuccessSuffixBytesAt15920CarrierExactData sp d4 s4 oldS0 oldS1 b4
      (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
        (writeOutputEvents d5 s5 tail)) P4)
    with "Hbody5") as "Hbody5to4"; [done | done |].
  iSpecialize ("Hbody5to4" with "[]").
  { iApply (write_success_suffix_bytes_rotate_15920 P sp d1 s1 d2 s2 d3 s3
      d4 s4 d5 s5 oldS0 oldS1 b1 b2 b3 b4 b5 tail). }
  iPoseProof (write_success_suffix_bytes_15910_carrier sp P4
    d4 s4 oldS0 oldS1 b4
    (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
      (writeOutputEvents d5 s5 tail))
    with "Hlookup Hcode Hbytes Hbody5to4") as "Hbody4".
  iPoseProof (instr_pre_wand 0x15910 0x15910 false false
    (writeSuccessSuffixBytesAt15920CarrierData sp d4 s4 oldS0 oldS1 b4
      (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
        (writeOutputEvents d4 s4
          (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
            (writeOutputEvents d5 s5 tail)))) P4)
    (writeSuccessSuffixBytesAt15910CarrierExactData sp d3 s3 oldS0 oldS1 b3
      (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
        (writeOutputEvents d4 s4
          (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
            (writeOutputEvents d5 s5 tail)))) P3)
    with "Hbody4") as "Hbody4to3"; [done | done |].
  iSpecialize ("Hbody4to3" with "[]").
  { iApply (write_success_suffix_bytes_rotate_15910 P sp d1 s1 d2 s2 d3 s3
      d4 s4 d5 s5 oldS0 oldS1 b1 b2 b3 b4 b5 tail). }
  iPoseProof (write_success_suffix_bytes_15900_carrier sp P3
    d3 s3 oldS0 oldS1 b3
    (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
      (writeOutputEvents d4 s4
        (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
          (writeOutputEvents d5 s5 tail))))
    with "Hlookup Hcode Hbytes Hbody4to3") as "Hbody3".
  iPoseProof (instr_pre_wand 0x15900 0x15900 false false
    (writeSuccessSuffixBytesAt15910CarrierData sp d3 s3 oldS0 oldS1 b3
      (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
        (writeOutputEvents d3 s3
          (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
            (writeOutputEvents d4 s4
              (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
                (writeOutputEvents d5 s5 tail)))))) P3)
    (writeSuccessSuffixBytesAt15900CarrierExactData sp d2 s2 oldS0 oldS1 b2
      (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
        (writeOutputEvents d3 s3
          (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
            (writeOutputEvents d4 s4
              (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
                (writeOutputEvents d5 s5 tail)))))) P2)
    with "Hbody3") as "Hbody3to2"; [done | done |].
  iSpecialize ("Hbody3to2" with "[]").
  { iApply (write_success_suffix_bytes_rotate_15900 P sp d1 s1 d2 s2 d3 s3
      d4 s4 d5 s5 oldS0 oldS1 b1 b2 b3 b4 b5 tail). }
  iPoseProof (write_success_suffix_bytes_158f0_carrier sp P2
    d2 s2 oldS0 oldS1 b2
    (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
      (writeOutputEvents d3 s3
        (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
          (writeOutputEvents d4 s4
            (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
              (writeOutputEvents d5 s5 tail))))))
    with "Hlookup Hcode Hbytes Hbody3to2") as "Hbody2".
  iPoseProof (instr_pre_wand 0x158f0 0x158f0 false false
    (writeSuccessSuffixBytesAt15900CarrierData sp d2 s2 oldS0 oldS1 b2
      (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
        (writeOutputEvents d2 s2
          (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
            (writeOutputEvents d3 s3
              (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
                (writeOutputEvents d4 s4
                  (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
                    (writeOutputEvents d5 s5 tail)))))))) P2)
    (writeSuccessSuffixBytesAt158f0CarrierExactData sp d1 s1 oldS0 oldS1 b1
      (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
        (writeOutputEvents d2 s2
          (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
            (writeOutputEvents d3 s3
              (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
                (writeOutputEvents d4 s4
                  (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
                    (writeOutputEvents d5 s5 tail)))))))) P1)
    with "Hbody2") as "Hbody2to1"; [done | done |].
  iSpecialize ("Hbody2to1" with "[]").
  { iApply (write_success_suffix_bytes_rotate_158f0 P sp d1 s1 d2 s2 d3 s3
      d4 s4 d5 s5 oldS0 oldS1 b1 b2 b3 b4 b5 tail). }
  iPoseProof (write_success_suffix_bytes_158e0_carrier sp P1
    d1 s1 oldS0 oldS1 b1
    (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
      (writeOutputEvents d2 s2
        (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
          (writeOutputEvents d3 s3
            (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
              (writeOutputEvents d4 s4
                (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
                  (writeOutputEvents d5 s5 tail))))))))
    with "Hlookup Hcode Hbytes Hbody2to1") as "Hbody1".
  iEval (rewrite instr_pre'_eq) in "Hbody1".
  iApply ("Hbody1" with "[Hentry]").
  iEval (rewrite /writeSuccessSuffixBytesAt158e0CarrierData).
  unfold P1.
  iEval (rewrite /writeSuccessSuffixBytesP1 /writeSuccessSuffixBytesDescriptor
    /writeSuccessSuffixBytesCarrierOtherRegisters).
  iEval (rewrite /writeSuccessSuffixBytesCarrierOtherRegisters) in "Hentry".
  have Haddr944 : bv_unsigned sp + 936 + 8 = bv_unsigned sp + 944 by lia.
  have Haddr960 : bv_unsigned sp + 952 + 8 = bv_unsigned sp + 960 by lia.
  have Haddr976 : bv_unsigned sp + 968 + 8 = bv_unsigned sp + 976 by lia.
  have Haddr992 : bv_unsigned sp + 984 + 8 = bv_unsigned sp + 992 by lia.
  iEval (rewrite Haddr944 Haddr960 Haddr976 Haddr992).
  iDestruct "Hentry" as
    "(Hsys & H1 & H2 & H5 & H6 & H8 & H9 & H10 & H11 & Hstack & Hmmio &
      Htrace & Hdata1 & Hlen1 & Hdata2 & Hlen2 & Hdata3 & Hlen3 & Hdata4 &
      Hlen4 & Hdata5 & Hlen5 & Hspmod & Hlow & Hhigh & Hbound & Hregs &
      HframeData1 & HframeSize1 & HframeData2 & HframeSize2 & HframeData3 &
      HframeSize3 & HframeData4 & HframeSize4 & HframeData5 & HframeSize5 &
      HP & _)".
  iFrame.
Qed.
