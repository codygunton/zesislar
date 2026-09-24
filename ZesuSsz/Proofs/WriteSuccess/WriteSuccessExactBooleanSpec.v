Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputSemantic.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactBooleanSuffix.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactBooleanPrefix.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactBooleanOutput.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutput.
From IslaTraces.write_success_03 Require Import instrs.
From IslaTraces.write_success_01 Require Import instrs.

Definition writeSuccessBooleanWordPayload (value : bv 64) : list (bv 8) :=
  [bv_extract 0 8 (bv_and value (BV 64 1))].

Lemma writeSuccessBooleanWordPayload_encoder (present : bool) :
  writeSuccessBooleanWordPayload (if present then BV 64 1 else BV 64 0) =
  writeSuccessPrivateBytes (writeSuccessEncodeU8 (if present then 1 else 0)).
Proof. destruct present; reflexivity. Qed.

Definition encoderBooleanExactReturnedFrame `{!islaG Sigma} `{!threadG}
    (value sp : bv 64) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  ("x5" ↦ᵣ RVal_Bits (BV 64 (mapIoContextAddress defaultMap)) ∗
   "x10" ↦ᵣ RVal_Bits (sp - BV 64 9)%bv ∗ "x11" ↦ᵣ RVal_Bits (BV 64 1) ∗
   bv_unsigned (sp - BV 64 9)%bv ↦ₘ∗ writeSuccessBooleanWordPayload value ∗
   (bv_unsigned sp - 16) ↦ₘ? 7 ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace tail ∗ P ∗ True)%I.

Definition encoderBooleanExactPost `{!islaG Sigma} `{!threadG}
    (value sp ret : bv 64) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits ret ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   (bv_unsigned sp - 8) ↦ₘ ret ∗
   encoderBooleanExactReturnedFrame value sp tail P ∗ True)%I.

Definition encoderBooleanExactFacts `{!islaG Sigma} `{!threadG}
    (value sp ret : bv 64) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (⌜bv_extract 0 3 sp = BV 3 0⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 16⌝ ∗ ⌜bv_unsigned sp < (machineRamEnd defaultMap)⌝ ∗
   ⌜bv_extract 0 1 ret = BV 1 0⌝ ∗ ⌜bv_extract 1 1 ret = BV 1 0⌝ ∗
   ⌜bv_extract 0 2 ret = BV 2 0⌝ ∗ P ∗
   instr_pre (bv_unsigned ret) (encoderBooleanExactPost value sp ret tail P) ∗ True)%I.

Definition encoderBooleanExactPrefixFrame `{!islaG Sigma} `{!threadG}
    (value sp ret old_x5 old_x11 : bv 64) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  ("x5" ↦ᵣ RVal_Bits old_x5 ∗ "x11" ↦ᵣ RVal_Bits old_x11 ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace (writeOutputEvents (sp - BV 64 9)%bv (BV 64 1)
     (writeSuccessBooleanWordPayload value) tail) ∗
   encoderBooleanExactFacts value sp ret tail P ∗ True)%I.

Definition encoderBooleanExactSpec `{!islaG Sigma} `{!threadG}
    (value sp ret old_x5 old_x11 : bv 64) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits ret ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x10" ↦ᵣ RVal_Bits value ∗ (bv_unsigned sp - 16) ↦ₘ? 16 ∗
   ⌜bv_extract 0 4 sp = BV 4 0⌝ ∗ ⌜bv_extract 0 3 sp = BV 3 0⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 16⌝ ∗ ⌜bv_unsigned sp < (machineRamEnd defaultMap)⌝ ∗
   encoderBooleanExactPrefixFrame value sp ret old_x5 old_x11 tail P ∗ True)%I.

Definition encoderBooleanExactWordsSpec `{!islaG Sigma} `{!threadG}
    (value sp ret old_x5 old_x11 : bv 64) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits ret ∗ "x2" ↦ᵣ RVal_Bits (sp - BV 64 16)%bv ∗
   "x10" ↦ᵣ RVal_Bits (bv_and value (BV 64 1)) ∗
   (bv_unsigned sp - 16) ↦ₘ? 7 ∗
   (bv_unsigned sp - 9) ↦ₘ (bv_extract 0 8 (bv_and value (BV 64 1))) ∗
   (bv_unsigned sp - 8) ↦ₘ ret ∗
   encoderBooleanExactPrefixFrame value sp ret old_x5 old_x11 tail P ∗ True)%I.

Definition encoderBooleanExactOutputFrame `{!islaG Sigma} `{!threadG}
    (value sp ret : bv 64) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  ((bv_unsigned sp - 16) ↦ₘ? 7 ∗ (bv_unsigned sp - 8) ↦ₘ ret ∗
   encoderBooleanExactFacts value sp ret tail P ∗ True)%I.

Definition encoderBooleanExactAtOutputSpec `{!islaG Sigma} `{!threadG}
    (value sp ret old_x5 old_x11 : bv 64) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x1" ↦ᵣ RVal_Bits ret ∗
   "x5" ↦ᵣ RVal_Bits old_x5 ∗ "x10" ↦ᵣ RVal_Bits (bv_and value (BV 64 1)) ∗
   "x11" ↦ᵣ RVal_Bits old_x11 ∗
   bv_unsigned (sp - BV 64 9)%bv ↦ₘ∗ writeSuccessBooleanWordPayload value ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace (writeOutputEvents (sp - BV 64 9)%bv (BV 64 1)
     (writeSuccessBooleanWordPayload value) tail) ∗
   ("x2" ↦ᵣ RVal_Bits (sp - BV 64 16)%bv ∗
    encoderBooleanExactOutputFrame value sp ret tail P ∗ True) ∗ True)%I.

Definition encoderBooleanExactSuffixSpec `{!islaG Sigma} `{!threadG}
    (value sp ret : bv 64) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x1" ↦ᵣ RVal_Bits (BV 64 0x15bbc) ∗
   "x5" ↦ᵣ RVal_Bits (BV 64 (mapIoContextAddress defaultMap)) ∗
   "x10" ↦ᵣ RVal_Bits (sp - BV 64 9)%bv ∗ "x11" ↦ᵣ RVal_Bits (BV 64 1) ∗
   bv_unsigned (sp - BV 64 9)%bv ↦ₘ∗ writeSuccessBooleanWordPayload value ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗ spec_trace tail ∗
   ("x2" ↦ᵣ RVal_Bits (sp - BV 64 16)%bv ∗
    encoderBooleanExactOutputFrame value sp ret tail P ∗ True) ∗ True)%I.

Global Instance : LithiumUnfold (@encoderBooleanExactReturnedFrame) := I.
Global Instance : LithiumUnfold (@encoderBooleanExactPost) := I.
Global Instance : LithiumUnfold (@encoderBooleanExactFacts) := I.
Global Instance : LithiumUnfold (@encoderBooleanExactPrefixFrame) := I.
Global Instance : LithiumUnfold (@encoderBooleanExactSpec) := I.
Global Instance : LithiumUnfold (@encoderBooleanExactWordsSpec) := I.
Global Instance : LithiumUnfold (@encoderBooleanExactOutputFrame) := I.
Global Instance : LithiumUnfold (@encoderBooleanExactAtOutputSpec) := I.
Global Instance : LithiumUnfold (@encoderBooleanExactSuffixSpec) := I.

Print Assumptions writeSuccessBooleanWordPayload_encoder.

Lemma encoder_boolean_exact_words_to_payload `{!islaG Sigma} `{!threadG}
    value sp ret old_x5 old_x11 tail (P : iProp Sigma) :
  encoderBooleanExactWordsSpec value sp ret old_x5 old_x11 tail P -∗
  encoderBooleanExactAtOutputSpec value sp ret old_x5 old_x11 tail P.
Proof.
  iIntros "Hwords". iDestruct "Hwords" as
    "(Hsys & H1 & H2 & H10 & Hlow & Hbyte & Hra & Hframe & _)".
  iDestruct "Hframe" as "(H5 & H11 & Hmmio & Htrace & Hfacts & _)".
  iDestruct "Hfacts" as
    "(%Halign & %Hmin & %Hmax & %Hret0 & %Hret1 & %Hret2 & HP & Hnext & _)".
  have Haddress : bv_unsigned (sp - BV 64 9)%bv = bv_unsigned sp - 9 by bv_solve.
  iEval (rewrite -Haddress -mem_mapsto_array_singleton) in "Hbyte".
  rewrite /encoderBooleanExactAtOutputSpec /encoderBooleanExactOutputFrame
    /encoderBooleanExactFacts /writeSuccessBooleanWordPayload.
  iFrame. repeat iSplit; try done.
Qed.

Print Assumptions encoder_boolean_exact_words_to_payload.

Lemma encoder_boolean_exact_suffix_spec_correct `{!islaG Sigma} `{!threadG}
    (value sp ret : bv 64) (tail : spec) (P : iProp Sigma) :
  ([∗ list] instruction ∈ drop 8 IslaTraces.write_success_03.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15bbc (encoderBooleanExactSuffixSpec value sp ret tail P).
Proof. move => *. zesu_block. Qed.

Print Assumptions encoder_boolean_exact_suffix_spec_correct.

Lemma encoder_boolean_exact_framed_correct `{!islaG Sigma} `{!threadG}
    (value sp ret old_x5 old_x11 : bv 64) (tail : spec) (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_03.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15b9c (encoderBooleanExactSpec value sp ret old_x5 old_x11 tail P).
Proof.
  iStartProof. iIntros "#Hcode #HoutputCode".
  iEval (simpl) in "Hcode".
  iDestruct "Hcode" as
    "(#Hi0 & #Hi1 & #Hi2 & #Hi3 & #Hi4 & #Hi5 & #Hi6 & #Hi7 & #Hi8 & #Hi9 & #Hi10 & _)".
  iAssert (instr_body 0x15bbc
    (encoderBooleanExactSuffixSpec value sp ret tail P))%I as "Hsuffix".
  { iApply encoder_boolean_exact_suffix_spec_correct.
    simpl. iFrame "Hi8 Hi9 Hi10". }
  iAssert (□ instr_pre 0x10190 (writeOutputTraceSpec (sp - BV 64 9)%bv
    (BV 64 1) (BV 64 0x15bbc) (writeSuccessBooleanWordPayload value) tail
    ("x2" ↦ᵣ RVal_Bits (sp - BV 64 16)%bv ∗
     encoderBooleanExactOutputFrame value sp ret tail P ∗ True)))%I as "#Houtput".
  { iModIntro. iApply instr_pre_to_body. iNext.
    iApply write_output_trace_correct. iExact "HoutputCode". }
  iPoseProof (encoder_boolean_exact_output value sp ret old_x5 old_x11 tail
    (encoderBooleanExactOutputFrame value sp ret tail P)
    with "[ ] Houtput Hsuffix") as "Hcall".
  { simpl. iFrame "Hi4 Hi5 Hi6 Hi7". }
  iApply (encoder_boolean_exact_prefix value sp ret
    (encoderBooleanExactPrefixFrame value sp ret old_x5 old_x11 tail P)
    with "[ ]").
  { simpl. iFrame "Hi0 Hi1 Hi2 Hi3". }
  iApply (instr_pre_wand 0x15bac 0x15bac false false with "Hcall"); [done | done |].
  iApply encoder_boolean_exact_words_to_payload.
Qed.

Print Assumptions encoder_boolean_exact_framed_correct.

Definition zesuEncoderBooleanExactPayloadCallSpec `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) : iProp Sigma :=
  (∃ (present : bool) (sp ret : bv 64) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits ret ∗ "x2" ↦ᵣ RVal_Bits sp ∗
    ("x5" ↦ᵣ: fun r5 => ⌜valu_has_shape r5 (BitsShape 64)⌝) ∗
    "x10" ↦ᵣ RVal_Bits (if present then BV 64 1 else BV 64 0) ∗
    ("x11" ↦ᵣ: fun r11 => ⌜valu_has_shape r11 (BitsShape 64)⌝) ∗
    (bv_unsigned sp - 16) ↦ₘ? 16 ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗
    spec_trace (writeOutputEvents (sp - BV 64 9)%bv (BV 64 1)
      (writeSuccessPrivateBytes (writeSuccessEncodeU8 (if present then 1 else 0))) tail) ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 16⌝ ∗ ⌜bv_unsigned sp < (machineRamEnd defaultMap)⌝ ∗
    ⌜bv_extract 0 1 ret = BV 1 0⌝ ∗ ⌜bv_extract 1 1 ret = BV 1 0⌝ ∗
    ⌜bv_extract 0 2 ret = BV 2 0⌝ ∗ P ∗
    instr_pre (bv_unsigned ret)
      (reg_col zesu_ram_sys_regs ∗
       "x1" ↦ᵣ RVal_Bits ret ∗ "x2" ↦ᵣ RVal_Bits sp ∗
       "x5" ↦ᵣ RVal_Bits (BV 64 (mapIoContextAddress defaultMap)) ∗
       "x10" ↦ᵣ RVal_Bits (sp - BV 64 9)%bv ∗ "x11" ↦ᵣ RVal_Bits (BV 64 1) ∗
       (bv_unsigned sp - 16) ↦ₘ? 16 ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗
       spec_trace tail ∗ P ∗ True) ∗ True)%I.

Global Instance : LithiumUnfold (@zesuEncoderBooleanExactPayloadCallSpec) := I.
