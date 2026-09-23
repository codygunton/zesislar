Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_07 Require Import instrs.
From IslaTraces.write_success_01 Require Import instrs.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCallAbi.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutput.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputSemantic.

Definition zesuEncoderIntPayloadCallSpec `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (∃ (value sp : bv 64) (ret : Z) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits (Z_to_bv 64 ret) ∗ "x2" ↦ᵣ RVal_Bits sp ∗
    "x5" ↦ᵣ: fun r5 => ⌜valu_has_shape r5 (BitsShape 64)⌝ ∗
    "x10" ↦ᵣ RVal_Bits value ∗
    "x11" ↦ᵣ: fun r11 => ⌜valu_has_shape r11 (BitsShape 64)⌝ ∗
    (bv_unsigned sp - 16) ↦ₘ? 16 ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗
    spec_trace (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
      (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned value))) tail) ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 16⌝ ∗ ⌜bv_unsigned sp < (machineRamEnd defaultMap)⌝ ∗
    ⌜0 <= ret < 2 ^ 64⌝ ∗
    ⌜bv_extract 0 1 (Z_to_bv 64 ret) = BV 1 0⌝ ∗
    ⌜bv_extract 1 1 (Z_to_bv 64 ret) = BV 1 0⌝ ∗
    ⌜bv_extract 0 2 (Z_to_bv 64 ret) = BV 2 0⌝ ∗
    instr_pre ret
      (reg_col zesu_ram_sys_regs ∗
       "x1" ↦ᵣ RVal_Bits (Z_to_bv 64 ret) ∗ "x2" ↦ᵣ RVal_Bits sp ∗
       "x5" ↦ᵣ RVal_Bits (BV 64 (mapIoContextAddress defaultMap)) ∗
       "x10" ↦ᵣ RVal_Bits (sp - BV 64 16)%bv ∗
       "x11" ↦ᵣ RVal_Bits (BV 64 8) ∗
       (bv_unsigned sp - 16) ↦ₘ? 16 ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗
       spec_trace tail ∗ True) ∗ True)%I.

Global Instance : LithiumUnfold (@zesuEncoderIntPayloadCallSpec) := I.

#[local] Hint Rewrite (@bv_sign_extend_idemp 64) :
  lithium_rewrite isla_coq_rewrite.

Definition zesuEncoderIntPayloadFrameSpec `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (ret : Z) (tail : spec) : iProp Sigma :=
  ("x2" ↦ᵣ RVal_Bits (sp - BV 64 16)%bv ∗
   bv_unsigned (sp - BV 64 8)%bv ↦ₘ Z_to_bv 64 ret ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 16⌝ ∗
   ⌜bv_unsigned sp < (machineRamEnd defaultMap)⌝ ∗ ⌜0 <= ret < 2 ^ 64⌝ ∗
   ⌜bv_extract 0 1 (Z_to_bv 64 ret) = BV 1 0⌝ ∗
   ⌜bv_extract 1 1 (Z_to_bv 64 ret) = BV 1 0⌝ ∗
   ⌜bv_extract 0 2 (Z_to_bv 64 ret) = BV 2 0⌝ ∗
   instr_pre ret
     (reg_col zesu_ram_sys_regs ∗
      "x1" ↦ᵣ RVal_Bits (Z_to_bv 64 ret) ∗ "x2" ↦ᵣ RVal_Bits sp ∗
      "x5" ↦ᵣ RVal_Bits (BV 64 (mapIoContextAddress defaultMap)) ∗
      "x10" ↦ᵣ RVal_Bits (sp - BV 64 16)%bv ∗
      "x11" ↦ᵣ RVal_Bits (BV 64 8) ∗
      (bv_unsigned sp - 16) ↦ₘ? 16 ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗
      spec_trace tail ∗ True) ∗ True)%I.

Global Instance : LithiumUnfold (@zesuEncoderIntPayloadFrameSpec) := I.

Definition zesuEncoderIntPayloadSuffixSpec `{!islaG Sigma} `{!threadG}
    (value sp : bv 64) (ret : Z) (tail : spec) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits (BV 64 0x15d2c) ∗
   "x5" ↦ᵣ RVal_Bits (BV 64 (mapIoContextAddress defaultMap)) ∗
   "x10" ↦ᵣ RVal_Bits (sp - BV 64 16)%bv ∗
   "x11" ↦ᵣ RVal_Bits (BV 64 8) ∗
   bv_unsigned (sp - BV 64 16)%bv ↦ₘ∗
     writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned value)) ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗ spec_trace tail ∗
   zesuEncoderIntPayloadFrameSpec sp ret tail ∗ True)%I.

Global Instance : LithiumUnfold (@zesuEncoderIntPayloadSuffixSpec) := I.

Lemma zesu_encoder_int_payload_suffix_correct `{!islaG Sigma} `{!threadG}
    (value sp : bv 64) (ret : Z) (tail : spec) :
  ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15d2c (zesuEncoderIntPayloadSuffixSpec value sp ret tail).
Proof. move => *. zesu_block. Qed.

Print Assumptions zesu_encoder_int_payload_suffix_correct.

Lemma zesu_encoder_int_payload_call_correct `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15d10 zesuEncoderIntPayloadCallSpec.
Proof.
  move => * /=. iStartProof.
  iIntros "_ #HencoderCode #HoutputCode".
  iEval (simpl) in "HencoderCode".
  iDestruct "HencoderCode" as
    "(#Hi0 & #Hi1 & #Hi2 & #Hi3 & #Hi4 & #Hi5 & #Hi6 & #Hi7 & #Hi8 & #Hi9 & _)".
  liARun.
  Unshelve. all: prepare_sidecond; try assumption; try rewrite bv_sign_extend_idemp;
    try bv_solve; try lia.
  all: try (change (bv_extract 0 2 (Z_to_bv 64 ret) = BV 2 0); assumption).
  all: lazymatch goal with |- ?G => fail "side condition" G end.
  Unshelve.
  zesu_unfold_bv_bindings.
  iRename select (_ ↦ₘ value)%I into "Hword".
  zesu_normalize_memory_cell "Hword" (bv_unsigned (sp - BV 64 16)%bv).
  iDestruct (mem_mapsto_mapsto_to_byte_array with "Hword") as "Hpayload".
  set (payload := writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned value))).
  set (P := zesuEncoderIntPayloadFrameSpec sp ret tail).
  iAssert (instr_pre 0x15d2c (zesuEncoderIntPayloadSuffixSpec value sp ret tail))%I as "Hsuffix".
  { iApply instr_pre_to_body. iNext.
    iApply zesu_encoder_int_payload_suffix_correct. simpl.
    iFrame "Hi0 Hi1 Hi2 Hi3 Hi4 Hi5 Hi6 Hi7 Hi8 Hi9". }
  iAssert (□ instr_pre 0x10190 (writeOutputTraceSpec (sp - BV 64 16)%bv
    (BV 64 8) (BV 64 0x15d2c) payload tail P))%I as "#Houtput".
  { iModIntro. iApply instr_pre_to_body. iNext.
    iApply write_output_trace_correct. iExact "HoutputCode". }
  liARun.
  Unshelve. all: prepare_sidecond; try assumption; try bv_solve; try lia.
  all: try (eexists; eexists; split; [reflexivity | split; reflexivity]).
  all: try (rewrite /Z_to_little_endian /=;
    eexists; eexists; split; [reflexivity | split; reflexivity]).
  all: try (rewrite /zesuEncoderIntPayloadSuffixSpec /P /payload; reflexivity).
  all: try (replace
    (bv_unsigned (sp + BV 64 18446744073709551600)%bv)
    with (bv_unsigned (sp - BV 64 16)%bv) by bv_solve; reflexivity).
  rewrite /Z_to_little_endian /=.
  rewrite !Z.land_ones; [|lia..].
  rewrite !Z.shiftr_div_pow2; [|lia..].
  vm_compute.
  eexists. eexists. repeat split; reflexivity.
Qed.

Print Assumptions zesu_encoder_int_payload_call_correct.

Lemma zesu_encoder_int_payload_call_pre `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15d10 zesuEncoderIntPayloadCallSpec.
Proof.
  iStartProof. iIntros "#HencoderCode #HoutputCode". iModIntro.
  iApply instr_pre_to_body. iNext.
  iApply zesu_encoder_int_payload_call_correct; iAssumption.
Qed.

Print Assumptions zesu_encoder_int_payload_call_pre.

Definition encoderIntExactReturn `{!islaG Sigma} `{!threadG}
    (sp ret : bv 64) (tail : spec) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x1" ↦ᵣ RVal_Bits ret ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   "x5" ↦ᵣ RVal_Bits (BV 64 (mapIoContextAddress defaultMap)) ∗
   "x10" ↦ᵣ RVal_Bits (sp - BV 64 16)%bv ∗
   "x11" ↦ᵣ RVal_Bits (BV 64 8) ∗
   (bv_unsigned sp - 16) ↦ₘ? 16 ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace tail ∗ True)%I.

Global Instance : LithiumUnfold (@encoderIntExactReturn) := I.

Definition zesuEncoderIntExactCallSpec `{!islaG Sigma} `{!threadG}
    : iProp Sigma :=
  (∃ (value sp ret : bv 64) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits ret ∗ "x2" ↦ᵣ RVal_Bits sp ∗
    "x10" ↦ᵣ RVal_Bits value ∗
    "x5" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
    "x11" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
    (bv_unsigned sp - 16) ↦ₘ? 16 ∗
    mmio_range (machineOutputAddress defaultMap) 16 ∗
    spec_trace (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
      (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned value))) tail) ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜mapRamBase defaultMap <= bv_unsigned sp - 16⌝ ∗
    ⌜bv_unsigned sp < machineRamEnd defaultMap⌝ ∗
    ⌜bv_extract 0 1 ret = BV 1 0⌝ ∗
    ⌜bv_extract 1 1 ret = BV 1 0⌝ ∗
    ⌜bv_extract 0 2 ret = BV 2 0⌝ ∗
    instr_pre (bv_unsigned ret) (encoderIntExactReturn sp ret tail) ∗ True)%I.

Global Instance : LithiumUnfold (@zesuEncoderIntExactCallSpec) := I.

Lemma encoder_int_exact_entry_to_payload `{!islaG Sigma} `{!threadG} :
  zesuEncoderIntExactCallSpec -∗ zesuEncoderIntPayloadCallSpec.
Proof.
  iStartProof. iIntros "Hexact".
  iEval (unfold zesuEncoderIntExactCallSpec) in "Hexact".
  iDestruct "Hexact" as (value sp ret tail)
    "(Hsys & H1 & H2 & H10 & H5 & H11 & Hstack & Hmmio & Htrace &
      %Halign & %Hlower & %Hupper & %Hret0 & %Hret1 & %Hret2 & Hreturn & _)".
  iEval (unfold zesuEncoderIntPayloadCallSpec).
  iExists value, sp, (bv_unsigned ret), tail.
  all: try (rewrite Z_to_bv_bv_unsigned).
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "H5".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "H11".
  iDestruct "H5" as (r5) "[Hx5 %Hshape5]".
  iDestruct "H11" as (r11) "[Hx11 %Hshape11]".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def).
  zesu_run.
Qed.

Print Assumptions encoder_int_exact_entry_to_payload.

Lemma encoder_int_exact_body_from_payload `{!islaG Sigma} `{!threadG} :
  instr_body 0x15d10 zesuEncoderIntPayloadCallSpec -∗
  instr_body 0x15d10 zesuEncoderIntExactCallSpec.
Proof.
  iStartProof. iIntros "Hpayload".
  iApply (instr_pre_wand 0x15d10 0x15d10 false false with "Hpayload");
    [done | done |].
  iIntros "Hexact".
  iApply (encoder_int_exact_entry_to_payload with "Hexact").
Qed.

Print Assumptions encoder_int_exact_body_from_payload.

Lemma zesu_encoder_int_exact_call_correct `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15d10 zesuEncoderIntExactCallSpec.
Proof.
  iStartProof. iIntros "HencoderCode HoutputCode".
  iApply encoder_int_exact_body_from_payload.
  iApply (zesu_encoder_int_payload_call_correct with "HencoderCode HoutputCode").
Qed.

Print Assumptions zesu_encoder_int_exact_call_correct.

Lemma zesu_encoder_int_exact_call_pre `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15d10 zesuEncoderIntExactCallSpec.
Proof.
  iStartProof. iIntros "#HencoderCode #HoutputCode". iModIntro.
  iApply instr_pre_to_body. iNext.
  iApply zesu_encoder_int_exact_call_correct; iAssumption.
Qed.

Print Assumptions zesu_encoder_int_exact_call_pre.
