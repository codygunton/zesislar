From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Experiments.WriteSuccess.
Require Import ZesuSsz.Experiments.WriteSuccessCalls.

#[local] Hint Rewrite (@bv_sign_extend_idemp 64) :
  lithium_rewrite isla_coq_rewrite.

Definition zesuEncoderIntCallSpec `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (∃ (value sp : bv 64) (ret : Z) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits (Z_to_bv 64 ret) ∗ "x2" ↦ᵣ RVal_Bits sp ∗
    "x5" ↦ᵣ: fun r5 => ⌜valu_has_shape r5 (BitsShape 64)⌝ ∗
    "x10" ↦ᵣ RVal_Bits value ∗
    "x11" ↦ᵣ: fun r11 => ⌜valu_has_shape r11 (BitsShape 64)⌝ ∗
    (bv_unsigned sp - 16) ↦ₘ? 16 ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace
      (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8) tail) ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned sp - 16⌝ ∗
    ⌜bv_unsigned sp < 0x40000000⌝ ∗
    ⌜0 <= ret < 2 ^ 64⌝ ∗
    ⌜bv_extract 0 1 (Z_to_bv 64 ret) = BV 1 0⌝ ∗
    ⌜bv_extract 1 1 (Z_to_bv 64 ret) = BV 1 0⌝ ∗
    ⌜bv_extract 0 2 (Z_to_bv 64 ret) = BV 2 0⌝ ∗
    instr_pre ret
      (reg_col zesu_ram_sys_regs ∗
       "x1" ↦ᵣ RVal_Bits (Z_to_bv 64 ret) ∗ "x2" ↦ᵣ RVal_Bits sp ∗
       "x5" ↦ᵣ RVal_Bits (BV 64 0x2401a0b8) ∗
       "x10" ↦ᵣ RVal_Bits (sp - BV 64 16)%bv ∗
       "x11" ↦ᵣ RVal_Bits (BV 64 8) ∗
       (bv_unsigned sp - 16) ↦ₘ? 16 ∗
       mmio_range 0x2401a0c0 16 ∗ spec_trace tail ∗ True) ∗ True)%I.

Global Instance : LithiumUnfold (@zesuEncoderIntCallSpec) := I.

Lemma zesu_encoder_int_call_correct `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_20.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_14.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15d10 zesuEncoderIntCallSpec.
Proof.
  move => * /=.
  iStartProof.
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try rewrite bv_sign_extend_idemp.
  all: try bv_solve.
  all: try lia.
  all: try (change
    (bv_extract 0 2 (Z_to_bv 64 ret) = BV 2 0); assumption).
  all: lazymatch goal with |- ?G => fail "side condition" G end.
Qed.

Lemma zesu_encoder_int_call_pre `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_20.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_14.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15d10 zesuEncoderIntCallSpec.
Proof.
  iStartProof. iIntros "#HintCode #HoutputCode". iModIntro.
  iApply instr_pre_to_body. iNext.
  iApply zesu_encoder_int_call_correct; iAssumption.
Qed.

Definition zesuEncoderBytesCallSpec `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (∃ (data size sp old_s0 old_s1 : bv 64) (ret : Z)
      (bytes : list (bv 8)) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits (Z_to_bv 64 ret) ∗ "x2" ↦ᵣ RVal_Bits sp ∗
    "x5" ↦ᵣ: fun r5 => ⌜valu_has_shape r5 (BitsShape 64)⌝ ∗
    "x6" ↦ᵣ: fun r6 => ⌜valu_has_shape r6 (BitsShape 64)⌝ ∗
    "x8" ↦ᵣ RVal_Bits old_s0 ∗ "x9" ↦ᵣ RVal_Bits old_s1 ∗
    "x10" ↦ᵣ RVal_Bits data ∗ "x11" ↦ᵣ RVal_Bits size ∗
    (bv_unsigned sp - 48) ↦ₘ? 48 ∗
    bv_unsigned data ↦ₘ∗ bytes ∗
    ⌜bv_unsigned size = length bytes⌝ ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace
      (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
        (writeOutputEvents data size tail)) ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned sp - 48⌝ ∗
    ⌜bv_unsigned sp < 0x40000000⌝ ∗
    ⌜0 <= ret < 2 ^ 64⌝ ∗
    ⌜bv_extract 0 1 (Z_to_bv 64 ret) = BV 1 0⌝ ∗
    ⌜bv_extract 1 1 (Z_to_bv 64 ret) = BV 1 0⌝ ∗
    ⌜bv_extract 0 2 (Z_to_bv 64 ret) = BV 2 0⌝ ∗
    instr_pre ret
      (reg_col zesu_ram_sys_regs ∗
       "x1" ↦ᵣ RVal_Bits (Z_to_bv 64 ret) ∗ "x2" ↦ᵣ RVal_Bits sp ∗
       "x5" ↦ᵣ RVal_Bits (BV 64 0x2401a0b8) ∗
       "x6" ↦ᵣ: fun r6 => ⌜valu_has_shape r6 (BitsShape 64)⌝ ∗
       "x8" ↦ᵣ RVal_Bits old_s0 ∗ "x9" ↦ᵣ RVal_Bits old_s1 ∗
       "x10" ↦ᵣ RVal_Bits data ∗ "x11" ↦ᵣ RVal_Bits size ∗
       (bv_unsigned sp - 48) ↦ₘ? 48 ∗
       bv_unsigned data ↦ₘ∗ bytes ∗
       mmio_range 0x2401a0c0 16 ∗ spec_trace tail ∗ True) ∗ True)%I.

Global Instance : LithiumUnfold (@zesuEncoderBytesCallSpec) := I.

Lemma zesu_encoder_bytes_call_correct `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_19.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_20.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_14.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15c6c zesuEncoderBytesCallSpec.
Proof.
  move => * /=.
  iStartProof.
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try (bv_simplify_arith select (bv_extract 0 3 sp = _)).
  all: try rewrite bv_sign_extend_idemp.
  all: try bv_solve.
  all: try lia.
  all: try (change
    (bv_extract 0 2 (Z_to_bv 64 ret) = BV 2 0); assumption).
  all: lazymatch goal with |- ?G => fail "side condition" G end.
Qed.

Lemma zesu_encoder_bytes_call_pre `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_19.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_20.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_14.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15c6c zesuEncoderBytesCallSpec.
Proof.
  iStartProof. iIntros "#HbytesCode #HintCode #HoutputCode". iModIntro.
  iApply instr_pre_to_body. iNext.
  iApply zesu_encoder_bytes_call_correct; iAssumption.
Qed.

Definition zesuEncoderBooleanCallSpec `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (zesu_c_call 16
    (fun _ sp RET =>
      ∃ tail : spec,
      mmio_range 0x2401a0c0 16 ∗
      spec_trace
        (writeOutputEvents (sp - BV 64 9)%bv (BV 64 1) tail) ∗
      RET (fun _ =>
        mmio_range 0x2401a0c0 16 ∗ spec_trace tail ∗ True)))%I.

Global Instance : LithiumUnfold (@zesuEncoderBooleanCallSpec) := I.

Lemma zesu_encoder_boolean_call_correct `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_16.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_14.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15b9c zesuEncoderBooleanCallSpec.
Proof.
  move => * /=.
  iStartProof.
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try (bv_simplify_arith select (bv_extract 0 3 sp = _)).
  all: try rewrite bv_sign_extend_idemp.
  all: try bv_solve.
  all: try lia.
  all: try (change (bv_extract 0 2 ret = BV 2 0); assumption).
  all: lazymatch goal with |- ?G => fail "side condition" G end.
Qed.

Lemma zesu_encoder_boolean_call_pre `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_16.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_14.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15b9c zesuEncoderBooleanCallSpec.
Proof.
  iStartProof. iIntros "#HbooleanCode #HoutputCode". iModIntro.
  iApply instr_pre_to_body. iNext.
  iApply zesu_encoder_boolean_call_correct; iAssumption.
Qed.

Definition zesuEncoderIntAny `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (∃ (value sp ret : bv 64) (tail : spec),
    encoderIntSpec value sp ret tail True)%I.

Global Instance : LithiumUnfold (@zesuEncoderIntAny) := I.

Lemma zesu_encoder_int_any_pre `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_20.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_14.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15d10 zesuEncoderIntAny.
Proof.
  iStartProof. iIntros "#HintCode #HoutputCode". iModIntro.
  iApply instr_pre_to_body. iNext.
  rewrite instr_pre'_eq. iIntros "Hspec".
  iDestruct "Hspec" as (value sp ret tail) "Hspec".
  iPoseProof (encoder_int_correct value sp ret tail True%I
    with "HintCode HoutputCode") as "Hbody".
  rewrite instr_pre'_eq. iApply ("Hbody" with "Hspec").
Qed.

Definition zesuEncoderBytesAny `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (∃ (data size sp ret : bv 64) (bytes : list (bv 8)) (tail : spec),
    encoderBytesSpec data size sp ret bytes tail True)%I.

Global Instance : LithiumUnfold (@zesuEncoderBytesAny) := I.

Lemma zesu_encoder_bytes_any_pre `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_19.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_20.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_14.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15c6c zesuEncoderBytesAny.
Proof.
  iStartProof. iIntros "#HbytesCode #HintCode #HoutputCode". iModIntro.
  iApply instr_pre_to_body. iNext.
  rewrite instr_pre'_eq. iIntros "Hspec".
  iDestruct "Hspec" as (data size sp ret bytes tail) "Hspec".
  iPoseProof (encoder_bytes_correct data size sp ret bytes tail True%I
    with "HbytesCode HintCode HoutputCode") as "Hbody".
  rewrite instr_pre'_eq. iApply ("Hbody" with "Hspec").
Qed.

Definition zesuEncoderBooleanAny `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (∃ (value sp ret : bv 64) (tail : spec),
    encoderBooleanSpec value sp ret tail True)%I.

Global Instance : LithiumUnfold (@zesuEncoderBooleanAny) := I.

Lemma zesu_encoder_boolean_any_pre `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_16.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_14.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15b9c zesuEncoderBooleanAny.
Proof.
  iStartProof. iIntros "#HbooleanCode #HoutputCode". iModIntro.
  iApply instr_pre_to_body. iNext.
  rewrite instr_pre'_eq. iIntros "Hspec".
  iDestruct "Hspec" as (value sp ret tail) "Hspec".
  iPoseProof (encoder_boolean_correct value sp ret tail True%I
    with "HbooleanCode HoutputCode") as "Hbody".
  rewrite instr_pre'_eq. iApply ("Hbody" with "Hspec").
Qed.
