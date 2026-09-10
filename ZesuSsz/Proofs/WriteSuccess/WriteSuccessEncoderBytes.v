From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_06 Require Import instrs.
From IslaTraces.write_success_07 Require Import instrs.
From IslaTraces.write_success_01 Require Import instrs.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBitvector.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderInt.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderBytesSuffix.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutput.

Import ListNotations.

#[local] Hint Rewrite bv_sign_extend_64_idemp : isla_coq_rewrite.

Definition encoderBytesIntCallAnySpec `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (∃ (data size sp ret : bv 64) (bytes : list (bv 8))
      (old_x6 old_s0 old_s1 stack2 : bv 64) (tail : spec) (P : iProp Sigma),
    encoderIntSpec size (sp - BV 64 32)%bv (BV 64 0x15c90)
      (writeOutputEvents data size tail)
      (encoderBytesSuffixFrame data size sp ret bytes
        old_x6 old_s0 old_s1 stack2 tail P))%I.

Global Instance : LithiumUnfold (@encoderBytesIntCallAnySpec) := I.

Lemma encoder_bytes_int_call_any_pre `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15d10 encoderBytesIntCallAnySpec.
Proof.
  iStartProof. iIntros "#HintCode #HoutputCode". iModIntro.
  iApply instr_pre_to_body. iNext.
  rewrite instr_pre'_eq. iIntros "Hspec".
  iDestruct "Hspec" as
    (data size sp ret bytes old_x6 old_s0 old_s1 stack2 tail P) "Hspec".
  iPoseProof (encoder_int_correct size (sp - BV 64 32)%bv
    (BV 64 0x15c90) (writeOutputEvents data size tail)
    (encoderBytesSuffixFrame data size sp ret bytes
      old_x6 old_s0 old_s1 stack2 tail P) with
    "HintCode HoutputCode") as "Hbody".
  rewrite instr_pre'_eq. iApply ("Hbody" with "Hspec").
Qed.

Definition encoderBytesSpec `{!islaG Sigma} `{!threadG}
    (data size sp ret : bv 64) (bytes : list (bv 8))
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (∃ (old_x5 old_x6 old_s0 old_s1
       stack0 stack1 stack2 stack3 stack4 stack5 : bv 64),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits ret ∗ "x2" ↦ᵣ RVal_Bits sp ∗
    "x5" ↦ᵣ RVal_Bits old_x5 ∗
    "x6" ↦ᵣ RVal_Bits old_x6 ∗
    "x8" ↦ᵣ RVal_Bits old_s0 ∗ "x9" ↦ᵣ RVal_Bits old_s1 ∗
    "x10" ↦ᵣ RVal_Bits data ∗ "x11" ↦ᵣ RVal_Bits size ∗
    (bv_unsigned sp - 48) ↦ₘ stack0 ∗
    (bv_unsigned sp - 40) ↦ₘ stack1 ∗
    (bv_unsigned sp - 32) ↦ₘ stack2 ∗
    (bv_unsigned sp - 24) ↦ₘ stack3 ∗
    (bv_unsigned sp - 16) ↦ₘ stack4 ∗
    (bv_unsigned sp - 8) ↦ₘ stack5 ∗
    bv_unsigned data ↦ₘ∗ bytes ∗
    ⌜bv_unsigned size = length bytes⌝ ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace
      (writeOutputEvents ((sp - BV 64 48)%bv) (BV 64 8)
        (writeOutputEvents data size tail)) ∗
    ⌜bv_extract 0 4 sp = BV 4 0⌝ ∗
    ⌜bv_extract 0 3 sp = BV 3 0⌝ ∗
    ⌜(0x20000000 <= bv_unsigned sp - 48)%Z⌝ ∗
    ⌜(bv_unsigned sp < 0x40000000)%Z⌝ ∗
    ⌜bv_extract 0 1 ret = BV 1 0⌝ ∗
    ⌜bv_extract 1 1 ret = BV 1 0⌝ ∗
    ⌜bv_extract 0 2 ret = BV 2 0⌝ ∗ P ∗
    instr_pre (bv_unsigned ret)
      (∃ (final_x6 : bv 64),
       reg_col zesu_ram_sys_regs ∗
       "x1" ↦ᵣ RVal_Bits ret ∗ "x2" ↦ᵣ RVal_Bits sp ∗
       "x5" ↦ᵣ RVal_Bits (BV 64 0x2401a0b8) ∗
       "x6" ↦ᵣ RVal_Bits final_x6 ∗
       "x8" ↦ᵣ RVal_Bits old_s0 ∗ "x9" ↦ᵣ RVal_Bits old_s1 ∗
       "x10" ↦ᵣ RVal_Bits data ∗ "x11" ↦ᵣ RVal_Bits size ∗
       (bv_unsigned sp - 48) ↦ₘ size ∗
       (bv_unsigned sp - 40) ↦ₘ (BV 64 0x15c90) ∗
       (bv_unsigned sp - 32) ↦ₘ stack2 ∗
       (bv_unsigned sp - 24) ↦ₘ old_s1 ∗
       (bv_unsigned sp - 16) ↦ₘ old_s0 ∗
       (bv_unsigned sp - 8) ↦ₘ ret ∗
       bv_unsigned data ↦ₘ∗ bytes ∗
       mmio_range 0x2401a0c0 16 ∗ spec_trace tail ∗ P ∗ True) ∗ True)%I.

Global Instance : LithiumUnfold (@encoderBytesSpec) := I.

Lemma encoder_bytes_correct `{!islaG Sigma} `{!threadG}
    (data size sp ret : bv 64) (bytes : list (bv 8))
    (tail : spec) (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_06.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15c6c (encoderBytesSpec data size sp ret bytes tail P).
Proof.
  move => * /=.
  iStartProof.
  iIntros "_ #HbytesCode #HintCode #HoutputCode".
  iPoseProof (encoder_bytes_int_call_any_pre with
    "HintCode HoutputCode") as "#Hint".
  iEval (simpl) in "HbytesCode".
  iDestruct "HbytesCode" as
    "(#H00 & #H04 & #H08 & #H0c & #H10 & #H14 & #H18 & #H1c &
      #H20 & #H24 & #H28 & #H2c & #H30 & #H34 & #H38 & #H3c &
      #H40 & _)".
  liARun.
  iPoseProof (encoder_bytes_suffix_pre data size sp ret bytes
    old_x6 old_s0 old_s1 stack2 tail P with
    "H24 H28 H2c H30 H34 H38 H3c H40 HoutputCode") as "#Hsuffix".
  iClear "H24 H28 H2c H30 H34 H38 H3c H40".
  iClear "HintCode HoutputCode".
  iExists (P, tail, stack2, old_s1, old_s0, old_x6, bytes,
    ret, sp, size, data, tt)ₗ.
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try (bv_simplify_arith select (bv_extract 0 4 sp = _)).
  all: try (bv_simplify_arith select (bv_extract 0 3 sp = _)).
  all: try rewrite bv_sign_extend_idemp.
  all: try bv_solve.
  all: try lia.
  all: try (change (bv_extract 0 2 ret = BV 2 0); assumption).
  Unshelve. all: try exact inhabitant.
  all: lazymatch goal with |- ?G => fail "side condition" G end.
Qed.
