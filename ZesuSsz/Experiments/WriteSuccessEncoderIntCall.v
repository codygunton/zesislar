From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_08 Require Import instrs.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Experiments.WriteSuccess.
Require Import ZesuSsz.Experiments.WriteSuccessCalls.

#[local] Hint Rewrite (@bv_sign_extend_idemp 64) :
  lithium_rewrite isla_coq_rewrite.

#[local] Hint Extern 7
  (FindInContext (FindInstrKind ?address ?later) FICSyntactic) =>
  let reduced := eval vm_compute in address in
  first [ constr_eq address reduced; fail 1
        | change (FindInContext (FindInstrKind reduced later) FICSyntactic);
          typeclasses eauto ] : typeclass_instances.

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
  ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
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
  ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15d10 zesuEncoderIntCallSpec.
Proof.
  iStartProof. iIntros "#HintCode #HoutputCode". iModIntro.
  iApply instr_pre_to_body. iNext.
  iApply zesu_encoder_int_call_correct; iAssumption.
Qed.
