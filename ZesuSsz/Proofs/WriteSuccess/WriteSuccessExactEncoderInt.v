Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_07 Require Import instrs.
From IslaTraces.write_success_01 Require Import instrs.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBitvector.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutput.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputSemantic.

Definition encoderIntExactPost `{!islaG Sigma} `{!threadG}
    (value sp ret : bv 64) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits ret ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x5" ↦ᵣ RVal_Bits (BV 64 0x2401a0b8) ∗
   "x10" ↦ᵣ RVal_Bits (sp - BV 64 16)%bv ∗
   "x11" ↦ᵣ RVal_Bits (BV 64 8) ∗
   bv_unsigned (sp - BV 64 16)%bv ↦ₘ∗
     writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned value)) ∗
   (bv_unsigned sp - 8) ↦ₘ ret ∗
   mmio_range 0x2401a0c0 16 ∗ spec_trace tail ∗ P ∗ True)%I.

Definition encoderIntExactFrame `{!islaG Sigma} `{!threadG}
    (value sp ret : bv 64) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  ("x2" ↦ᵣ RVal_Bits (sp - BV 64 16)%bv ∗
   (bv_unsigned sp - 8) ↦ₘ ret ∗
   ⌜bv_extract 0 4 sp = BV 4 0⌝ ∗
   ⌜bv_extract 0 3 sp = BV 3 0⌝ ∗
   ⌜0x20000000 <= bv_unsigned sp - 16⌝ ∗
   ⌜bv_unsigned sp < 0x40000000⌝ ∗
   ⌜bv_extract 0 1 ret = BV 1 0⌝ ∗
   ⌜bv_extract 1 1 ret = BV 1 0⌝ ∗
   ⌜bv_extract 0 2 ret = BV 2 0⌝ ∗ P ∗
   instr_pre (bv_unsigned ret) (encoderIntExactPost value sp ret tail P) ∗ True)%I.

Definition encoderIntExactSuffixSpec `{!islaG Sigma} `{!threadG}
    (value sp ret : bv 64) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits (BV 64 0x15d2c) ∗
   "x5" ↦ᵣ RVal_Bits (BV 64 0x2401a0b8) ∗
   "x10" ↦ᵣ RVal_Bits (sp - BV 64 16)%bv ∗
   "x11" ↦ᵣ RVal_Bits (BV 64 8) ∗
   bv_unsigned (sp - BV 64 16)%bv ↦ₘ∗
     writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned value)) ∗
   mmio_range 0x2401a0c0 16 ∗ spec_trace tail ∗
   encoderIntExactFrame value sp ret tail P ∗ True)%I.

Definition encoderIntExactSpec `{!islaG Sigma} `{!threadG}
    (value sp ret : bv 64) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (∃ (old_x5 old_x11 stack0 stack8 : bv 64),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits ret ∗ "x2" ↦ᵣ RVal_Bits sp ∗
    "x5" ↦ᵣ RVal_Bits old_x5 ∗
    "x10" ↦ᵣ RVal_Bits value ∗ "x11" ↦ᵣ RVal_Bits old_x11 ∗
    (bv_unsigned sp - 16) ↦ₘ stack0 ∗
    (bv_unsigned sp - 8) ↦ₘ stack8 ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
      (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned value))) tail) ∗
    ⌜bv_extract 0 4 sp = BV 4 0⌝ ∗
    ⌜bv_extract 0 3 sp = BV 3 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned sp - 16⌝ ∗
    ⌜bv_unsigned sp < 0x40000000⌝ ∗
    ⌜bv_extract 0 1 ret = BV 1 0⌝ ∗
    ⌜bv_extract 1 1 ret = BV 1 0⌝ ∗
    ⌜bv_extract 0 2 ret = BV 2 0⌝ ∗ P ∗
    instr_pre (bv_unsigned ret) (encoderIntExactPost value sp ret tail P))%I.

Global Instance : LithiumUnfold (@encoderIntExactPost) := I.
Global Instance : LithiumUnfold (@encoderIntExactFrame) := I.
Global Instance : LithiumUnfold (@encoderIntExactSuffixSpec) := I.
Global Instance : LithiumUnfold (@encoderIntExactSpec) := I.

#[local] Hint Rewrite bv_sign_extend_64_idemp : isla_coq_rewrite.

Lemma encoder_int_exact_suffix_correct `{!islaG Sigma} `{!threadG}
    (value sp ret : bv 64) (tail : spec) (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15d2c (encoderIntExactSuffixSpec value sp ret tail P).
Proof.
  move => * /=. iStartProof. liARun.
  Unshelve. all: prepare_sidecond; try assumption; try bv_solve; try lia.
  all: try (bv_simplify_arith select (bv_extract 0 4 sp = _)).
  all: try (bv_simplify_arith select (bv_extract 0 3 sp = _)).
  all: try bv_solve.
  all: try (change (bv_extract 0 2 ret = BV 2 0); assumption).
  all: lazymatch goal with |- ?G => fail "suffix residual" G end.
Qed.

Lemma encoder_int_exact_correct `{!islaG Sigma} `{!threadG}
    (value sp ret : bv 64) (tail : spec) (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15d10 (encoderIntExactSpec value sp ret tail P).
Proof.
  move => * /=. iStartProof. iIntros "_ #HencoderCode #HoutputCode".
  iEval (simpl) in "HencoderCode".
  iDestruct "HencoderCode" as
    "(#Hi0 & #Hi1 & #Hi2 & #Hi3 & #Hi4 & #Hi5 & #Hi6 & #Hi7 & #Hi8 & #Hi9 & _)".
  liARun.
  Unshelve. all: prepare_sidecond; try assumption; try rewrite bv_sign_extend_idemp;
    try bv_solve; try lia.
  all: try (bv_simplify_arith select (bv_extract 0 4 sp = _)).
  all: try (bv_simplify_arith select (bv_extract 0 3 sp = _)).
  all: try bv_solve.
  all: try (change (bv_extract 0 2 ret = BV 2 0); assumption).
  all: lazymatch goal with |- ?G => fail "side condition" G end.
  Unshelve. iRename select (bv_unsigned LET6 ↦ₘ value)%I into "Hword".
  iDestruct (mem_mapsto_mapsto_to_byte_array with "Hword") as "Hpayload".
  set (payload := writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned value))).
  set (Q := encoderIntExactFrame value sp ret tail P).
  iAssert (instr_pre 0x15d2c (encoderIntExactSuffixSpec value sp ret tail P))%I as "Hsuffix".
  { iApply instr_pre_to_body. iNext. iApply encoder_int_exact_suffix_correct.
    simpl. iFrame "Hi0 Hi1 Hi2 Hi3 Hi4 Hi5 Hi6 Hi7 Hi8 Hi9". }
  iAssert (□ instr_pre 0x10190 (writeOutputTraceSpec (sp - BV 64 16)%bv
    (BV 64 8) (BV 64 0x15d2c) payload tail Q))%I as "#Houtput".
  { iModIntro. iApply instr_pre_to_body. iNext.
    iApply write_output_trace_correct. iExact "HoutputCode". }
  liARun.
  Unshelve. all: prepare_sidecond; try assumption; try bv_solve; try lia.
  all: try (replace (bv_unsigned LET14) with 0x15d2c by vm_compute; liARun).
  all: try (eexists; eexists; split; [reflexivity | split; reflexivity]).
  all: try (rewrite /Z_to_little_endian /=;
    eexists; eexists; split; [reflexivity | split; reflexivity]).
  all: try (rewrite /encoderIntExactSuffixSpec /Q /payload; reflexivity).
  all: try (replace (bv_unsigned (sp + BV 64 18446744073709551600)%bv)
    with (bv_unsigned (sp - BV 64 16)%bv) by bv_solve; reflexivity).
  rewrite /Z_to_little_endian /= !Z.land_ones; [|lia..].
  rewrite !Z.shiftr_div_pow2; [|lia..]. vm_compute.
  eexists. eexists. repeat split; reflexivity.
Qed.

Lemma encoder_int_exact_pre `{!islaG Sigma} `{!threadG}
    (value sp ret : bv 64) (tail : spec) (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15d10 (encoderIntExactSpec value sp ret tail P).
Proof.
  iStartProof. iIntros "#HencoderCode #HoutputCode". iModIntro.
  iApply instr_pre_to_body. iNext.
  iApply encoder_int_exact_correct; iAssumption.
Qed.

Print Assumptions encoder_int_exact_correct.
