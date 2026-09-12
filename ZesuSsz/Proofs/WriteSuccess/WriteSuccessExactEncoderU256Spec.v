Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncodeWords.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputSemantic.

Definition writeSuccessU256WordsPayload (w0 w1 w2 w3 : bv 64) : list (bv 8) :=
  writeSuccessPrivateBytes
    (writeSuccessEncodeU64 (bv_unsigned w0) ++
     writeSuccessEncodeU64 (bv_unsigned w1) ++
     writeSuccessEncodeU64 (bv_unsigned w2) ++
     writeSuccessEncodeU64 (bv_unsigned w3)).

Lemma writeSuccessU256WordsPayload_encoder w0 w1 w2 w3 :
  writeSuccessU256WordsPayload w0 w1 w2 w3 =
  writeSuccessPrivateBytes (writeSuccessEncodeU256
    (bv_unsigned w0 + 2 ^ 64 *
      (bv_unsigned w1 + 2 ^ 64 * (bv_unsigned w2 + 2 ^ 64 * bv_unsigned w3)))).
Proof. rewrite writeSuccessEncodeU256_words. reflexivity. Qed.

Definition encoderU256ExactPost `{!islaG Sigma} `{!threadG}
    (w0 w1 w2 w3 sp ret : bv 64) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits ret ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x5" ↦ᵣ RVal_Bits (BV 64 0x2401a0b8) ∗
   "x10" ↦ᵣ RVal_Bits (sp - BV 64 48)%bv ∗
   "x11" ↦ᵣ RVal_Bits (BV 64 32) ∗
   "x12" ↦ᵣ RVal_Bits w2 ∗ "x13" ↦ᵣ RVal_Bits w3 ∗
   bv_unsigned (sp - BV 64 48)%bv ↦ₘ∗ writeSuccessU256WordsPayload w0 w1 w2 w3 ∗
   (bv_unsigned sp - 16) ↦ₘ? 8 ∗ (bv_unsigned sp - 8) ↦ₘ ret ∗
   mmio_range 0x2401a0c0 16 ∗ spec_trace tail ∗ P ∗ True)%I.

Definition encoderU256ExactFrame `{!islaG Sigma} `{!threadG}
    (w0 w1 w2 w3 sp ret : bv 64) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  ("x2" ↦ᵣ RVal_Bits (sp - BV 64 48)%bv ∗
   "x12" ↦ᵣ RVal_Bits w2 ∗ "x13" ↦ᵣ RVal_Bits w3 ∗
   (bv_unsigned sp - 16) ↦ₘ? 8 ∗ (bv_unsigned sp - 8) ↦ₘ ret ∗
   ⌜bv_extract 0 4 sp = BV 4 0⌝ ∗ ⌜bv_extract 0 3 sp = BV 3 0⌝ ∗
   ⌜0x20000000 <= bv_unsigned sp - 48⌝ ∗
   ⌜bv_unsigned sp < 0x40000000⌝ ∗
   ⌜bv_extract 0 1 ret = BV 1 0⌝ ∗
   ⌜bv_extract 1 1 ret = BV 1 0⌝ ∗
   ⌜bv_extract 0 2 ret = BV 2 0⌝ ∗ P ∗
   instr_pre (bv_unsigned ret)
     (encoderU256ExactPost w0 w1 w2 w3 sp ret tail P) ∗ True)%I.

Definition encoderU256ExactSuffixSpec `{!islaG Sigma} `{!threadG}
    (w0 w1 w2 w3 sp ret : bv 64) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits (BV 64 0x15cd8) ∗
   "x5" ↦ᵣ RVal_Bits (BV 64 0x2401a0b8) ∗
   "x10" ↦ᵣ RVal_Bits (sp - BV 64 48)%bv ∗
   "x11" ↦ᵣ RVal_Bits (BV 64 32) ∗
   bv_unsigned (sp - BV 64 48)%bv ↦ₘ∗ writeSuccessU256WordsPayload w0 w1 w2 w3 ∗
   mmio_range 0x2401a0c0 16 ∗ spec_trace tail ∗
   encoderU256ExactFrame w0 w1 w2 w3 sp ret tail P ∗ True)%I.

Definition encoderU256ExactSpec `{!islaG Sigma} `{!threadG}
    (w0 w1 w2 w3 sp ret : bv 64) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (∃ old_x5 : bv 64,
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits ret ∗ "x2" ↦ᵣ RVal_Bits sp ∗
    "x5" ↦ᵣ RVal_Bits old_x5 ∗
    "x10" ↦ᵣ RVal_Bits w0 ∗ "x11" ↦ᵣ RVal_Bits w1 ∗
    "x12" ↦ᵣ RVal_Bits w2 ∗ "x13" ↦ᵣ RVal_Bits w3 ∗
    (bv_unsigned sp - 48) ↦ₘ? 48 ∗ mmio_range 0x2401a0c0 16 ∗
    spec_trace (writeOutputEvents (sp - BV 64 48)%bv (BV 64 32)
      (writeSuccessU256WordsPayload w0 w1 w2 w3) tail) ∗
    ⌜bv_extract 0 4 sp = BV 4 0⌝ ∗ ⌜bv_extract 0 3 sp = BV 3 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned sp - 48⌝ ∗
    ⌜bv_unsigned sp < 0x40000000⌝ ∗
    ⌜bv_extract 0 1 ret = BV 1 0⌝ ∗
    ⌜bv_extract 1 1 ret = BV 1 0⌝ ∗
    ⌜bv_extract 0 2 ret = BV 2 0⌝ ∗ P ∗
    instr_pre (bv_unsigned ret)
      (encoderU256ExactPost w0 w1 w2 w3 sp ret tail P) ∗ True)%I.

Global Instance : LithiumUnfold (@encoderU256ExactPost) := I.
Global Instance : LithiumUnfold (@encoderU256ExactFrame) := I.
Global Instance : LithiumUnfold (@encoderU256ExactSuffixSpec) := I.
Global Instance : LithiumUnfold (@encoderU256ExactSpec) := I.

Definition encoderU256ExactAtOutputSpec `{!islaG Sigma} `{!threadG}
    (w0 w1 w2 w3 sp ret : bv 64) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (∃ old_x5 : bv 64,
    reg_col zesu_ram_sys_regs ∗ "x1" ↦ᵣ RVal_Bits ret ∗
    "x5" ↦ᵣ RVal_Bits old_x5 ∗
    "x10" ↦ᵣ RVal_Bits w0 ∗ "x11" ↦ᵣ RVal_Bits w1 ∗
    bv_unsigned (sp - BV 64 48)%bv ↦ₘ∗ writeSuccessU256WordsPayload w0 w1 w2 w3 ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace (writeOutputEvents (sp - BV 64 48)%bv (BV 64 32)
      (writeSuccessU256WordsPayload w0 w1 w2 w3) tail) ∗
    encoderU256ExactFrame w0 w1 w2 w3 sp ret tail P ∗ True)%I.

Global Instance : LithiumUnfold (@encoderU256ExactAtOutputSpec) := I.

Definition encoderU256ExactAtOutputWordsSpec `{!islaG Sigma} `{!threadG}
    (w0 w1 w2 w3 sp ret : bv 64) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (∃ old_x5 : bv 64,
    reg_col zesu_ram_sys_regs ∗ "x1" ↦ᵣ RVal_Bits ret ∗
    "x5" ↦ᵣ RVal_Bits old_x5 ∗
    "x10" ↦ᵣ RVal_Bits w0 ∗ "x11" ↦ᵣ RVal_Bits w1 ∗
    bv_unsigned (sp - BV 64 48)%bv ↦ₘ w0 ∗
    (bv_unsigned (sp - BV 64 48)%bv + 8) ↦ₘ w1 ∗
    (bv_unsigned (sp - BV 64 48)%bv + 16) ↦ₘ w2 ∗
    (bv_unsigned (sp - BV 64 48)%bv + 24) ↦ₘ w3 ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace (writeOutputEvents (sp - BV 64 48)%bv (BV 64 32)
      (writeSuccessU256WordsPayload w0 w1 w2 w3) tail) ∗
    encoderU256ExactFrame w0 w1 w2 w3 sp ret tail P ∗ True)%I.

Global Instance : LithiumUnfold (@encoderU256ExactAtOutputWordsSpec) := I.

Lemma encoder_u256_exact_words_to_payload `{!islaG Sigma} `{!threadG}
    w0 w1 w2 w3 sp ret tail (P : iProp Sigma) :
  encoderU256ExactAtOutputWordsSpec w0 w1 w2 w3 sp ret tail P -∗
  encoderU256ExactAtOutputSpec w0 w1 w2 w3 sp ret tail P.
Proof.
  iIntros "Hwords". iDestruct "Hwords" as (old_x5)
    "(Hsys & H1 & H5 & H10 & H11 & H0 & H1word & H2 & H3 & Hmmio & Htrace & Hframe & _)".
  iDestruct (mem_mapsto_u64_quad_to_byte_array with "H0 H1word H2 H3") as "Hpayload".
  iEval (rewrite -!writeSuccessPrivateEncodeU64 /writeSuccessPrivateBytes
    -!map_app -app_assoc) in "Hpayload".
  iExists old_x5. iFrame.
Qed.

Print Assumptions writeSuccessU256WordsPayload_encoder.
Print Assumptions encoder_u256_exact_words_to_payload.
