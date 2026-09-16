Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_127 Require Import instrs.
From IslaTraces.write_success_01 Require Import instrs.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBitvector.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncodeWords.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutput.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputSemantic.

Import ListNotations.

Definition writeSuccessU128WordsPayload (low high : bv 64) : list (bv 8) :=
  writeSuccessPrivateBytes
    (writeSuccessEncodeU64 (bv_unsigned low) ++
     writeSuccessEncodeU64 (bv_unsigned high)).

Lemma writeSuccessU128WordsPayload_encoder low high :
  writeSuccessU128WordsPayload low high =
  writeSuccessPrivateBytes
    (writeSuccessEncodeU128 (bv_unsigned low + 2 ^ 64 * bv_unsigned high)).
Proof. rewrite writeSuccessEncodeU128_words. reflexivity. Qed.

Lemma writeSuccessU128WordsPayload_take low high :
  take 8 (writeSuccessU128WordsPayload low high) =
  writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned low)).
Proof. reflexivity. Qed.

Lemma writeSuccessU128WordsPayload_drop low high :
  drop 8 (writeSuccessU128WordsPayload low high) =
  writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned high)).
Proof. reflexivity. Qed.

Definition encoderU128ExactPost `{!islaG Sigma} `{!threadG}
    (low high sp ret : bv 64) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits ret ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x5" ↦ᵣ RVal_Bits (BV 64 (mapIoContextAddress defaultMap)) ∗
   "x10" ↦ᵣ RVal_Bits (sp - BV 64 32)%bv ∗
   "x11" ↦ᵣ RVal_Bits (BV 64 16) ∗
   bv_unsigned (sp - BV 64 32)%bv ↦ₘ∗ writeSuccessU128WordsPayload low high ∗
   (bv_unsigned sp - 16) ↦ₘ? 8 ∗ (bv_unsigned sp - 8) ↦ₘ ret ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗ spec_trace tail ∗ P ∗ True)%I.

Definition encoderU128ExactFrame `{!islaG Sigma} `{!threadG}
    (low high sp ret : bv 64) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  ("x2" ↦ᵣ RVal_Bits (sp - BV 64 32)%bv ∗
   (bv_unsigned sp - 16) ↦ₘ? 8 ∗ (bv_unsigned sp - 8) ↦ₘ ret ∗
   ⌜bv_extract 0 4 sp = BV 4 0⌝ ∗ ⌜bv_extract 0 3 sp = BV 3 0⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 32⌝ ∗
   ⌜bv_unsigned sp < (machineRamEnd defaultMap)⌝ ∗
   ⌜bv_extract 0 1 ret = BV 1 0⌝ ∗
   ⌜bv_extract 1 1 ret = BV 1 0⌝ ∗
   ⌜bv_extract 0 2 ret = BV 2 0⌝ ∗ P ∗
   instr_pre (bv_unsigned ret)
     (encoderU128ExactPost low high sp ret tail P) ∗ True)%I.

Definition encoderU128ExactSuffixSpec `{!islaG Sigma} `{!threadG}
    (low high sp ret : bv 64) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits (BV 64 0x15d04) ∗
   "x5" ↦ᵣ RVal_Bits (BV 64 (mapIoContextAddress defaultMap)) ∗
   "x10" ↦ᵣ RVal_Bits (sp - BV 64 32)%bv ∗
   "x11" ↦ᵣ RVal_Bits (BV 64 16) ∗
   bv_unsigned (sp - BV 64 32)%bv ↦ₘ∗ writeSuccessU128WordsPayload low high ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗ spec_trace tail ∗
   encoderU128ExactFrame low high sp ret tail P ∗ True)%I.

Definition encoderU128ExactSpec `{!islaG Sigma} `{!threadG}
    (low high sp ret : bv 64) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (∃ old_x5 : bv 64,
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits ret ∗ "x2" ↦ᵣ RVal_Bits sp ∗
    "x5" ↦ᵣ RVal_Bits old_x5 ∗
    "x10" ↦ᵣ RVal_Bits low ∗ "x11" ↦ᵣ RVal_Bits high ∗
    (bv_unsigned sp - 32) ↦ₘ? 32 ∗
    mmio_range (machineOutputAddress defaultMap) 16 ∗
    spec_trace (writeOutputEvents (sp - BV 64 32)%bv (BV 64 16)
      (writeSuccessU128WordsPayload low high) tail) ∗
    ⌜bv_extract 0 4 sp = BV 4 0⌝ ∗ ⌜bv_extract 0 3 sp = BV 3 0⌝ ∗
    ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 32⌝ ∗
    ⌜bv_unsigned sp < (machineRamEnd defaultMap)⌝ ∗
    ⌜bv_extract 0 1 ret = BV 1 0⌝ ∗
    ⌜bv_extract 1 1 ret = BV 1 0⌝ ∗
    ⌜bv_extract 0 2 ret = BV 2 0⌝ ∗ P ∗
    instr_pre (bv_unsigned ret)
      (encoderU128ExactPost low high sp ret tail P) ∗ True)%I.

Definition encoderU128ExactAtOutputSpec `{!islaG Sigma} `{!threadG}
    (low high sp ret : bv 64) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (∃ old_x5 : bv 64,
    reg_col zesu_ram_sys_regs ∗ "x1" ↦ᵣ RVal_Bits ret ∗
    "x5" ↦ᵣ RVal_Bits old_x5 ∗
    "x10" ↦ᵣ RVal_Bits low ∗ "x11" ↦ᵣ RVal_Bits high ∗
    bv_unsigned (sp - BV 64 32)%bv ↦ₘ∗ writeSuccessU128WordsPayload low high ∗
    mmio_range (machineOutputAddress defaultMap) 16 ∗
    spec_trace (writeOutputEvents (sp - BV 64 32)%bv (BV 64 16)
      (writeSuccessU128WordsPayload low high) tail) ∗
    encoderU128ExactFrame low high sp ret tail P ∗ True)%I.

Global Instance : LithiumUnfold (@encoderU128ExactPost) := I.
Global Instance : LithiumUnfold (@encoderU128ExactFrame) := I.
Global Instance : LithiumUnfold (@encoderU128ExactSuffixSpec) := I.
Global Instance : LithiumUnfold (@encoderU128ExactSpec) := I.
Global Instance : LithiumUnfold (@encoderU128ExactAtOutputSpec) := I.

Definition encoderU128ExactAtOutputWordsSpec `{!islaG Sigma} `{!threadG}
    (low high sp ret : bv 64) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (∃ old_x5 : bv 64,
    reg_col zesu_ram_sys_regs ∗ "x1" ↦ᵣ RVal_Bits ret ∗
    "x5" ↦ᵣ RVal_Bits old_x5 ∗
    "x10" ↦ᵣ RVal_Bits low ∗ "x11" ↦ᵣ RVal_Bits high ∗
    bv_unsigned (sp - BV 64 32)%bv ↦ₘ low ∗
    (bv_unsigned (sp - BV 64 32)%bv + 8) ↦ₘ high ∗
    mmio_range (machineOutputAddress defaultMap) 16 ∗
    spec_trace (writeOutputEvents (sp - BV 64 32)%bv (BV 64 16)
      (writeSuccessU128WordsPayload low high) tail) ∗
    encoderU128ExactFrame low high sp ret tail P ∗ True)%I.

Global Instance : LithiumUnfold (@encoderU128ExactAtOutputWordsSpec) := I.

Lemma encoder_u128_exact_words_to_payload `{!islaG Sigma} `{!threadG}
    low high sp ret tail (P : iProp Sigma) :
  encoderU128ExactAtOutputWordsSpec low high sp ret tail P -∗
  encoderU128ExactAtOutputSpec low high sp ret tail P.
Proof.
  iIntros "Hwords". iDestruct "Hwords" as (old_x5)
    "(Hsys & H1 & H5 & H10 & H11 & Hlow & Hhigh & Hmmio & Htrace & Hframe & _)".
  iDestruct (mem_mapsto_u64_pair_to_byte_array with "Hlow Hhigh") as "Hpayload".
  iEval (rewrite -!writeSuccessPrivateEncodeU64 /writeSuccessPrivateBytes -map_app)
    in "Hpayload".
  iExists old_x5. iFrame.
Qed.

Definition zesuEncoderU128PayloadCallSpec `{!islaG Sigma} `{!threadG} :
    iProp Sigma :=
  (∃ (low high sp ret : bv 64) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits ret ∗ "x2" ↦ᵣ RVal_Bits sp ∗
    ("x5" ↦ᵣ: fun r5 => ⌜valu_has_shape r5 (BitsShape 64)⌝) ∗
    "x10" ↦ᵣ RVal_Bits low ∗ "x11" ↦ᵣ RVal_Bits high ∗
    (bv_unsigned sp - 32) ↦ₘ? 32 ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗
    spec_trace (writeOutputEvents (sp - BV 64 32)%bv (BV 64 16)
      (writeSuccessPrivateBytes (writeSuccessEncodeU128
        (bv_unsigned low + 2 ^ 64 * bv_unsigned high))) tail) ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 32⌝ ∗
    ⌜bv_unsigned sp < (machineRamEnd defaultMap)⌝ ∗
    ⌜bv_extract 0 1 ret = BV 1 0⌝ ∗
    ⌜bv_extract 1 1 ret = BV 1 0⌝ ∗
    ⌜bv_extract 0 2 ret = BV 2 0⌝ ∗
    instr_pre (bv_unsigned ret)
      (reg_col zesu_ram_sys_regs ∗
       "x1" ↦ᵣ RVal_Bits ret ∗ "x2" ↦ᵣ RVal_Bits sp ∗
       "x5" ↦ᵣ RVal_Bits (BV 64 (mapIoContextAddress defaultMap)) ∗
       "x10" ↦ᵣ RVal_Bits (sp - BV 64 32)%bv ∗
       "x11" ↦ᵣ RVal_Bits (BV 64 16) ∗
       (bv_unsigned sp - 32) ↦ₘ? 32 ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗
       spec_trace tail ∗ True) ∗ True)%I.

Global Instance : LithiumUnfold (@zesuEncoderU128PayloadCallSpec) := I.

#[local] Hint Rewrite bv_sign_extend_64_idemp : isla_coq_rewrite.

Lemma encoder_u128_exact_suffix_correct `{!islaG Sigma} `{!threadG}
    (low high sp ret : bv 64) (tail : spec) (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_127.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15d04 (encoderU128ExactSuffixSpec low high sp ret tail P).
Proof.
  move => * /=. iStartProof. liARun.
  Unshelve. all: prepare_sidecond; try assumption; try bv_solve; try lia.
  all: try (bv_simplify_arith select (bv_extract 0 4 sp = _)).
  all: try (bv_simplify_arith select (bv_extract 0 3 sp = _)).
  all: try bv_solve.
  all: try (change (bv_extract 0 2 ret = BV 2 0); assumption).
  all: lazymatch goal with |- ?G => fail "u128 suffix residual" G end.
Qed.

Print Assumptions writeSuccessPrivateEncodeU64.
Print Assumptions writeSuccessU128WordsPayload_encoder.
Print Assumptions encoder_u128_exact_words_to_payload.
