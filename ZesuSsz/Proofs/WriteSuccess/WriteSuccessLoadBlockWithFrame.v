From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index HintsLoadBlock.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Experiments.WriteSuccessLoadBlockAdapter.
Require Import ZesuSsz.Experiments.WriteSuccessLoadBlockCore.

Definition writeSuccessLoadBlockWithFrameSpec
    `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (∃ (sp base : bv 64) (values : list (bv 64)),
    reg_col zesu_instr_sys_regs ∗
    reg_col writeSuccessLoadBlockRegisterShapes ∗
    "x2" ↦ᵣ RVal_Bits sp ∗ "x8" ↦ᵣ RVal_Bits base ∗
    (bv_unsigned base + 720) ↦ₘ∗ values ∗
    bv_unsigned sp ↦ₘ? 312 ∗
    ⌜length values = 16%nat⌝ ∗
    ⌜bv_unsigned base `mod` 8 = 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned base + 720⌝ ∗
    ⌜bv_unsigned base + 848 < 0x40000000⌝ ∗
    ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned sp⌝ ∗
    ⌜bv_unsigned sp + 312 < 0x40000000⌝ ∗
    instr_pre 0x14e00 (
      reg_col zesu_instr_sys_regs ∗
      reg_col (writeSuccessLoadBlockResultRegisters values) ∗
      "x2" ↦ᵣ RVal_Bits sp ∗ "x8" ↦ᵣ RVal_Bits base ∗
      (bv_unsigned base + 720) ↦ₘ∗ values ∗
      writeSuccessLoadBlockStack sp values ∗
      bv_unsigned sp ↦ₘ? 8 ∗
      (bv_unsigned sp + 104) ↦ₘ? 176 ∗ True))%I.

Local Instance : LithiumUnfold (@writeSuccessLoadBlockWithFrameSpec) := I.

Lemma write_success_load_block_with_frame
    `{!islaG Sigma} `{!threadG} :
  instr_body_lookup_resources
    IslaTraces.write_success_blocks.Index.body_lookup -∗
  instr_body 0x14d80 writeSuccessLoadBlockWithFrameSpec.
Proof.
  move => *.
  iStartProof. iIntros "_ #Hcode".
  liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try (cbn; lia).
  all: try bv_solve.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try (cbn; lia).
  all: try bv_solve.
  Unshelve.
  all: try (replace (bv_unsigned sp + 104) with
    (bv_unsigned sp + 96 + 8) by lia; iFrame).
  all: done.
Qed.

Definition writeSuccessLoadTerminalWithFrame
    `{!islaG Sigma} `{!threadG} (sp base : bv 64)
    (values : list (bv 64)) (saved : list valu) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col (writeSuccessLoadBlockResultRegisters values) ∗
   "x2" ↦ᵣ RVal_Bits sp ∗ "x8" ↦ᵣ RVal_Bits base ∗
   (bv_unsigned base + 720) ↦ₘ∗ values ∗
   writeSuccessLoadBlockStack sp values ∗
   bv_unsigned sp ↦ₘ? 8 ∗
   (bv_unsigned sp + 104) ↦ₘ? 176 ∗
   (reg_col writeSuccessLoadCallerFrame ∗
    reg_col (delete 0%nat (writeSuccessLoadSavedRegShapes base saved))) ∗
   True)%I.

Definition writeSuccessLoadMemoryWithFrame
    `{!islaG Sigma} `{!threadG} (sp base : bv 64)
    (values : list (bv 64)) (saved : list valu) : iProp Sigma :=
  ((bv_unsigned base + 720) ↦ₘ∗ values ∗
   bv_unsigned sp ↦ₘ? 312 ∗
   ⌜length values = 16%nat⌝ ∗
   ⌜bv_unsigned base `mod` 8 = 0⌝ ∗
   ⌜0x20000000 <= bv_unsigned base + 720⌝ ∗
   ⌜bv_unsigned base + 848 < 0x40000000⌝ ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
   ⌜0x20000000 <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp + 312 < 0x40000000⌝ ∗
   instr_pre 0x14e00
     (writeSuccessLoadTerminalWithFrame sp base values saved))%I.

Definition writeSuccessLoadAdapterWithFrameSpec
    `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (∃ (sp base b10 b11 : bv 64) (values : list (bv 64)) (saved : list valu),
    writeSuccessLoadRegisterResources sp base b10 b11 saved ∗
    writeSuccessLoadMemoryWithFrame sp base values saved)%I.

Global Instance : LithiumUnfold (@writeSuccessLoadTerminalWithFrame) := I.
Global Instance : LithiumUnfold (@writeSuccessLoadMemoryWithFrame) := I.
Global Instance : LithiumUnfold (@writeSuccessLoadAdapterWithFrameSpec) := I.

Lemma write_success_load_adapter_with_frame_to_core
    `{!islaG Sigma} `{!threadG} :
  writeSuccessLoadAdapterWithFrameSpec ⊢ writeSuccessLoadBlockWithFrameSpec.
Proof.
  rewrite /writeSuccessLoadAdapterWithFrameSpec.
  iIntros "Hspec".
  iDestruct "Hspec" as (sp base b10 b11 values saved) "[Hregs Hmemory]".
  iEval (unfold writeSuccessLoadRegisterResources) in "Hregs".
  iDestruct "Hregs" as "(Hsys & Hcaller & Hsaved & H10 & H11 & H2)".
  iEval (unfold writeSuccessLoadMemoryWithFrame) in "Hmemory".
  iDestruct "Hmemory" as
    "(Hvalues & Hstack & %Hlength & %Hbasealign & %Hbasemin & %Hbasemax &
      %Hspalign & %Hspmin & %Hspmax & Hret)".
  iDestruct (reg_col_lookup writeSuccessLoadCallerRegShapes 1%nat
    (KindReg "x12", BitsShape 64) with "Hcaller") as
    (v12 Hv12) "[H12 Hcaller]"; [reflexivity |].
  apply valu_has_bits_shape in Hv12 as (b12 & ->).
  iDestruct (reg_col_lookup (delete 1%nat writeSuccessLoadCallerRegShapes)
    1%nat (KindReg "x13", BitsShape 64) with "Hcaller") as
    (v13 Hv13) "[H13 Hcaller]"; [reflexivity |].
  apply valu_has_bits_shape in Hv13 as (b13 & ->).
  iDestruct (reg_col_lookup (delete 1%nat
      (delete 1%nat writeSuccessLoadCallerRegShapes)) 1%nat
    (KindReg "x14", BitsShape 64) with "Hcaller") as
    (v14 Hv14) "[H14 Hcaller]"; [reflexivity |].
  apply valu_has_bits_shape in Hv14 as (b14 & ->).
  iDestruct (reg_col_lookup (writeSuccessLoadSavedRegShapes base saved) 0%nat
    (KindReg "x8", ExactShape (RVal_Bits base)) with "Hsaved") as
    (v8 Hv8) "[H8 Hsaved]".
  { destruct saved; reflexivity. }
  cbn in Hv8. subst v8.
  iAssert (instr_pre 0x14e00 (
      reg_col zesu_instr_sys_regs ∗
      reg_col (writeSuccessLoadBlockResultRegisters values) ∗
      "x2" ↦ᵣ RVal_Bits sp ∗ "x8" ↦ᵣ RVal_Bits base ∗
      (bv_unsigned base + 720) ↦ₘ∗ values ∗
      writeSuccessLoadBlockStack sp values ∗
      bv_unsigned sp ↦ₘ? 8 ∗
      (bv_unsigned sp + 104) ↦ₘ? 176 ∗ True))%I
    with "[Hret Hcaller Hsaved]" as "HinternalRet".
  { iApply (instr_pre_wand 0x14e00 0x14e00 true true with "Hret");
      [done | done |].
    iIntros "Hpost".
    iDestruct "Hpost" as
      "(HpostSys & HpostRegs & Hpost2 & Hpost8 & HpostValues &
        HpostStack & Hgap8 & Hgap176 & _)".
    iEval (unfold writeSuccessLoadTerminalWithFrame).
    iFrame. }
  iExists sp, base, values.
  iFrame "Hsys H2 H8 Hvalues Hstack".
  iSplitL "H10 H11 H12 H13 H14".
  { rewrite !reg_col_cons reg_col_nil. iFrame.
    repeat iSplit; iPureIntro; done. }
  repeat iSplit; try iPureIntro; try assumption.
  iExact "HinternalRet".
Qed.

Lemma write_success_load_adapter_with_frame
    `{!islaG Sigma} `{!threadG} :
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x14d80 writeSuccessLoadAdapterWithFrameSpec.
Proof.
  move => *.
  iStartProof. iIntros "_ #Hcode".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  iPoseProof (write_success_load_block_with_frame with "Hcode") as "Hbody".
  iApply (instr_pre_wand 0x14d80 0x14d80 false false with "Hbody");
    [done | done |].
  iApply write_success_load_adapter_with_frame_to_core.
Qed.
