From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import InstrSpecs.Specs.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCalls.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessLoadBlockCore.

Import ListNotations.

Lemma bv_add_32_mod_8_zero (sp : bv 64)
    (Halign : bv_extract 0 4 sp = BV 4 0)
    (Hadd : bv_unsigned (sp + 32) = (bv_unsigned sp + 32)%Z) :
  bv_unsigned (sp + 32) `mod` 8 = 0.
Proof.
  rewrite Hadd.
  bv_simplify_arith Halign.
  unfold bv_wrap, bv_modulus in Halign.
  cbn in Halign.
  nia.
Qed.

Lemma bv_sub_2000_mod_8_zero (sp : bv 64)
    (Halign : bv_extract 0 4 sp = BV 4 0)
    (Hsub : bv_unsigned (sp - 2000) = (bv_unsigned sp - 2000)%Z) :
  bv_unsigned (sp - 2000) `mod` 8 = 0.
Proof.
  rewrite Hsub.
  bv_simplify_arith Halign.
  unfold bv_wrap, bv_modulus in Halign.
  cbn in Halign.
  nia.
Qed.

Definition writeSuccessLoadCallerRegisters : list string :=
  ["x1"; "x12"; "x13"; "x14"; "x15"; "x16"; "x17"] ++ tmp_registers.

Definition writeSuccessLoadCallerRegShapes : list (reg_kind * valu_shape) :=
  (fun register => (KindReg register, BitsShape 64))
    <$> writeSuccessLoadCallerRegisters.

Definition writeSuccessLoadSavedRegisters : list string :=
  ["x8"; "x9"; "x18"; "x19"; "x20"; "x21";
   "x22"; "x23"; "x24"; "x25"; "x26"; "x27"].

Definition writeSuccessLoadSavedRegShapes (base : bv 64)
    (saved : list valu) : list (reg_kind * valu_shape) :=
  zip_with (fun register value => (KindReg register, ExactShape value))
    writeSuccessLoadSavedRegisters (RVal_Bits base :: saved).

Definition writeSuccessLoadCallerFrame : list (reg_kind * valu_shape) :=
  delete 1%nat (delete 1%nat (delete 1%nat writeSuccessLoadCallerRegShapes)).

Definition writeSuccessLoadRegisterResources `{!islaG Sigma} `{!threadG}
    (sp base b10 b11 : bv 64) (saved : list valu) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col writeSuccessLoadCallerRegShapes ∗
   reg_col (writeSuccessLoadSavedRegShapes base saved) ∗
   "x10" ↦ᵣ RVal_Bits b10 ∗ "x11" ↦ᵣ RVal_Bits b11 ∗
   "x2" ↦ᵣ RVal_Bits sp)%I.

Definition writeSuccessLoadTerminal `{!islaG Sigma} `{!threadG}
    (sp base : bv 64) (values : list (bv 64)) (saved : list valu) :
    iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col (writeSuccessLoadBlockResultRegisters values) ∗
   "x2" ↦ᵣ RVal_Bits sp ∗ "x8" ↦ᵣ RVal_Bits base ∗
   (bv_unsigned base + 720) ↦ₘ∗ values ∗
   writeSuccessLoadBlockStack sp values ∗
   (reg_col writeSuccessLoadCallerFrame ∗
    reg_col (delete 0%nat (writeSuccessLoadSavedRegShapes base saved))) ∗
   True)%I.

Definition writeSuccessLoadMemoryResources `{!islaG Sigma} `{!threadG}
    (sp base : bv 64) (values : list (bv 64)) (saved : list valu) :
    iProp Sigma :=
  ((bv_unsigned base + 720) ↦ₘ∗ values ∗
   bv_unsigned sp ↦ₘ? 312 ∗
   ⌜length values = 16%nat⌝ ∗
   ⌜bv_unsigned base `mod` 8 = 0⌝ ∗
   ⌜0x20000000 <= bv_unsigned base + 720⌝ ∗
   ⌜bv_unsigned base + 848 < 0x40000000⌝ ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
   ⌜0x20000000 <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp + 312 < 0x40000000⌝ ∗
   instr_pre 0x14e00 (writeSuccessLoadTerminal sp base values saved))%I.

Definition writeSuccessLoadBlockAdapterSpec `{!islaG Sigma} `{!threadG} :
    iProp Sigma :=
  (∃ (sp base b10 b11 : bv 64) (values : list (bv 64)) (saved : list valu),
    writeSuccessLoadRegisterResources sp base b10 b11 saved ∗
    writeSuccessLoadMemoryResources sp base values saved)%I.

Lemma write_success_load_block_adapter_to_core `{!islaG Sigma} `{!threadG} :
  writeSuccessLoadBlockAdapterSpec ⊢ writeSuccessLoadBlockSpec.
Proof.
  rewrite /writeSuccessLoadBlockAdapterSpec.
  iIntros "Hspec".
  iDestruct "Hspec" as (sp base b10 b11 values saved) "[Hregs Hmemory]".
  iEval (unfold writeSuccessLoadRegisterResources) in "Hregs".
  iDestruct "Hregs" as "(Hsys & Hcaller & Hsaved & H10 & H11 & H2)".
  iEval (unfold writeSuccessLoadMemoryResources) in "Hmemory".
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
      writeSuccessLoadBlockStack sp values ∗ True))%I
    with "[Hret Hcaller Hsaved]" as "HinternalRet".
  { iApply (instr_pre_wand 0x14e00 0x14e00 true true with "Hret");
      [done | done |].
    iIntros "Hpost".
    iDestruct "Hpost" as
      "(HpostSys & HpostRegs & Hpost2 & Hpost8 & HpostValues & HpostStack & _)".
    iEval (unfold writeSuccessLoadTerminal). iFrame. }
  iExists sp, base, values.
  iFrame "Hsys H2 H8 Hvalues Hstack".
  iSplitL "H10 H11 H12 H13 H14".
  { rewrite !reg_col_cons reg_col_nil. iFrame.
    repeat iSplit; iPureIntro; done. }
  repeat iSplit; try iPureIntro; try assumption.
  iExact "HinternalRet".
Qed.

Lemma write_success_load_block_adapter_correct `{!islaG Sigma} `{!threadG} :
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x14d80 writeSuccessLoadBlockAdapterSpec.
Proof.
  move => *.
  iStartProof. iIntros "_ #Hcode".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  iPoseProof (write_success_load_block_correct with "Hcode") as "Hbody".
  iApply (instr_pre_wand 0x14d80 0x14d80 false false with "Hbody");
    [done | done |].
  iApply write_success_load_block_adapter_to_core.
Qed.

Lemma write_success_load_block_adapter_pre `{!islaG Sigma} `{!threadG} :
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x14d80 writeSuccessLoadBlockAdapterSpec.
Proof.
  iStartProof. iIntros "#Hcode". iModIntro.
  iApply instr_pre_to_body. iNext.
  iApply write_success_load_block_adapter_correct. iExact "Hcode".
Qed.
