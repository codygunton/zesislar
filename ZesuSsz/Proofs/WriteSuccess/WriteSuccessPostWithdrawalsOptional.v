Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
From IslaTraces.write_success_98 Require Import a15718_spec.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderOptionalU64Call.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeSuffixOptionalU64159b8SomeAssembly.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeSuffixOptionalU64159b8NoneAssembly.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeSuffixOptionalU64159b8Defs.

Import ListNotations.

Definition writeSuccessPostWithdrawalsSaved : list string :=
  ["x8"; "x9"; "x18"; "x19"; "x20"; "x21";
   "x22"; "x23"; "x24"; "x25"; "x26"; "x27"].

Definition writeSuccessPostWithdrawalsVolatile : list string :=
  ["x3"; "x4"; "x6"; "x7"; "x12"; "x13"; "x14"; "x15"; "x16";
   "x17"; "x28"; "x29"; "x30"; "x31"].

Definition writeSuccessPostWithdrawalsRemainingEvents
    (sp data size : bv 64) (tail : spec) : spec :=
  writeOutputEventsAny (sp - BV 64 48)%bv (BV 64 8)
    (writeOutputEventsAny data size
      (writeOutputEventsAny (sp + BV 64 1000)%bv (BV 64 32) tail)).

Definition writeSuccessPostWithdrawalsAt1571c
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp optionalValue optionalTag data size root : bv 64)
      (bytes : list (bv 8))
      (saved : list (bv 64)) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
      (["x1"; "x12"; "x13"; "x14"; "x15"; "x16"; "x17"] ++
       tmp_registers)) ∗
    reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
      ["x3"; "x4"]) ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x10" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    "x11" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    reg_col (zip_with (fun register (value : bv 64) =>
      (KindReg register, ExactShape (RVal_Bits value)))
      writeSuccessPostWithdrawalsSaved saved) ∗
    ⌜length saved = length writeSuccessPostWithdrawalsSaved⌝ ∗
    (bv_unsigned sp - 48) ↦ₘ? 48 ∗
    bv_unsigned (sp + BV 64 1624)%bv ↦ₘ optionalValue ∗
    (bv_unsigned (sp + BV 64 1624)%bv + 8) ↦ₘ optionalTag ∗
    (bv_unsigned sp + 1152) ↦ₘ optionalValue ∗
    (bv_unsigned sp + 1160) ↦ₘ optionalTag ∗
    (bv_unsigned sp + 1168) ↦ₘ data ∗
    (bv_unsigned sp + 1176) ↦ₘ size ∗
    (bv_unsigned sp + 1000) ↦ₘ root ∗
    bv_unsigned data ↦ₘ∗ bytes ∗
    ⌜bv_unsigned size = length bytes⌝ ∗
    mmio_range (machineOutputAddress defaultMap) 16 ∗
    spec_trace (writeSuccessPostWithdrawalsRemainingEvents sp data size tail) ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 48⌝ ∗
    ⌜bv_unsigned sp < (machineRamEnd defaultMap)⌝ ∗
    ⌜bv_unsigned sp + 1896 < (machineRamEnd defaultMap)⌝ ∗ P ∗ True)%I.

Global Instance : LithiumUnfold
    (@writeSuccessPostWithdrawalsAt1571c) := I.

Definition writeSuccessPostWithdrawalsAt15700
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp optionalValue optionalTag data size root : bv 64)
      (bytes : list (bv 8)) (saved : list (bv 64)) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits (BV 64 0x15700) ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x5" ↦ᵣ RVal_Bits (BV 64 (mapIoContextAddress defaultMap)) ∗
    "x10" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    "x11" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
      writeSuccessPostWithdrawalsVolatile) ∗
    reg_col (zip_with (fun register (value : bv 64) =>
      (KindReg register, ExactShape (RVal_Bits value)))
      writeSuccessPostWithdrawalsSaved saved) ∗
    ⌜length saved = length writeSuccessPostWithdrawalsSaved⌝ ∗
    (bv_unsigned sp - 48) ↦ₘ? 48 ∗
    (bv_unsigned sp + 1624) ↦ₘ? 16 ∗
    (bv_unsigned sp + 1152) ↦ₘ optionalValue ∗
    (bv_unsigned sp + 1160) ↦ₘ optionalTag ∗
    (bv_unsigned sp + 1168) ↦ₘ data ∗
    (bv_unsigned sp + 1176) ↦ₘ size ∗
    (bv_unsigned sp + 1000) ↦ₘ root ∗
    bv_unsigned data ↦ₘ∗ bytes ∗
    ⌜bv_unsigned size = length bytes⌝ ∗
    mmio_range (machineOutputAddress defaultMap) 16 ∗
    ((⌜bv_extract 0 8 optionalTag = BV 8 0⌝ ∗
       spec_trace (writeOutputEventsAny (sp - BV 64 9)%bv (BV 64 1)
         (writeSuccessPostWithdrawalsRemainingEvents sp data size tail))) ∨
     (⌜bv_extract 0 8 optionalTag <> BV 8 0⌝ ∗
       spec_trace (writeOutputEventsAny (sp - BV 64 25)%bv (BV 64 1)
         (writeOutputEventsAny (sp - BV 64 16)%bv (BV 64 8)
           (writeSuccessPostWithdrawalsRemainingEvents sp data size tail))))) ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 48⌝ ∗
    ⌜bv_unsigned sp < (machineRamEnd defaultMap)⌝ ∗
    ⌜bv_unsigned sp + 1896 < (machineRamEnd defaultMap)⌝ ∗ P ∗ True)%I.

Global Instance : LithiumUnfold
    (@writeSuccessPostWithdrawalsAt15700) := I.

Definition writeSuccessPostWithdrawalsAt15718
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp optionalValue optionalTag data size root : bv 64)
      (bytes : list (bv 8)) (saved : list (bv 64)) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits (BV 64 0x15714) ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x5" ↦ᵣ RVal_Bits (BV 64 (mapIoContextAddress defaultMap)) ∗
    "x10" ↦ᵣ RVal_Bits (sp + BV 64 1624)%bv ∗
    "x11" ↦ᵣ RVal_Bits optionalTag ∗
    reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
      writeSuccessPostWithdrawalsVolatile) ∗
    reg_col (zip_with (fun register (value : bv 64) =>
      (KindReg register, ExactShape (RVal_Bits value)))
      writeSuccessPostWithdrawalsSaved saved) ∗
    ⌜length saved = length writeSuccessPostWithdrawalsSaved⌝ ∗
    (bv_unsigned sp - 48) ↦ₘ? 48 ∗
    bv_unsigned (sp + BV 64 1624)%bv ↦ₘ optionalValue ∗
    (bv_unsigned (sp + BV 64 1624)%bv + 8) ↦ₘ optionalTag ∗
    (bv_unsigned sp + 1152) ↦ₘ optionalValue ∗
    (bv_unsigned sp + 1160) ↦ₘ optionalTag ∗
    (bv_unsigned sp + 1168) ↦ₘ data ∗
    (bv_unsigned sp + 1176) ↦ₘ size ∗
    (bv_unsigned sp + 1000) ↦ₘ root ∗
    bv_unsigned data ↦ₘ∗ bytes ∗
    ⌜bv_unsigned size = length bytes⌝ ∗
    mmio_range (machineOutputAddress defaultMap) 16 ∗
    ((⌜bv_extract 0 8 optionalTag = BV 8 0⌝ ∗
       spec_trace (writeOutputEventsAny (sp - BV 64 9)%bv (BV 64 1)
         (writeSuccessPostWithdrawalsRemainingEvents sp data size tail))) ∨
     (⌜bv_extract 0 8 optionalTag <> BV 8 0⌝ ∗
       spec_trace (writeOutputEventsAny (sp - BV 64 25)%bv (BV 64 1)
         (writeOutputEventsAny (sp - BV 64 16)%bv (BV 64 8)
           (writeSuccessPostWithdrawalsRemainingEvents sp data size tail))))) ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 48⌝ ∗
    ⌜bv_unsigned sp < (machineRamEnd defaultMap)⌝ ∗
    ⌜bv_unsigned sp + 1896 < (machineRamEnd defaultMap)⌝ ∗ P ∗ True)%I.

Global Instance : LithiumUnfold
    (@writeSuccessPostWithdrawalsAt15718) := I.

Definition writeSuccessPostWithdrawals15700State
    `{!islaG Sigma} `{!threadG}
    (sp optionalValue optionalTag data size root : bv 64)
    (bytes : list (bv 8)) (saved : list (bv 64)) (tail : spec)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x1" ↦ᵣ RVal_Bits (BV 64 0x15700) ∗
   "x2" ↦ᵣ RVal_Bits sp ∗ "x5" ↦ᵣ RVal_Bits (BV 64 (mapIoContextAddress defaultMap)) ∗
   "x10" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
   "x11" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
   reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
     writeSuccessPostWithdrawalsVolatile) ∗
   reg_col (zip_with (fun register (value : bv 64) =>
     (KindReg register, ExactShape (RVal_Bits value)))
     writeSuccessPostWithdrawalsSaved saved) ∗
   ⌜length saved = length writeSuccessPostWithdrawalsSaved⌝ ∗
   (bv_unsigned sp - 48) ↦ₘ? 48 ∗ (bv_unsigned sp + 1624) ↦ₘ? 16 ∗
   (bv_unsigned sp + 1152) ↦ₘ optionalValue ∗
   (bv_unsigned sp + 1160) ↦ₘ optionalTag ∗
   (bv_unsigned sp + 1168) ↦ₘ data ∗ (bv_unsigned sp + 1176) ↦ₘ size ∗
   (bv_unsigned sp + 1000) ↦ₘ root ∗ bv_unsigned data ↦ₘ∗ bytes ∗
   ⌜bv_unsigned size = length bytes⌝ ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗
   ((⌜bv_extract 0 8 optionalTag = BV 8 0⌝ ∗
      spec_trace (writeOutputEventsAny (sp - BV 64 9)%bv (BV 64 1)
        (writeSuccessPostWithdrawalsRemainingEvents sp data size tail))) ∨
    (⌜bv_extract 0 8 optionalTag <> BV 8 0⌝ ∗
      spec_trace (writeOutputEventsAny (sp - BV 64 25)%bv (BV 64 1)
        (writeOutputEventsAny (sp - BV 64 16)%bv (BV 64 8)
          (writeSuccessPostWithdrawalsRemainingEvents sp data size tail))))) ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 48⌝ ∗
   ⌜bv_unsigned sp < (machineRamEnd defaultMap)⌝ ∗
   ⌜bv_unsigned sp + 1896 < (machineRamEnd defaultMap)⌝ ∗ P ∗ True)%I.

Definition writeSuccessPostWithdrawals15718State
    `{!islaG Sigma} `{!threadG}
    (sp optionalValue optionalTag data size root : bv 64)
    (bytes : list (bv 8)) (saved : list (bv 64)) (tail : spec)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x1" ↦ᵣ RVal_Bits (BV 64 0x15714) ∗
   "x2" ↦ᵣ RVal_Bits sp ∗ "x5" ↦ᵣ RVal_Bits (BV 64 (mapIoContextAddress defaultMap)) ∗
   "x10" ↦ᵣ RVal_Bits (sp + BV 64 1624)%bv ∗
   "x11" ↦ᵣ RVal_Bits optionalTag ∗
   reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
     writeSuccessPostWithdrawalsVolatile) ∗
   reg_col (zip_with (fun register (value : bv 64) =>
     (KindReg register, ExactShape (RVal_Bits value)))
     writeSuccessPostWithdrawalsSaved saved) ∗
   ⌜length saved = length writeSuccessPostWithdrawalsSaved⌝ ∗
   (bv_unsigned sp - 48) ↦ₘ? 48 ∗
   bv_unsigned (sp + BV 64 1624)%bv ↦ₘ optionalValue ∗
   (bv_unsigned (sp + BV 64 1624)%bv + 8) ↦ₘ optionalTag ∗
   (bv_unsigned sp + 1152) ↦ₘ optionalValue ∗
   (bv_unsigned sp + 1160) ↦ₘ optionalTag ∗
   (bv_unsigned sp + 1168) ↦ₘ data ∗ (bv_unsigned sp + 1176) ↦ₘ size ∗
   (bv_unsigned sp + 1000) ↦ₘ root ∗ bv_unsigned data ↦ₘ∗ bytes ∗
   ⌜bv_unsigned size = length bytes⌝ ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗
   ((⌜bv_extract 0 8 optionalTag = BV 8 0⌝ ∗
      spec_trace (writeOutputEventsAny (sp - BV 64 9)%bv (BV 64 1)
        (writeSuccessPostWithdrawalsRemainingEvents sp data size tail))) ∨
    (⌜bv_extract 0 8 optionalTag <> BV 8 0⌝ ∗
      spec_trace (writeOutputEventsAny (sp - BV 64 25)%bv (BV 64 1)
        (writeOutputEventsAny (sp - BV 64 16)%bv (BV 64 8)
          (writeSuccessPostWithdrawalsRemainingEvents sp data size tail))))) ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 48⌝ ∗
   ⌜bv_unsigned sp < (machineRamEnd defaultMap)⌝ ∗
   ⌜bv_unsigned sp + 1896 < (machineRamEnd defaultMap)⌝ ∗ P ∗ True)%I.

Global Instance : LithiumUnfold
    (@writeSuccessPostWithdrawals15700State) := I.
Global Instance : LithiumUnfold
    (@writeSuccessPostWithdrawals15718State) := I.

Definition writeSuccessPostWithdrawals1571cState
    `{!islaG Sigma} `{!threadG}
    (sp optionalValue optionalTag data size root : bv 64)
    (bytes : list (bv 8)) (saved : list (bv 64)) (tail : spec)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
     (["x1"; "x12"; "x13"; "x14"; "x15"; "x16"; "x17"] ++
      tmp_registers)) ∗
   reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
     ["x3"; "x4"]) ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   "x10" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
   "x11" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
   reg_col (zip_with (fun register (value : bv 64) =>
     (KindReg register, ExactShape (RVal_Bits value)))
     writeSuccessPostWithdrawalsSaved saved) ∗
   ⌜length saved = length writeSuccessPostWithdrawalsSaved⌝ ∗
   (bv_unsigned sp - 48) ↦ₘ? 48 ∗
   bv_unsigned (sp + BV 64 1624)%bv ↦ₘ optionalValue ∗
   (bv_unsigned (sp + BV 64 1624)%bv + 8) ↦ₘ optionalTag ∗
   (bv_unsigned sp + 1152) ↦ₘ optionalValue ∗
   (bv_unsigned sp + 1160) ↦ₘ optionalTag ∗
   (bv_unsigned sp + 1168) ↦ₘ data ∗ (bv_unsigned sp + 1176) ↦ₘ size ∗
   (bv_unsigned sp + 1000) ↦ₘ root ∗ bv_unsigned data ↦ₘ∗ bytes ∗
   ⌜bv_unsigned size = length bytes⌝ ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace (writeSuccessPostWithdrawalsRemainingEvents sp data size tail) ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 48⌝ ∗
   ⌜bv_unsigned sp < (machineRamEnd defaultMap)⌝ ∗
   ⌜bv_unsigned sp + 1896 < (machineRamEnd defaultMap)⌝ ∗ P ∗ True)%I.

Global Instance : LithiumUnfold
    (@writeSuccessPostWithdrawals1571cState) := I.

Definition writeSuccessPostWithdrawalsCallFrame
    `{!islaG Sigma} `{!threadG}
    (sp optionalValue optionalTag data size root : bv 64)
    (bytes : list (bv 8)) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
     ["x3"; "x4"]) ∗
   (bv_unsigned sp - 48) ↦ₘ? 16 ∗
   (bv_unsigned sp + 1152) ↦ₘ optionalValue ∗
   (bv_unsigned sp + 1160) ↦ₘ optionalTag ∗
   (bv_unsigned sp + 1168) ↦ₘ data ∗
   (bv_unsigned sp + 1176) ↦ₘ size ∗
   (bv_unsigned sp + 1000) ↦ₘ root ∗ bv_unsigned data ↦ₘ∗ bytes ∗
   ⌜bv_unsigned size = length bytes⌝ ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 48⌝ ∗
   ⌜bv_unsigned sp < (machineRamEnd defaultMap)⌝ ∗
   ⌜bv_unsigned sp + 1896 < (machineRamEnd defaultMap)⌝ ∗ P ∗ True)%I.

Global Instance : LithiumUnfold
    (@writeSuccessPostWithdrawalsCallFrame) := I.

Lemma post_withdrawals_optional_return `{!islaG Sigma} `{!threadG}
    (sp optionalValue optionalTag data size root : bv 64)
    (bytes : list (bv 8)) (tail : spec) (P : iProp Sigma) :
  instr_pre' false 0x1571c (writeSuccessPostWithdrawalsAt1571c P) -∗
  ∀ b8 b9 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27,
    instr_pre 0x1571c
      (writeSuccessSuffixOptionalU64159b8Return
        (BV 64 0x1571c) sp (sp + BV 64 1624)%bv optionalValue optionalTag
        (writeSuccessPostWithdrawalsRemainingEvents sp data size tail)
        b8 b9 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 ∗
       writeSuccessPostWithdrawalsCallFrame
         sp optionalValue optionalTag data size root bytes tail P).
Proof.
  iIntros "Hnext" (b8 b9 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27).
  iApply instr_pre_to_body. iNext.
  iApply (instr_pre_wand 0x1571c 0x1571c false false with "Hnext");
    [done | reflexivity |].
  iIntros "(Hreturn & Hframe)".
  iEval (unfold writeSuccessSuffixOptionalU64159b8Return, zesu_c_call_ret)
    in "Hreturn".
  iDestruct "Hreturn" as "(Hsys & Hcaller & Hsaved & Hrest)".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "Hrest".
  iDestruct "Hrest" as (r10) "(H10 & Hrest)".
  iDestruct "Hrest" as (b10) "(%Hr10 & Hrest)".
  iDestruct "Hrest" as (r11) "(H11 & Hrest)".
  iDestruct "Hrest" as (b11)
    "(%Hr11 & H2 & Hstack32 & Hresources)".
  subst r10 r11.
  iAssert ("x10" ↦ᵣ: (fun value =>
      ⌜valu_has_shape value (BitsShape 64)⌝))%I
    with "[H10]" as "H10bits".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists (RVal_Bits b10). iFrame. iPureIntro. cbn. done. }
  iAssert ("x11" ↦ᵣ: (fun value =>
      ⌜valu_has_shape value (BitsShape 64)⌝))%I
    with "[H11]" as "H11bits".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists (RVal_Bits b11). iFrame. iPureIntro. cbn. done. }
  iDestruct "Hresources" as
    "(HscratchValue & HscratchTag & Hmmio & Htrace & _)".
  iEval (unfold writeSuccessPostWithdrawalsCallFrame) in "Hframe".
  iDestruct "Hframe" as
    "(Hextra & Hstack16 & HsourceValue & HsourceTag & HdataSlot &
      HsizeSlot & Hroot & Hbytes & %HbytesLength & %Halign & %Hlower &
      %Hupper & %HframeUpper & HP & _)".
  iAssert ((bv_unsigned sp - 48) ↦ₘ? 48)%I
    with "[Hstack16 Hstack32]" as "Hstack".
  { iApply (mem_mapsto_uninit_combine 16 with "Hstack16"); first lia.
    have -> : bv_unsigned sp - 48 + 16 = bv_unsigned sp - 32 by lia.
    iExact "Hstack32". }
  iAssert (bv_unsigned (sp + BV 64 1624)%bv ↦ₘ optionalValue)%I
    with "[HscratchValue]" as "HscratchValue".
  { iExact "HscratchValue". }
  rewrite /writeSuccessPostWithdrawalsAt1571c.
  iExists sp, optionalValue, optionalTag, data, size, root, bytes,
    [b8; b9; b18; b19; b20; b21; b22; b23; b24; b25; b26; b27], tail.
  iFrame "Hsys Hcaller H2 H10bits H11bits Hsaved Hstack HscratchValue HscratchTag
    HsourceValue HsourceTag HdataSlot HsizeSlot Hroot Hbytes Hmmio Htrace HP
    Hextra".
  repeat iSplit; try iPureIntro; try assumption; try reflexivity; try lia.
Qed.

Lemma block_15700 `{!islaG Sigma} `{!threadG}
    (sp optionalValue optionalTag data size root : bv 64)
    (bytes : list (bv 8)) (saved : list (bv 64)) (tail : spec)
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x15718
    (writeSuccessPostWithdrawals15718State sp optionalValue optionalTag
      data size root bytes saved tail P) -∗
  instr_body 0x15700
    (writeSuccessPostWithdrawals15700State sp optionalValue optionalTag
      data size root bytes saved tail P).
Proof.
  move => *.
  iStartProof. iIntros "_ #Hlookup #Hcode Hnext".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  liARun.
  Unshelve.
  all: try zesu_finish.
  all: lazymatch goal with |- ?G => fail "block_15700 residual" G end.
Qed.

Print Assumptions block_15700.

Ltac open_post_withdrawals_saved saved HsavedLength :=
  destruct saved as [|s8 saved]; cbn in HsavedLength; try lia;
  destruct saved as [|s9 saved]; cbn in HsavedLength; try lia;
  destruct saved as [|s18 saved]; cbn in HsavedLength; try lia;
  destruct saved as [|s19 saved]; cbn in HsavedLength; try lia;
  destruct saved as [|s20 saved]; cbn in HsavedLength; try lia;
  destruct saved as [|s21 saved]; cbn in HsavedLength; try lia;
  destruct saved as [|s22 saved]; cbn in HsavedLength; try lia;
  destruct saved as [|s23 saved]; cbn in HsavedLength; try lia;
  destruct saved as [|s24 saved]; cbn in HsavedLength; try lia;
  destruct saved as [|s25 saved]; cbn in HsavedLength; try lia;
  destruct saved as [|s26 saved]; cbn in HsavedLength; try lia;
  destruct saved as [|s27 saved]; cbn in HsavedLength; try lia;
  destruct saved; cbn in HsavedLength; try lia.

Lemma post_withdrawals_saved_bits `{!islaG Sigma} `{!threadG}
    (saved : list (bv 64)) :
  ⌜length saved = length writeSuccessPostWithdrawalsSaved⌝ -∗
  reg_col (zip_with (fun register (value : bv 64) =>
    (KindReg register, ExactShape (RVal_Bits value)))
    writeSuccessPostWithdrawalsSaved saved) -∗
  ("x8" ↦ᵣ: (fun v => ⌜valu_has_shape v (BitsShape 64)⌝) ∗
   "x9" ↦ᵣ: (fun v => ⌜valu_has_shape v (BitsShape 64)⌝) ∗
   "x18" ↦ᵣ: (fun v => ⌜valu_has_shape v (BitsShape 64)⌝) ∗
   "x19" ↦ᵣ: (fun v => ⌜valu_has_shape v (BitsShape 64)⌝) ∗
   "x20" ↦ᵣ: (fun v => ⌜valu_has_shape v (BitsShape 64)⌝) ∗
   "x21" ↦ᵣ: (fun v => ⌜valu_has_shape v (BitsShape 64)⌝) ∗
   "x22" ↦ᵣ: (fun v => ⌜valu_has_shape v (BitsShape 64)⌝) ∗
   "x23" ↦ᵣ: (fun v => ⌜valu_has_shape v (BitsShape 64)⌝) ∗
   "x24" ↦ᵣ: (fun v => ⌜valu_has_shape v (BitsShape 64)⌝) ∗
   "x25" ↦ᵣ: (fun v => ⌜valu_has_shape v (BitsShape 64)⌝) ∗
   "x26" ↦ᵣ: (fun v => ⌜valu_has_shape v (BitsShape 64)⌝) ∗
   "x27" ↦ᵣ: (fun v => ⌜valu_has_shape v (BitsShape 64)⌝) ∗ True)%I.
Proof.
  iIntros "%HsavedLength Hsaved".
  open_post_withdrawals_saved saved HsavedLength.
  iEval (rewrite !reg_col_cons reg_col_nil) in "Hsaved".
  iDestruct "Hsaved" as
    "((%v8 & %Hv8 & H8) & (%v9 & %Hv9 & H9) &
      (%v18 & %Hv18 & H18) & (%v19 & %Hv19 & H19) &
      (%v20 & %Hv20 & H20) & (%v21 & %Hv21 & H21) &
      (%v22 & %Hv22 & H22) & (%v23 & %Hv23 & H23) &
      (%v24 & %Hv24 & H24) & (%v25 & %Hv25 & H25) &
      (%v26 & %Hv26 & H26) & (%v27 & %Hv27 & H27) & _)".
  cbn in Hv8, Hv9, Hv18, Hv19, Hv20, Hv21, Hv22, Hv23, Hv24, Hv25,
    Hv26, Hv27.
  subst v8; subst v9; subst v18; subst v19; subst v20; subst v21.
  subst v22; subst v23; subst v24; subst v25; subst v26; subst v27.
  iSplitL "H8"; first (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def;
    iExists _; iFrame; iPureIntro; cbn; done).
  iSplitL "H9"; first (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def;
    iExists _; iFrame; iPureIntro; cbn; done).
  iSplitL "H18"; first (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def;
    iExists _; iFrame; iPureIntro; cbn; done).
  iSplitL "H19"; first (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def;
    iExists _; iFrame; iPureIntro; cbn; done).
  iSplitL "H20"; first (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def;
    iExists _; iFrame; iPureIntro; cbn; done).
  iSplitL "H21"; first (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def;
    iExists _; iFrame; iPureIntro; cbn; done).
  iSplitL "H22"; first (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def;
    iExists _; iFrame; iPureIntro; cbn; done).
  iSplitL "H23"; first (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def;
    iExists _; iFrame; iPureIntro; cbn; done).
  iSplitL "H24"; first (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def;
    iExists _; iFrame; iPureIntro; cbn; done).
  iSplitL "H25"; first (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def;
    iExists _; iFrame; iPureIntro; cbn; done).
  iSplitL "H26"; first (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def;
    iExists _; iFrame; iPureIntro; cbn; done).
  iSplitL "H27"; first (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def;
    iExists _; iFrame; iPureIntro; cbn; done).
  done.
Qed.

Ltac apply_post_withdrawals_optional_call :=
  iApply "Hjalr";
  rewrite /InstrSpecs.Specs.zesu_jalr_same_spec;
  iExists (BV 64 0x15714); iFrame "Hsys H1";
  iSplit; first (iPureIntro; bv_solve);
  replace
    (bv_unsigned
      (bv_or (bv_and ((BV 64 0x15714) + BV 64 1204)%bv
        (BV 64 18446744073709551614)) (BV 64 0)))
    with 0x15bc8 by bv_solve;
  iEval (rewrite -instr_pre'_eq) in "Hoptional";
  iApply (instr_pre_wand 0x15bc8 0x15bc8 true true with "Hoptional");
    [done | reflexivity |];
  iIntros "Hcall".

Definition writeSuccessPostWithdrawalsOptionalReady
    `{!islaG Sigma} `{!threadG}
    (sp optionalValue optionalTag data size root : bv 64)
    (bytes : list (bv 8)) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x1" ↦ᵣ RVal_Bits (BV 64 0x15714) ∗
   (writeSuccessSuffixOptionalU64159b8NoneFrame
      (writeSuccessPostWithdrawalsCallFrame
        sp optionalValue optionalTag data size root bytes tail P)
      (BV 64 0x1571c) sp (sp + BV 64 1624)%bv optionalValue optionalTag
      (writeSuccessPostWithdrawalsRemainingEvents sp data size tail) ∨
    writeSuccessSuffixOptionalU64159b8SomeFrame
      (writeSuccessPostWithdrawalsCallFrame
        sp optionalValue optionalTag data size root bytes tail P)
      (BV 64 0x1571c) sp (sp + BV 64 1624)%bv optionalValue optionalTag
      (writeSuccessPostWithdrawalsRemainingEvents sp data size tail)))%I.

Global Instance : LithiumUnfold
    (@writeSuccessPostWithdrawalsOptionalReady) := I.

Lemma post_withdrawals_optional_prepare `{!islaG Sigma} `{!threadG}
    (sp optionalValue optionalTag data size root : bv 64)
    (bytes : list (bv 8)) (saved : list (bv 64)) (tail : spec)
    (P : iProp Sigma) :
  writeSuccessPostWithdrawals15718State sp optionalValue optionalTag
    data size root bytes saved tail P -∗
  (∀ b8 b9 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27,
    instr_pre 0x1571c
      (writeSuccessSuffixOptionalU64159b8Return
        (BV 64 0x1571c) sp (sp + BV 64 1624)%bv optionalValue optionalTag
        (writeSuccessPostWithdrawalsRemainingEvents sp data size tail)
        b8 b9 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 ∗
       writeSuccessPostWithdrawalsCallFrame
        sp optionalValue optionalTag data size root bytes tail P)) -∗
  writeSuccessPostWithdrawalsOptionalReady
    sp optionalValue optionalTag data size root bytes tail P.
Proof.
  iIntros "Hentry Hret".
  iEval (rewrite /writeSuccessPostWithdrawals15718State) in "Hentry".
  iDestruct "Hentry" as
    "(Hsys & H1 & H2 & H5 & H10 & H11 & Hvolatile & Hsaved & %HsavedLength &
      Hstack & HscratchValue & HscratchTag & HsourceValue & HsourceTag &
      HdataSlot & HsizeSlot & Hroot & Hbytes & %HbytesLength & Hmmio &
      Hbranch & %Halign & %Hlower & %Hupper & %HframeUpper & HP & _)".
  iPoseProof (post_withdrawals_saved_bits saved with "[] Hsaved")
    as "HsavedBits"; first (iPureIntro; exact HsavedLength).
  iEval (rewrite /writeSuccessPostWithdrawalsVolatile /reg_col; cbn)
    in "Hvolatile".
  iDestruct "Hvolatile" as
    "(H3 & H4 & H6 & H7 & H12raw & H13raw & H14raw & H15raw & H16raw &
      H17raw & H28 & H29 & H30 & H31 & _)".
  iDestruct "H12raw" as (v12) "(%Hv12 & H12map)".
  iDestruct "H13raw" as (v13) "(%Hv13 & H13map)".
  iDestruct "H14raw" as (v14) "(%Hv14 & H14map)".
  iDestruct "H15raw" as (v15) "(%Hv15 & H15map)".
  iDestruct "H16raw" as (v16) "(%Hv16 & H16map)".
  iDestruct "H17raw" as (v17) "(%Hv17 & H17map)".
  iAssert ("x12" ↦ᵣ: (fun v => ⌜valu_has_shape v (BitsShape 64)⌝))%I
    with "[H12map]" as "H12"; first (rewrite reg_mapsto_pred_eq
      /reg_mapsto_pred_def; iExists v12; iFrame; iPureIntro; exact Hv12).
  iAssert ("x13" ↦ᵣ: (fun v => ⌜valu_has_shape v (BitsShape 64)⌝))%I
    with "[H13map]" as "H13".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists v13. iFrame. iPureIntro. exact Hv13. }
  iAssert ("x14" ↦ᵣ: (fun v => ⌜valu_has_shape v (BitsShape 64)⌝))%I
    with "[H14map]" as "H14".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists v14. iFrame. iPureIntro. exact Hv14. }
  iAssert ("x15" ↦ᵣ: (fun v => ⌜valu_has_shape v (BitsShape 64)⌝))%I
    with "[H15map]" as "H15".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists v15. iFrame. iPureIntro. exact Hv15. }
  iAssert ("x16" ↦ᵣ: (fun v => ⌜valu_has_shape v (BitsShape 64)⌝))%I
    with "[H16map]" as "H16".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists v16. iFrame. iPureIntro. exact Hv16. }
  iAssert ("x17" ↦ᵣ: (fun v => ⌜valu_has_shape v (BitsShape 64)⌝))%I
    with "[H17map]" as "H17".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists v17. iFrame. iPureIntro. exact Hv17. }
  iDestruct "HsavedBits" as
    "(H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 &
      H27 & _)".
  iAssert ("x5" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝))%I
    with "[H5]" as "H5bits".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists (RVal_Bits (BV 64 (mapIoContextAddress defaultMap))). iFrame. iPureIntro. cbn. done. }
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "H5bits".
  iDestruct "H5bits" as (v5) "(H5map & %Hv5)".
  iAssert (reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
      tmp_registers))%I with "[H5map H6 H7 H28 H29 H30 H31]" as "Htmp".
  { rewrite /tmp_registers !reg_col_cons reg_col_nil.
    iSplitL "H5map"; first (iExists v5; iFrame; iPureIntro; exact Hv5).
    iFrame. }
  iAssert (reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
      ["x3"; "x4"]))%I with "[H3 H4]" as "Hextra".
  { rewrite !reg_col_cons reg_col_nil. iFrame. }
  iDestruct (mem_mapsto_uninit_split 16 with "Hstack") as
    "[Hstack16 Hstack32]"; first lia.
  have HstackAddress : bv_unsigned sp - 48 + 16 = bv_unsigned sp - 32 by lia.
  iEval (rewrite HstackAddress) in "Hstack32".
  iAssert (writeSuccessPostWithdrawalsCallFrame
      sp optionalValue optionalTag data size root bytes tail P)%I
    with "[Hextra Hstack16 HsourceValue HsourceTag HdataSlot HsizeSlot Hroot
      Hbytes HP]" as "HframeQ".
  { rewrite /writeSuccessPostWithdrawalsCallFrame. iFrame.
    repeat iSplit; try iPureIntro; try assumption. }
  iAssert ("x11" ↦ᵣ: (fun value =>
      ⌜valu_has_shape value (BitsShape 64)⌝))%I with "[H11]" as "H11bits".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists (RVal_Bits optionalTag). iFrame. iPureIntro. cbn. done. }
  rewrite /writeSuccessPostWithdrawalsOptionalReady.
  iFrame "Hsys H1".
  iDestruct "Hbranch" as "[Hnone|Hsome]".
  - iLeft. iDestruct "Hnone" as "[%Htag Htrace]".
    rewrite /writeSuccessSuffixOptionalU64159b8NoneFrame. iFrame.
    repeat iSplit; try iPureIntro; try assumption; try bv_solve; try lia.
  - iRight. iDestruct "Hsome" as "[%Htag Htrace]".
    rewrite /writeSuccessSuffixOptionalU64159b8SomeFrame. iFrame.
    repeat iSplit; try iPureIntro; try assumption; try bv_solve; try lia.
Qed.

Lemma block_15718 `{!islaG Sigma} `{!threadG}
    (sp optionalValue optionalTag data size root : bv 64)
    (bytes : list (bv 8)) (saved : list (bv 64)) (tail : spec)
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  □ instr_pre 0x15bc8 zesuEncoderOptionalU64CallSpec -∗
  instr_body 0x1571c (writeSuccessPostWithdrawalsAt1571c P) -∗
  instr_body 0x15718
    (writeSuccessPostWithdrawals15718State sp optionalValue optionalTag
      data size root bytes saved tail P).
Proof.
  iStartProof. iIntros "#Hlookup #Hoptional Hnext".
  iPoseProof "Hlookup" as "#Hlookup15718".
  iEval (rewrite /instr_lookup_resources) in "Hlookup15718".
  iPoseProof ("Hlookup15718" $! 0x15718 with "[]") as "#Hinstr15718".
  { iPureIntro. rewrite IslaTraces.write_success_blocks.Index.lookup_a15718.
    done. }
  iPoseProof (IslaTraces.write_success_98.a15718_spec.a15718_spec
    0x15718 with "Hinstr15718") as "Hjalr".
  rewrite instr_pre'_eq. iIntros "Hentry".
  iEval (rewrite -instr_pre'_eq) in "Hnext".
  iPoseProof (post_withdrawals_optional_return sp optionalValue optionalTag
    data size root bytes tail P with "Hnext") as "Hret".
  iPoseProof (post_withdrawals_optional_prepare sp optionalValue optionalTag
    data size root bytes saved tail P with "Hentry Hret") as "Hready".
  iEval (unfold writeSuccessPostWithdrawalsOptionalReady) in "Hready".
  iDestruct "Hready" as "(Hsys & H1 & [Hnone|Hsome])".
  - apply_post_withdrawals_optional_call.
    iApply (write_success_suffix_optional_u64_159b8_none_assembly
      (writeSuccessPostWithdrawalsCallFrame
        sp optionalValue optionalTag data size root bytes tail P)
      (BV 64 0x1571c) sp (sp + BV 64 1624)%bv optionalValue optionalTag
      (writeSuccessPostWithdrawalsRemainingEvents sp data size tail) with "Hcall Hnone").
  - apply_post_withdrawals_optional_call.
    iApply (write_success_suffix_optional_u64_159b8_some_assembly
      (writeSuccessPostWithdrawalsCallFrame
        sp optionalValue optionalTag data size root bytes tail P)
      (BV 64 0x1571c) sp (sp + BV 64 1624)%bv optionalValue optionalTag
      (writeSuccessPostWithdrawalsRemainingEvents sp data size tail) with "Hcall Hsome").
  Unshelve. all: try zesu_finish.
  all: lazymatch goal with |- ?G => fail "block_15718 residual" G end.
Qed.

Print Assumptions block_15718.
