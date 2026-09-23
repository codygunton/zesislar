Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderBytesCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeSuffixRoot.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPostWithdrawalsOptional.

Import ListNotations.

Definition writeSuccessPostWithdrawalsCallRegisters : list string :=
  ["x3"; "x4"; "x7"; "x12"; "x13"; "x14"; "x15";
   "x16"; "x17"; "x28"; "x29"; "x30"; "x31"].

Definition writeSuccessPostWithdrawalsAt15728
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp optionalValue optionalTag data size root : bv 64)
      (bytes : list (bv 8)) (saved : list (bv 64)) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits (BV 64 0x15724) ∗ "x2" ↦ᵣ RVal_Bits sp ∗
    "x5" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    "x6" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    "x10" ↦ᵣ RVal_Bits data ∗ "x11" ↦ᵣ RVal_Bits size ∗
    reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
      writeSuccessPostWithdrawalsCallRegisters) ∗
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
    (bv_unsigned sp + 1000) ↦ₘ root ∗ bv_unsigned data ↦ₘ∗ bytes ∗
    ⌜bv_unsigned size = length bytes⌝ ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗
    spec_trace (writeSuccessPostWithdrawalsRemainingEvents sp data size tail) ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 48⌝ ∗
    ⌜bv_unsigned sp < (machineRamEnd defaultMap)⌝ ∗
    ⌜bv_unsigned sp + 1896 < (machineRamEnd defaultMap)⌝ ∗ P ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessPostWithdrawalsAt15728) := I.

Definition writeSuccessPostWithdrawals15728State
    `{!islaG Sigma} `{!threadG}
    (sp optionalValue optionalTag data size root : bv 64)
    (bytes : list (bv 8)) (saved : list (bv 64)) (tail : spec)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits (BV 64 0x15724) ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x5" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
   "x6" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
   "x10" ↦ᵣ RVal_Bits data ∗ "x11" ↦ᵣ RVal_Bits size ∗
   reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
     writeSuccessPostWithdrawalsCallRegisters) ∗
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
    (@writeSuccessPostWithdrawals15728State) := I.

Lemma block_1571c `{!islaG Sigma} `{!threadG}
    (sp optionalValue optionalTag data size root : bv 64)
    (bytes : list (bv 8)) (saved : list (bv 64)) (tail : spec)
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x15728 (writeSuccessPostWithdrawals15728State sp optionalValue
    optionalTag data size root bytes saved tail P) -∗
  instr_body 0x1571c (writeSuccessPostWithdrawals1571cState sp optionalValue
    optionalTag data size root bytes saved tail P).
Proof. move => *. zesu_block. Qed.

Print Assumptions block_1571c.

Definition writeSuccessPostWithdrawalsAt1572cState
    `{!islaG Sigma} `{!threadG}
    (sp optionalValue optionalTag data size root : bv 64)
    (bytes : list (bv 8)) (saved : list (bv 64)) (tail : spec)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits (BV 64 0x1572c) ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x5" ↦ᵣ RVal_Bits (BV 64 (mapIoContextAddress defaultMap)) ∗
   "x6" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
   "x10" ↦ᵣ RVal_Bits data ∗ "x11" ↦ᵣ RVal_Bits size ∗
   reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
     ["x3"; "x4"; "x7"; "x12"; "x13"; "x14"; "x15"; "x16"; "x17";
      "x28"; "x29"; "x30"; "x31"]) ∗
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
   mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace (writeOutputEventsAny (sp + BV 64 1000)%bv (BV 64 32) tail) ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 48⌝ ∗
   ⌜bv_unsigned sp < (machineRamEnd defaultMap)⌝ ∗
   ⌜bv_unsigned sp + 1896 < (machineRamEnd defaultMap)⌝ ∗ P ∗ True)%I.

Global Instance : LithiumUnfold
    (@writeSuccessPostWithdrawalsAt1572cState) := I.

Ltac prepare_post_withdrawals_bytes_call sp data size bytes tail
    s8 s9 s18 s19 s20 s21 s22 s23 s24 s25 s26 s27 :=
  try iRename select
    (reg_col (zip_with (fun register (value : bv 64) =>
      (KindReg register, ExactShape (RVal_Bits value)))
      writeSuccessPostWithdrawalsSaved
      [s8; s9; s18; s19; s20; s21; s22; s23; s24; s25; s26; s27]))
    into "Hsaved";
  try iEval (cbn) in "Hsaved";
  try iDestruct "Hsaved" as
    "(H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27 & _)";
  iRename select (mmio_range _ 16) into "Hmmio";
  try iRename select ("x2" ↦ᵣ RVal_Bits sp)%I into "H2";
  try iRename select ("x5" ↦ᵣ RVal_Bits _)%I into "H5";
  try iRename select ("x6" ↦ᵣ RVal_Bits _)%I into "H6";
  try iRename select ("x10" ↦ᵣ RVal_Bits data)%I into "H10";
  try iRename select ("x11" ↦ᵣ RVal_Bits size)%I into "H11";
  try iRename select ((bv_unsigned sp - 48) ↦ₘ? 48)%I into "Hstack";
  try iRename select (bv_unsigned data ↦ₘ∗ bytes)%I into "Hdata";
  try iRename select
    (spec_trace (writeSuccessPostWithdrawalsRemainingEvents sp data size tail))
    into "Htrace";
  repeat iDestruct select (_ ∗ _)%I as "(? & ?)";
  iExists
    (writeOutputEventsAny (sp + BV 64 1000)%bv (BV 64 32) tail,
      bytes, 0x1572c, s9, s8, sp, size, data, tt)ₗ;
  cbn;
  repeat iDestruct select (_ ∗ _)%I as "(? & ?)";
  iDestruct select
    (∃ value : valu, ⌜value = RVal_Bits s8⌝ ∗ "x8" ↦ᵣ value)%I
    as (value8) "(-> & H8)";
  iDestruct select
    (∃ value : valu, ⌜value = RVal_Bits s9⌝ ∗ "x9" ↦ᵣ value)%I
    as (value9) "(-> & H9)";
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def);
  iFrame "H2 H5 H6 H8 H9 H10 H11 Hstack Hdata Hmmio Htrace";
  repeat iSplit; try iPureIntro; try assumption; try lia; try bv_solve;
  try iAssumption; try iExact "Hmmio".

Lemma block_15728 `{!islaG Sigma} `{!threadG}
    (sp optionalValue optionalTag data size root : bv 64)
    (bytes : list (bv 8)) (saved : list (bv 64)) (tail : spec)
    (P : iProp Sigma)
    (HsavedLength : length saved = length writeSuccessPostWithdrawalsSaved) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  □ instr_pre 0x15c6c zesuEncoderBytesCallSpec -∗
  instr_body 0x1572c (writeSuccessPostWithdrawalsAt1572cState sp
    optionalValue optionalTag data size root bytes saved tail P) -∗
  instr_body 0x15728 (writeSuccessPostWithdrawals15728State sp
    optionalValue optionalTag data size root bytes saved tail P).
Proof.
  move => *.
  open_post_withdrawals_saved saved HsavedLength.
  iStartProof. iIntros "_ #Hlookup #Hbytes Hnext".
  iAssert (instr_pre 0x1572c (writeSuccessPostWithdrawalsAt1572cState sp
    optionalValue optionalTag data size root bytes
    [s8; s9; s18; s19; s20; s21; s22; s23; s24; s25; s26; s27]
    tail P))%I with "[Hnext]" as "HnextPre".
  { iApply instr_pre_to_body. iNext. iExact "Hnext". }
  liARun.
  Unshelve. all: try zesu_finish.
  Unshelve.
  all: prepare_post_withdrawals_bytes_call sp data size bytes tail
    s8 s9 s18 s19 s20 s21 s22 s23 s24 s25 s26 s27.
  iApply (instr_pre_wand 0x1572c 0x1572c true true with "HnextPre");
    [done | reflexivity |].
  iIntros "Hreturn".
  iEval (unfold writeSuccessPostWithdrawalsAt1572cState) in "Hreturn".
  iEval (simpl) in "Hreturn".
  iDestruct "Hreturn" as "(? & ?)".
  repeat iDestruct select (_ ∗ _)%I as "(? & ?)".
  iFrame.
  cbn.
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def).
  iFrame.
  repeat iSplit; try iPureIntro; try assumption; try lia; try bv_solve.
  all: try reflexivity.
  have HreturnAddress : Z_to_bv 64 87852 = BV 64 87852 by bv_solve.
  rewrite -HreturnAddress.
  iFrame.
Qed.

Print Assumptions block_15728.
