Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessByteLists.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCallAbi.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPost1566c.

Import ListNotations.

Definition writeSuccessTransactionsPost15674Saved : list string :=
  ["x8"; "x9"; "x18"; "x19"; "x20"; "x21";
   "x22"; "x23"; "x24"; "x25"; "x26"; "x27"].

Definition writeSuccessTransactionsPost15674Caller : list string :=
  ["x1"; "x12"; "x13"; "x14"; "x15"; "x16"; "x17";
   "x5"; "x6"; "x7"; "x28"; "x29"; "x30"; "x31"].

Definition writeSuccessTransactionsPost15674ReturnOther : list string :=
  ["x3"; "x4"].

Definition writeSuccessTransactionsPost15674ByteListFacts
    (sp first second : bv 64) (items : list ByteListItem) : Prop :=
  bv_unsigned second = length items /\
  length items < 2 ^ 64 /\
  bv_extract 0 3 first = BV 3 0 /\
  (mapRamBase defaultMap) <= bv_unsigned first /\
  bv_unsigned first + 16 * Z.of_nat (length items) < (machineRamEnd defaultMap) /\
  bv_extract 0 4 sp = BV 4 0 /\
  (mapRamBase defaultMap) <= bv_unsigned sp - 80 /\
  bv_unsigned sp < (machineRamEnd defaultMap).

Definition writeSuccessTransactionsPost15674CallRet
    `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (saved : list valu) (first second : bv 64)
    (items : list ByteListItem) (tail : spec) : iProp Sigma :=
  zesu_c_call_ret 80 saved (BV 64 0x15678) sp
    (fun _ =>
      byteListItemResources (bv_unsigned first) items ∗
      mmio_range (machineOutputAddress defaultMap) 16 ∗ spec_trace tail ∗ True)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsPost15674CallRet) := I.

Definition writeSuccessTransactionsPost15674CallRegisters : list string :=
  ["x12"; "x13"; "x14"; "x15"; "x16"; "x17";
   "x5"; "x6"; "x7"; "x28"; "x29"; "x30"; "x31"].

Definition writeSuccessTransactionsPost15674CallEntrySpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (transactions : list writeSuccessTransaction)
      (bytes : list (bv 8)) (tail : spec) (first second : bv 64)
      (items : list ByteListItem) (saved : list valu),
    reg_col zesu_ram_sys_regs ∗
    reg_col ((fun r => (KindReg r, BitsShape 64)) <$>
      writeSuccessTransactionsPost15674CallRegisters) ∗
    reg_col (zip_with (fun r v => (KindReg r, ExactShape v))
      writeSuccessTransactionsPost15674Saved saved) ∗
    ⌜length saved = 12%nat⌝ ∗
    ⌜Forall (fun v => valu_has_shape v (BitsShape 64)) saved⌝ ∗
    reg_col ((fun r => (KindReg r, BitsShape 64)) <$>
      writeSuccessTransactionsPost15674ReturnOther) ∗
    "x1" ↦ᵣ RVal_Bits (BV 64 0x15670) ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x10" ↦ᵣ RVal_Bits first ∗
    "x11" ↦ᵣ RVal_Bits second ∗
    (bv_unsigned sp - 80) ↦ₘ? 80 ∗
    (bv_unsigned sp) ↦ₘ? 104 ∗
    (bv_unsigned sp + 104) ↦ₘ Z_to_bv 64 base ∗
    (bv_unsigned sp + 112) ↦ₘ Z_to_bv 64 (Z.of_nat (length transactions)) ∗
    (bv_unsigned sp + 120) ↦ₘ? 984 ∗
    (bv_unsigned sp + 1104) ↦ₘ first ∗
    (bv_unsigned sp + 1112) ↦ₘ second ∗
    (bv_unsigned sp + 1120) ↦ₘ? 776 ∗
    base ↦ₘ∗ bytes ∗ writeSuccessTransactionsOwn transactions ∗
    byteListItemResources (bv_unsigned first) items ∗
    ⌜writeSuccessTransactionsPost15674ByteListFacts sp first second items⌝ ∗
    ⌜bv_unsigned sp + 1896 < (machineRamEnd defaultMap)⌝ ∗
    mmio_range (machineOutputAddress defaultMap) 16 ∗
    spec_trace
      (writeOutputEventsAny (sp - BV 64 48)%bv (BV 64 8)
        (byteListItemEvents (sp - BV 64 32)%bv items tail)) ∗
    P ∗ True)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsPost15674CallEntrySpec) := I.

Definition writeSuccessTransactionsPost15678Spec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (transactions : list writeSuccessTransaction)
      (bytes : list (bv 8)) (tail : spec) (first second : bv 64)
      (items : list ByteListItem) (saved : list valu)
      (r10 r11 : bv 64),
    reg_col zesu_ram_sys_regs ∗
    reg_col ((fun r => (KindReg r, BitsShape 64)) <$>
      writeSuccessTransactionsPost15674Caller) ∗
    reg_col (zip_with (fun r v => (KindReg r, ExactShape v))
      writeSuccessTransactionsPost15674Saved saved) ∗
    ⌜length saved = 12%nat⌝ ∗
    reg_col ((fun r => (KindReg r, BitsShape 64)) <$>
      writeSuccessTransactionsPost15674ReturnOther) ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x10" ↦ᵣ RVal_Bits r10 ∗
    "x11" ↦ᵣ RVal_Bits r11 ∗
    writeSuccessTransactionsPostScratch15670 sp base (length transactions)
      first second ∗
    base ↦ₘ∗ bytes ∗ writeSuccessTransactionsOwn transactions ∗
    byteListItemResources (bv_unsigned first) items ∗
    ⌜writeSuccessTransactionsPost15674ByteListFacts sp first second items⌝ ∗
    ⌜bv_unsigned sp + 1896 < (machineRamEnd defaultMap)⌝ ∗
    mmio_range (machineOutputAddress defaultMap) 16 ∗
    spec_trace tail ∗
    P ∗ True)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsPost15678Spec) := I.

Definition writeSuccessTransactionsPost15674ReturnFrame
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transactions : list writeSuccessTransaction)
    (bytes : list (bv 8)) (tail : spec) (first second : bv 64)
    (items : list ByteListItem) (saved : list valu) : iProp Sigma :=
  (reg_col ((fun r => (KindReg r, BitsShape 64)) <$>
      writeSuccessTransactionsPost15674ReturnOther) ∗
   base ↦ₘ∗ bytes ∗ writeSuccessTransactionsOwn transactions ∗
   ⌜length saved = 12%nat⌝ ∗
   ⌜writeSuccessTransactionsPost15674ByteListFacts sp first second items⌝ ∗
   ⌜bv_unsigned sp + 1896 < (machineRamEnd defaultMap)⌝ ∗
   P ∗ True ∗
   ((bv_unsigned sp - 48) ↦ₘ? 48 -∗
      writeSuccessTransactionsPostScratch15670 sp base (length transactions)
        first second))%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsPost15674ReturnFrame) := I.

Lemma write_success_transactions_post_15674_return_adapter
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transactions : list writeSuccessTransaction)
    (bytes : list (bv 8)) (tail : spec) (first second : bv 64)
    (items : list ByteListItem) (saved : list valu) :
  writeSuccessTransactionsPost15674CallRet sp saved first second items tail -∗
  writeSuccessTransactionsPost15674ReturnFrame P sp base transactions bytes
    tail first second items saved -∗
  writeSuccessTransactionsPost15678Spec P.
Proof.
  iStartProof. iIntros "Hpost Hframe".
  iEval (unfold writeSuccessTransactionsPost15674CallRet,
    zesu_c_call_ret) in "Hpost".
  iDestruct "Hpost" as "(Hsys & Hcaller & Hsaved & Hrest)".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "Hrest".
  iDestruct "Hrest" as (r10) "(H10 & Hrest)".
  iDestruct "Hrest" as (b10) "(%Hr10 & Hrest)". subst r10.
  iDestruct "Hrest" as (r11) "(H11 & Hrest)".
  iDestruct "Hrest" as (b11) "(%Hr11 & Hrest)". subst r11.
  iDestruct "Hrest" as "(H2 & Hstack & Hitems & Hmmio & Htrace & _)".
  iEval (unfold writeSuccessTransactionsPost15674ReturnFrame) in "Hframe".
  iDestruct "Hframe" as
    "(HreturnOther & Hbase & Hown & HsavedLength & Hfacts & HspUpper & HP & _ &
      HscratchFrame)".
  iDestruct (mem_mapsto_uninit_split 32 with "Hstack") as
    "(_ & Hstack48)"; first lia.
  have HstackAddress : bv_unsigned sp - 80 + 32 = bv_unsigned sp - 48 by lia.
  iEval (rewrite HstackAddress) in "Hstack48".
  iPoseProof ("HscratchFrame" with "Hstack48") as "HscratchFull".
  iExists sp, base, transactions, bytes, tail, first, second, items, saved.
  iFrame "Hsys Hcaller Hsaved HreturnOther H2 H10 H11 HscratchFull Hbase Hown
    Hitems HsavedLength Hfacts HspUpper Hmmio Htrace HP".
Qed.
