Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccess.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCallAbi.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCalls.

Import ListNotations.

Definition zesuEncoderU256SavedRegisters : list string :=
  ["x8"; "x9"; "x18"; "x19"; "x20"; "x21";
   "x22"; "x23"; "x24"; "x25"; "x26"; "x27"].

Definition zesuEncoderU256CallSpec `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (zesu_c_call 48
    (fun _ sp RET =>
      ∃ tail : spec,
      mmio_range 0x2401a0c0 16 ∗
      spec_trace
        (writeOutputEvents (sp - BV 64 48)%bv (BV 64 32) tail) ∗
      RET (fun _ =>
        mmio_range 0x2401a0c0 16 ∗ spec_trace tail ∗ True)))%I.

Global Instance : LithiumUnfold (@zesuEncoderU256CallSpec) := I.

Definition zesuEncoderU256CallerContinuation
    `{!islaG Sigma} `{!threadG}
    (sp ret : bv 64) (saved : list valu) (tail : spec) : iProp Sigma :=
  (instr_pre (bv_unsigned ret)
    (zesu_c_call_ret 48 saved ret sp
      (fun _ =>
        mmio_range 0x2401a0c0 16 ∗ spec_trace tail ∗ True)) ∗ True)%I.

Global Instance : LithiumUnfold
  (@zesuEncoderU256CallerContinuation) := I.

Definition zesuEncoderU256AtOutputCallSpec
    `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (∃ (sp ret : bv 64) (saved : list valu) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
      (["x10"; "x11"; "x12"; "x13"; "x14"; "x15"; "x16"; "x17"] ++
       tmp_registers)) ∗
    reg_col (zip_with
      (fun register value => (KindReg register, ExactShape value))
      zesuEncoderU256SavedRegisters saved) ∗
    "x1" ↦ᵣ RVal_Bits ret ∗
    "x2" ↦ᵣ RVal_Bits (sp - BV 64 48)%bv ∗
    (bv_unsigned sp - 48) ↦ₘ? 40 ∗
    (bv_unsigned sp - 8) ↦ₘ ret ∗
    ⌜length saved = 12%nat⌝ ∗
    ⌜Forall (fun value => valu_has_shape value (BitsShape 64)) saved⌝ ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned sp - 48⌝ ∗
    ⌜bv_unsigned sp < 0x40000000⌝ ∗
    ⌜bv_extract 0 1 ret = BV 1 0⌝ ∗
    ⌜bv_extract 1 1 ret = BV 1 0⌝ ∗
    ⌜bv_extract 0 2 ret = BV 2 0⌝ ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace
      (writeOutputEvents (sp - BV 64 48)%bv (BV 64 32) tail) ∗
    zesuEncoderU256CallerContinuation sp ret saved tail ∗ True)%I.

Global Instance : LithiumUnfold
  (@zesuEncoderU256AtOutputCallSpec) := I.

Definition zesuEncoderU256AfterOutputSpec
    `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (∃ (sp ret : bv 64) (saved : list valu) (tail : spec),
    zesu_c_call_ret 0 saved (BV 64 0x15cd8)
      (sp - BV 64 48)%bv
      (fun _ =>
        mmio_range 0x2401a0c0 16 ∗ spec_trace tail ∗ True) ∗
    (bv_unsigned sp - 48) ↦ₘ? 40 ∗
    (bv_unsigned sp - 8) ↦ₘ ret ∗
    ⌜length saved = 12%nat⌝ ∗
    ⌜Forall (fun value => valu_has_shape value (BitsShape 64)) saved⌝ ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned sp - 48⌝ ∗
    ⌜bv_unsigned sp < 0x40000000⌝ ∗
    ⌜bv_extract 0 1 ret = BV 1 0⌝ ∗
    ⌜bv_extract 1 1 ret = BV 1 0⌝ ∗
    ⌜bv_extract 0 2 ret = BV 2 0⌝ ∗
    zesuEncoderU256CallerContinuation sp ret saved tail ∗ True)%I.

Global Instance : LithiumUnfold
  (@zesuEncoderU256AfterOutputSpec) := I.

Definition zesuEncoderU256WriteOutputEntrySpec
    `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (∃ (sp ret : bv 64) (saved : list valu) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
      (["x12"; "x13"; "x14"; "x15"; "x16"; "x17"] ++ tmp_registers)) ∗
    reg_col (zip_with
      (fun register value => (KindReg register, ExactShape value))
      zesuEncoderU256SavedRegisters saved) ∗
    "x1" ↦ᵣ RVal_Bits (BV 64 0x15cd8) ∗
    "x2" ↦ᵣ RVal_Bits (sp - BV 64 48)%bv ∗
    "x10" ↦ᵣ RVal_Bits (sp - BV 64 48)%bv ∗
    "x11" ↦ᵣ RVal_Bits (BV 64 32) ∗
    (bv_unsigned sp - 48) ↦ₘ? 40 ∗
    (bv_unsigned sp - 8) ↦ₘ ret ∗
    ⌜length saved = 12%nat⌝ ∗
    ⌜Forall (fun value => valu_has_shape value (BitsShape 64)) saved⌝ ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned sp - 48⌝ ∗
    ⌜bv_unsigned sp < 0x40000000⌝ ∗
    ⌜bv_extract 0 1 ret = BV 1 0⌝ ∗
    ⌜bv_extract 1 1 ret = BV 1 0⌝ ∗
    ⌜bv_extract 0 2 ret = BV 2 0⌝ ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace
      (writeOutputEvents (sp - BV 64 48)%bv (BV 64 32) tail) ∗
    zesuEncoderU256CallerContinuation sp ret saved tail ∗
    instr_body 0x15cd8 zesuEncoderU256AfterOutputSpec ∗ True)%I.

Global Instance : LithiumUnfold
  (@zesuEncoderU256WriteOutputEntrySpec) := I.
