Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Definition exactNativeLoadOtherRegisters : list string :=
  ["x1"; "x3"; "x4"; "x5"; "x6"; "x7"; "x9"; "x10"; "x11"; "x12"; "x13"; "x14"; "x15"; "x16"; "x17"; "x18"; "x19"; "x20"; "x21"; "x22"; "x23"; "x24"; "x25"; "x26"; "x27"; "x28"; "x29"; "x30"; "x31"].
Definition exactNativeLoadOtherShapes : list (reg_kind * valu_shape) :=
  (fun register => (KindReg register, BitsShape 64)) <$> exactNativeLoadOtherRegisters.
Definition exactNativeLoadState `{!islaG Sigma} `{!threadG}
    (sp decoded : bv 64) (object : list (bv 8)) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ reg_col exactNativeLoadOtherShapes ∗
   "x2" ↦ᵣ RVal_Bits sp ∗ "x8" ↦ᵣ RVal_Bits decoded ∗
   bv_unsigned decoded ↦ₘ∗ object ∗ bv_unsigned sp ↦ₘ? 312 ∗
   ⌜length object = 848%nat⌝ ∗ ⌜bv_unsigned decoded `mod` 8 = 0⌝ ∗
   ⌜mapRamBase defaultMap <= bv_unsigned decoded⌝ ∗
   ⌜bv_unsigned decoded + 848 < machineRamEnd defaultMap⌝ ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗ ⌜mapRamBase defaultMap <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp + 312 < machineRamEnd defaultMap⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@exactNativeLoadState) := I.
