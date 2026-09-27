Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.V2Steps.
Require Import ZesuSsz.Automation.Sets.v2.
Require Import ZesuSsz.Automation.Switches.ReturnWand.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeSuffixBytes158e0.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactBooleanClosedCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactBooleanSpec.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import isla.riscv64.riscv64.

Lemma test_suffix_return_wand `{!islaG Sigma} `{!threadG}
    (data size sp old_s0 old_s1 : bv 64)
    (bytes : list (bv 8)) (tail : spec) (P : iProp Sigma)
    (Halign : bv_unsigned sp `mod` 16 = 0)
    (Hmin : mapRamBase defaultMap <= bv_unsigned sp - 48)
    (Hmax : bv_unsigned sp < machineRamEnd defaultMap)
    (Hframe : bv_unsigned sp + 1896 < machineRamEnd defaultMap) :
  writeSuccessSuffixBytes158e0Frame sp data size bytes P -∗
  (((reg_col zesu_ram_sys_regs ∗
     "x1" ↦ᵣ RVal_Bits (Z_to_bv 64 (88300 + 4)) ∗
     "x2" ↦ᵣ RVal_Bits sp ∗
     "x5" ↦ᵣ RVal_Bits (BV 64 (mapIoContextAddress defaultMap)) ∗
     "x6" ↦ᵣ: (fun r6 => ⌜valu_has_shape r6 (BitsShape 64)⌝) ∗
     "x8" ↦ᵣ RVal_Bits old_s0 ∗ "x9" ↦ᵣ RVal_Bits old_s1 ∗
     "x10" ↦ᵣ RVal_Bits data ∗ "x11" ↦ᵣ RVal_Bits size ∗
     (bv_unsigned sp - 48) ↦ₘ? 48 ∗ bv_unsigned data ↦ₘ∗ bytes ∗
     mmio_range (machineOutputAddress defaultMap) 16 ∗
     spec_trace tail ∗ True) -∗ writeSuccessSuffixAt158f0 P) ∗ True).
Proof.
  iIntros "Hcaller".
  zesu_rule_set_v2_steps.
  zesu_run_pass_v2.
  iDestruct select (reg_col zesu_ram_sys_regs ∗ _)%I as "(Hsys & H1 & H2 & H5 & H6 & H8 & H9 & H10 & H11 & Hstack & Hdata & Hmmio & Htrace & _)".
  iExists (tail, bytes, old_s1, old_s0, size, data, sp, tt)ₗ.
  iEval (replace (Z_to_bv 64 (88300 + 4)) with (BV 64 0x158f0) by bv_solve) in "H1".
  iFrame.
  repeat iSplit; try done; iPureIntro; assumption.
Qed.
Print Assumptions test_suffix_return_wand.

Lemma test_boolean_return_wand `{!islaG Sigma} `{!threadG}
    (value sp ret : bv 64) (tail : spec) (P : iProp Sigma) :
  P -∗
  ((encoderBooleanClosedReturn value sp ret tail -∗
    encoderBooleanExactPost value sp ret tail P) ∗ True).
Proof.
  iIntros "HP".
  zesu_rule_set_v2_steps.
  iApply encoder_boolean_closed_return_to_framed. iFrame.
Qed.
Print Assumptions test_boolean_return_wand.
