Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuMachineMap.Machine.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessOutputSemantic WriteSuccessObservation WriteSuccessExactEncoderIntCall.

Lemma exact_tail_scalar_call_handoff
    `{!islaG Sigma} `{!threadG} (sp saved value : bv 64) (tail : spec)
    (P : iProp Sigma) :
  bv_unsigned sp `mod` 16 = 0 ->
  mapRamBase defaultMap <= bv_unsigned sp - 16 ->
  bv_unsigned sp + 96 < machineRamEnd defaultMap ->
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  □ instr_pre 0x15d10 zesuEncoderIntExactCallSpec -∗
  instr_pre 0x159b0
    (encoderIntExactReturn sp (BV 64 0x159b0) tail ∗
     "x8" ↦ᵣ RVal_Bits saved ∗ (bv_unsigned sp + 96) ↦ₘ saved ∗
     (bv_unsigned sp + 80) ↦ₘ value ∗ P) -∗
  instr_body 0x159a0
    (reg_col zesu_ram_sys_regs ∗
     "x2" ↦ᵣ RVal_Bits sp ∗
     reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
       ["x1"; "x5"; "x8"; "x10"; "x11"]) ∗
     (bv_unsigned sp + 96) ↦ₘ saved ∗ (bv_unsigned sp + 80) ↦ₘ value ∗
     (bv_unsigned sp - 16) ↦ₘ? 16 ∗
     mmio_range (machineOutputAddress defaultMap) 16 ∗
     spec_trace (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
       (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned value))) tail) ∗
     P ∗ True).
Proof.
  zesu_block.
  unLET.
  iRename select (instr_pre 0x159b0 _) into "Hnext".
  iAssert (instr_pre 0x159b0
    (encoderIntExactReturn sp (BV 64 0x159b0) tail))%I with "[-]" as "Hreturn".
  { iApply (instr_pre_wand 0x159b0 0x159b0 true true with "Hnext"); [done | done |].
    iIntros "Hpost".
    have HsavedAddress : bv_unsigned (sp + BV 64 96)%bv = bv_unsigned sp + 96.
    { match goal with Hupper : bv_unsigned sp + 96 < machineRamEnd defaultMap |- _ =>
        clear -Hupper; bv_solve end. }
    have HvalueAddress : bv_unsigned (sp + BV 64 80)%bv = bv_unsigned sp + 80.
    { match goal with Hupper : bv_unsigned sp + 96 < machineRamEnd defaultMap |- _ =>
        clear -Hupper; bv_solve end. }
    rewrite -HsavedAddress -HvalueAddress. iFrame. }
  iRename select (instr_lookup_resources _) into "Hlookup".
  iClear "Hlookup".
  liInst (λ x, x.1ₗ = tail); unLET; liARun.
  iApply zesu_instr_pre_match_identity; [f_equal; bv_solve | done].
  Unshelve. all: prepare_sidecond.
  all: try assumption; try bv_solve.
Qed.
Print Assumptions exact_tail_scalar_call_handoff.
