Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.MemoryWords.
Require Import isla.riscv64.riscv64.
Require Import ZesuMachineMap.Machine.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessOutputSemantic WriteSuccessObservation WriteSuccessExactEncoderBytes.

Lemma exact_tail_present_bytes_call_handoff
    `{!islaG Sigma} `{!threadG} (sp data size oldS1 : bv 64)
    (bytes : list (bv 8)) (tail : spec) (P : iProp Sigma) :
  bv_unsigned sp `mod` 16 = 0 ->
  mapRamBase defaultMap <= bv_unsigned sp - 48 ->
  bv_unsigned sp + 8 < machineRamEnd defaultMap ->
  bv_unsigned size = length bytes ->
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  □ instr_pre 0x15c6c zesuEncoderBytesExactCallSpec -∗
  (∀ stack2 : bv 64, instr_pre 0x15990
    (encoderBytesExactReturn data size sp (BV 64 0x15990) bytes
       (BV 64 0) data oldS1 stack2 tail ∗
     (bv_unsigned sp + 8) ↦ₘ size ∗ P)) -∗
  instr_body 0x15980
    (reg_col zesu_ram_sys_regs ∗
     "x2" ↦ᵣ RVal_Bits sp ∗
     reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
       ["x1"; "x5"; "x6"; "x10"; "x11"]) ∗
     "x8" ↦ᵣ RVal_Bits data ∗ "x9" ↦ᵣ RVal_Bits oldS1 ∗
     (bv_unsigned sp + 8) ↦ₘ size ∗
     (bv_unsigned sp - 48) ↦ₘ? 48 ∗ bv_unsigned data ↦ₘ∗ bytes ∗
     mmio_range (machineOutputAddress defaultMap) 16 ∗
     spec_trace (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
       (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned size)))
       (writeOutputEvents data size bytes tail)) ∗ P ∗ True).
Proof.
  zesu_block.
  unLET.
  iRename select (∀ stack2 : bv 64, instr_pre 0x15990 _)%I into "Hnext".
  iAssert (∀ stack2 : bv 64, instr_pre 0x15990
    (encoderBytesExactReturn data size sp (BV 64 0x15990) bytes
      (BV 64 0) data oldS1 stack2 tail))%I with "[-]" as "Hreturn".
  { iIntros (stack2). iSpecialize ("Hnext" $! stack2).
    iApply (instr_pre_wand 0x15990 0x15990 true true with "Hnext"); [done | done |].
    iIntros "Hpost".
    have HsizeAddress : bv_unsigned (sp + BV 64 8)%bv = bv_unsigned sp + 8.
    { match goal with Hupper : bv_unsigned sp + 8 < machineRamEnd defaultMap |- _ =>
        clear -Hupper; bv_solve end. }
    rewrite -HsizeAddress. iFrame. }
  iRename select (instr_lookup_resources _) into "Hlookup".
  iClear "Hlookup".
  liInst (λ x, x.1ₗ = tail); unLET; liARun.
  replace (Z_to_bv 64 0x1598c + BV 64 4)%bv with (BV 64 0x15990) by bv_solve.
  iSplit; last done. iApply "Hreturn".
  Unshelve. all: prepare_sidecond.
  all: try assumption; try bv_solve.
Qed.
Print Assumptions exact_tail_present_bytes_call_handoff.
