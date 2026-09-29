Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuMachineMap.Machine.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessOutputSemantic WriteSuccessExactBooleanSpec
  WriteSuccessExactBooleanClosedCall.

Lemma exact_tail_present_boolean_call_handoff
    `{!islaG Sigma} `{!threadG} (sp : bv 64) (tail : spec)
    (P : iProp Sigma) :
  bv_extract 0 4 sp = BV 4 0 ->
  mapRamBase defaultMap <= bv_unsigned sp - 16 ->
  bv_unsigned sp < machineRamEnd defaultMap ->
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  □ instr_pre 0x15b9c zesuEncoderBooleanExactCallSpec -∗
  instr_pre 0x15980
    (encoderBooleanClosedReturn (BV 64 1) sp (BV 64 0x15980) tail ∗ P) -∗
  instr_body 0x15974
    (reg_col zesu_ram_sys_regs ∗
     "x1" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
     "x2" ↦ᵣ RVal_Bits sp ∗
     "x5" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
     "x10" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
     "x11" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
     (bv_unsigned sp - 16) ↦ₘ? 16 ∗
     mmio_range (machineOutputAddress defaultMap) 16 ∗
     spec_trace (writeOutputEvents (sp - BV 64 9)%bv (BV 64 1)
       (writeSuccessBooleanWordPayload (BV 64 1)) tail) ∗ P ∗ True).
Proof.
  zesu_block.
  iRename select (instr_pre 0x15980
    (encoderBooleanClosedReturn (BV 64 1) sp (BV 64 0x15980) tail ∗ P)) into "Hnext".
  iRename select P into "HP".
  iAssert (instr_pre 0x15980
    (encoderBooleanClosedReturn (BV 64 1) sp (BV 64 0x15980) tail))%I
    with "[Hnext HP]" as "Hreturn".
  { iApply (instr_pre_wand 0x15980 0x15980 true true with "Hnext"); [done | done |].
    iIntros "Hpost". iFrame. }
  iRename select (instr_lookup_resources _) into "Hlookup".
  iClear "Hlookup".
  liInst (λ x, x.1ₗ = tail); unLET; liARun.
  iApply zesu_instr_pre_match_identity; [f_equal; bv_solve | done].
  Unshelve. all: prepare_sidecond.
  all: try assumption; try bv_solve.
Qed.
Print Assumptions exact_tail_present_boolean_call_handoff.
