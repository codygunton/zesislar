Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.CallScratchBoolean.
Require Import isla.riscv64.riscv64.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactBooleanSpec WriteSuccessExactBooleanClosedCall.

Lemma exact_tail_boolean_return_scratch_handoff
    `{!islaG Sigma} `{!threadG} (value sp ret : bv 64)
    (tail : spec) (P : iProp Sigma) :
  mapRamBase defaultMap <= bv_unsigned sp - 16 ->
  encoderBooleanClosedReturn value sp ret tail ∗ P -∗
  reg_col zesu_ram_sys_regs ∗
  "x1" ↦ᵣ RVal_Bits ret ∗ "x2" ↦ᵣ RVal_Bits sp ∗
  "x5" ↦ᵣ RVal_Bits (BV 64 (mapIoContextAddress defaultMap)) ∗
  "x10" ↦ᵣ RVal_Bits (sp - BV 64 9)%bv ∗
  "x11" ↦ᵣ RVal_Bits (BV 64 1) ∗
  (bv_unsigned sp - 16) ↦ₘ? 16 ∗
  mmio_range (machineOutputAddress defaultMap) 16 ∗
  spec_trace tail ∗ P.
Proof.
  intros Hlower. iIntros "[Hreturn HP]".
  iEval (unfold encoderBooleanClosedReturn) in "Hreturn".
  iDestruct "Hreturn" as
    "(Hsys & H1 & H2 & Hret & H5 & H10 & H11 & Hpayload & Hgap & Hmmio & Htrace & _)".
  have Haddress : bv_unsigned (sp - BV 64 9)%bv = bv_unsigned sp - 9 by bv_solve.
  iEval (rewrite /writeSuccessBooleanWordPayload mem_mapsto_array_singleton Haddress) in "Hpayload".
  iPoseProof (call_boolean_scratch_reuse sp ret _ with "[$Hgap $Hpayload $Hret]") as "Hscratch".
  iFrame.
Qed.
Print Assumptions exact_tail_boolean_return_scratch_handoff.
