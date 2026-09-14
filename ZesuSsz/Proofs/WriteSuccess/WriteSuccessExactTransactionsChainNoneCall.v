Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactOptionalU64NoneCall WriteSuccessExactOptionalU64NoneCallSpec
  WriteSuccessExactBooleanSpec.
From IslaTraces.write_success_35 Require Import instrs.
Local Remove Hints IslaTraces.write_success_35.a150f8_spec.a150f8_spec_inst : typeclass_instances.

Definition transactionChainNoneEntry `{!islaG Sigma} `{!threadG}
    (sp oldra olddata old5 old6 old11 : bv 64)
    (bytes : list (bv 8)) tail (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits oldra ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x5" ↦ᵣ RVal_Bits old5 ∗ "x6" ↦ᵣ RVal_Bits old6 ∗
   "x10" ↦ᵣ RVal_Bits olddata ∗ "x11" ↦ᵣ RVal_Bits old11 ∗
   (bv_unsigned sp - 32) ↦ₘ? 32 ∗ bv_unsigned (sp + BV 64 1664)%bv ↦ₘ∗ bytes ∗
   ⌜bytes !! 8%nat = Some (BV 8 0)⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned (sp + BV 64 1664)%bv⌝ ∗
   ⌜bv_unsigned (sp + BV 64 1664)%bv + Z.of_nat (length bytes) < (machineRamEnd defaultMap)⌝ ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace (writeOutputEvents (sp - BV 64 9)%bv (BV 64 1)
     (writeSuccessBooleanWordPayload (BV 64 0)) tail) ∗
   ⌜bv_extract 0 4 sp = BV 4 0⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 32⌝ ∗ ⌜bv_unsigned sp < (machineRamEnd defaultMap)⌝ ∗
   P ∗ instr_pre 0x150fc (optionalU64NoneExactCallPost (sp + BV 64 1664)%bv sp
     (BV 64 0x150fc) bytes tail P) ∗ True)%I.
Global Instance : LithiumUnfold (@transactionChainNoneEntry) := I.

Lemma transactions_chain_none_call_correct `{!islaG Sigma} `{!threadG}
    sp oldra olddata old5 old6 old11 bytes tail (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_35.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_04.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_03.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x150f0 (transactionChainNoneEntry sp oldra olddata old5 old6 old11 bytes tail P).
Proof.
  iStartProof. iIntros "#Hcaller #Hoptional #Hboolean #Houtput".
  iPoseProof (optional_u64_none_exact_call_correct (sp + BV 64 1664)%bv sp
    (BV 64 0x150fc) old5 old6 old11 bytes tail P
    with "Hoptional Hboolean Houtput") as "Hcallee".
  iEval (rewrite /IslaTraces.write_success_35.instrs.instr_map /=) in "Hcaller".
  iDestruct "Hcaller" as "#(H0 & H1 & H2 & _)".
  zesu_run. Unshelve. all: unLET. all: try bv_solve.
Qed.
Print Assumptions transactions_chain_none_call_correct.
