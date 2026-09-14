Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactOptionalU64NoneCall WriteSuccessExactOptionalU64NoneCallSpec
  WriteSuccessExactTransactionsChainNoneCall
  WriteSuccessExactBooleanSpec.
From IslaTraces.write_success_35 Require Import instrs.
Local Remove Hints IslaTraces.write_success_35.a150f8_spec.a150f8_spec_inst : typeclass_instances.

Definition transactionChainNoneCaller `{!islaG Sigma} `{!threadG}
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
   P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionChainNoneCaller) := I.


Lemma transactions_chain_none_caller_entry `{!islaG Sigma} `{!threadG}
    sp oldra olddata old5 old6 old11 bytes tail (P : iProp Sigma) :
  □ instr_pre 0x150fc (optionalU64NoneExactCallPost (sp + BV 64 1664)%bv sp
    (BV 64 0x150fc) bytes tail P) -∗
  transactionChainNoneCaller sp oldra olddata old5 old6 old11 bytes tail P -∗
  transactionChainNoneEntry sp oldra olddata old5 old6 old11 bytes tail P.
Proof.
  iStartProof. iIntros "#Hnext Hcaller".
  iEval (rewrite /transactionChainNoneCaller) in "Hcaller".
  iEval (rewrite /transactionChainNoneEntry).
  iDestruct "Hcaller" as "(Hsys & H1 & H2 & H5 & H6 & H10 & H11 & Hstack &
    Hbytes & Htag & Hmin & Hmax & Hmmio & Htrace & Hsp & Hlow & Hhigh & HP & _)".
  iFrame. iSplit; last done. iExact "Hnext".
Qed.
Print Assumptions transactions_chain_none_caller_entry.
