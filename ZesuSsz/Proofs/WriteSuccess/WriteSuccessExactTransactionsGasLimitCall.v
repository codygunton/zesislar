Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactEncoderIntFramedCall WriteSuccessObservation WriteSuccessOutputSemantic.
From IslaTraces.write_success_43 Require Import instrs.
Local Remove Hints IslaTraces.write_success_43.a15150_spec.a15150_spec_inst : typeclass_instances.

Definition transactionGasLimitFrame `{!islaG Sigma} `{!threadG}
    (sp value : bv 64) (P : iProp Sigma) : iProp Sigma :=
  ("x26" ↦ᵣ RVal_Bits value ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗ ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 16⌝ ∗
   ⌜bv_unsigned sp < (machineRamEnd defaultMap)⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionGasLimitFrame) := I.

Definition transactionGasLimitPost `{!islaG Sigma} `{!threadG}
    (sp value : bv 64) tail (P : iProp Sigma) : iProp Sigma :=
  encoderIntExactFramedPost sp (BV 64 0x15154) tail (transactionGasLimitFrame sp value P).
Global Instance : LithiumUnfold (@transactionGasLimitPost) := I.

Definition transactionGasLimitEntry `{!islaG Sigma} `{!threadG}
    (sp value oldra old5 old11 : bv 64) tail (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x1" ↦ᵣ RVal_Bits oldra ∗ "x5" ↦ᵣ RVal_Bits old5 ∗
   "x11" ↦ᵣ RVal_Bits old11 ∗ reg_col [(KindReg "x10", BitsShape 64)] ∗
   "x26" ↦ᵣ RVal_Bits value ∗ (bv_unsigned sp - 16) ↦ₘ? 16 ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
     (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned value))) tail) ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗ ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 16⌝ ∗
   ⌜bv_unsigned sp < (machineRamEnd defaultMap)⌝ ∗ P ∗
   instr_pre 0x15154 (transactionGasLimitPost sp value tail P) ∗ True)%I.
Global Instance : LithiumUnfold (@transactionGasLimitEntry) := I.

Lemma transactions_gas_limit_call_correct `{!islaG Sigma} `{!threadG}
    sp value oldra old5 old11 tail (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_43.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15148 (transactionGasLimitEntry sp value oldra old5 old11 tail P).
Proof.
  iStartProof. iIntros "#Hcaller #Hencoder #Houtput".
  iPoseProof (encoder_int_exact_framed_correct value sp (BV 64 0x15154) old5 old11 tail
    (transactionGasLimitFrame sp value P) with "Hencoder Houtput") as "Hcallee".
  iEval (rewrite /IslaTraces.write_success_43.instrs.instr_map /=) in "Hcaller".
  iDestruct "Hcaller" as "#(H0 & H1 & H2 & _)".
  zesu_run. Unshelve. all: unLET. all: try bv_solve.
Qed.
Print Assumptions transactions_gas_limit_call_correct.
