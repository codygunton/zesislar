Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactEncoderU128 WriteSuccessExactEncoderU128Correct.
From IslaTraces.write_success_37 Require Import instrs.
Local Remove Hints IslaTraces.write_success_37.a15114_spec.a15114_spec_inst : typeclass_instances.

Definition transactionGasPriceFrame `{!islaG Sigma} `{!threadG}
    (sp low high : bv 64) (P : iProp Sigma) : iProp Sigma :=
  ("x24" ↦ᵣ RVal_Bits high ∗ "x25" ↦ᵣ RVal_Bits low ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗ ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 32⌝ ∗
   ⌜bv_unsigned sp < (machineRamEnd defaultMap)⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionGasPriceFrame) := I.

Definition transactionGasPricePost `{!islaG Sigma} `{!threadG}
    (sp low high : bv 64) tail (P : iProp Sigma) : iProp Sigma :=
  encoderU128ExactPost low high sp (BV 64 0x15118) tail (transactionGasPriceFrame sp low high P).
Global Instance : LithiumUnfold (@transactionGasPricePost) := I.

Definition transactionGasPriceEntry `{!islaG Sigma} `{!threadG}
    (sp low high oldra old5 : bv 64) tail (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x1" ↦ᵣ RVal_Bits oldra ∗ "x5" ↦ᵣ RVal_Bits old5 ∗
   reg_col [(KindReg "x10", BitsShape 64); (KindReg "x11", BitsShape 64)] ∗
   "x24" ↦ᵣ RVal_Bits high ∗ "x25" ↦ᵣ RVal_Bits low ∗
   (bv_unsigned sp - 32) ↦ₘ? 32 ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace (writeOutputEvents (sp - BV 64 32)%bv (BV 64 16)
     (writeSuccessU128WordsPayload low high) tail) ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗ ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 32⌝ ∗
   ⌜bv_unsigned sp < (machineRamEnd defaultMap)⌝ ∗ P ∗
   instr_pre 0x15118 (transactionGasPricePost sp low high tail P) ∗ True)%I.
Global Instance : LithiumUnfold (@transactionGasPriceEntry) := I.

Lemma transactions_gas_price_call_correct `{!islaG Sigma} `{!threadG}
    sp low high oldra old5 tail (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_37.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_127.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15108 (transactionGasPriceEntry sp low high oldra old5 tail P).
Proof.
  iStartProof. iIntros "#Hcaller #Hencoder #Houtput".
  iPoseProof (encoder_u128_exact_correct low high sp (BV 64 0x15118) tail
    (transactionGasPriceFrame sp low high P) with "Hencoder Houtput") as "Hcallee".
  iEval (rewrite /IslaTraces.write_success_37.instrs.instr_map /=) in "Hcaller".
  iDestruct "Hcaller" as "#(H0 & H1 & H2 & H3 & _)".
  zesu_run. Unshelve. all: unLET. all: try bv_solve.
Qed.
Print Assumptions transactions_gas_price_call_correct.
