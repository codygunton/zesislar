Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactEncoderU256 WriteSuccessExactEncoderU256Spec.
From IslaTraces.write_success_85 Require Import instrs.
Local Remove Hints IslaTraces.write_success_85.a15644_spec.a15644_spec_inst : typeclass_instances.
Local Remove Hints IslaTraces.write_success_85.a15648_spec.a15648_spec_inst : typeclass_instances.
Local Remove Hints IslaTraces.write_success_85.a1564c_spec.a1564c_spec_inst : typeclass_instances.
Local Remove Hints IslaTraces.write_success_85.a15650_spec.a15650_spec_inst : typeclass_instances.
Local Remove Hints IslaTraces.write_success_85.a15658_spec.a15658_spec_inst : typeclass_instances.

Definition transactionSignatureSFrame `{!islaG Sigma} `{!threadG}
    (sp w0 w1 w2 w3 : bv 64) (P : iProp Sigma) : iProp Sigma :=
  ((bv_unsigned sp + 208) ↦ₘ w0 ∗ (bv_unsigned sp + 240) ↦ₘ w1 ∗
   (bv_unsigned sp + 232) ↦ₘ w2 ∗ (bv_unsigned sp + 224) ↦ₘ w3 ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗ ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 48⌝ ∗
   ⌜bv_unsigned sp + 248 < (machineRamEnd defaultMap)⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionSignatureSFrame) := I.

Definition transactionSignatureSPost `{!islaG Sigma} `{!threadG}
    (sp w0 w1 w2 w3 : bv 64) tail (P : iProp Sigma) : iProp Sigma :=
  encoderU256ExactPost w0 w1 w2 w3 sp (BV 64 0x1565c) tail
    (transactionSignatureSFrame sp w0 w1 w2 w3 P).
Global Instance : LithiumUnfold (@transactionSignatureSPost) := I.

Definition transactionSignatureSEntry `{!islaG Sigma} `{!threadG}
    (sp w0 w1 w2 w3 oldra old5 : bv 64) tail (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x1" ↦ᵣ RVal_Bits oldra ∗ "x5" ↦ᵣ RVal_Bits old5 ∗
   reg_col [(KindReg "x10", BitsShape 64); (KindReg "x11", BitsShape 64);
     (KindReg "x12", BitsShape 64); (KindReg "x13", BitsShape 64)] ∗
   (bv_unsigned sp - 48) ↦ₘ? 48 ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace (writeOutputEvents (sp - BV 64 48)%bv (BV 64 32)
     (writeSuccessU256WordsPayload w0 w1 w2 w3) tail) ∗
   transactionSignatureSFrame sp w0 w1 w2 w3 P ∗
   instr_pre 0x1565c (transactionSignatureSPost sp w0 w1 w2 w3 tail P) ∗ True)%I.
Global Instance : LithiumUnfold (@transactionSignatureSEntry) := I.

Lemma transactions_signature_s_call_correct `{!islaG Sigma} `{!threadG}
    sp w0 w1 w2 w3 oldra old5 tail (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_85.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_08.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15644 (transactionSignatureSEntry sp w0 w1 w2 w3 oldra old5 tail P).
Proof.
  iStartProof. iIntros "#Hcaller #Hencoder #Houtput".
  iPoseProof (encoder_u256_exact_correct w0 w1 w2 w3 sp (BV 64 0x1565c) tail
    (transactionSignatureSFrame sp w0 w1 w2 w3 P) with "Hencoder Houtput") as "Hcallee".
  iEval (rewrite /IslaTraces.write_success_85.instrs.instr_map /=) in "Hcaller".
  iDestruct "Hcaller" as "#(H0 & H1 & H2 & H3 & H4 & H5 & _)".
  zesu_run. Unshelve. all: unLET. all: try bv_solve.
Qed.
Print Assumptions transactions_signature_s_call_correct.
