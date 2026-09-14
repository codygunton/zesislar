Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactEncoderU256 WriteSuccessExactEncoderU256Spec.
From IslaTraces.write_success_49 Require Import instrs.
Local Remove Hints IslaTraces.write_success_49.a151a4_spec.a151a4_spec_inst : typeclass_instances.
Local Remove Hints IslaTraces.write_success_49.a151b0_spec.a151b0_spec_inst : typeclass_instances.

Definition transactionValueFrame `{!islaG Sigma} `{!threadG}
    (sp w0 w1 w2 w3 : bv 64) (P : iProp Sigma) : iProp Sigma :=
  ("x18" ↦ᵣ RVal_Bits w0 ∗ "x20" ↦ᵣ RVal_Bits w1 ∗
   (bv_unsigned sp + 128) ↦ₘ w2 ∗ "x21" ↦ᵣ RVal_Bits w3 ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗ ⌜0x20000000 <= bv_unsigned sp - 48⌝ ∗
   ⌜bv_unsigned sp + 136 < 0x40000000⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionValueFrame) := I.

Definition transactionValuePost `{!islaG Sigma} `{!threadG}
    (sp w0 w1 w2 w3 : bv 64) tail (P : iProp Sigma) : iProp Sigma :=
  encoderU256ExactPost w0 w1 w2 w3 sp (BV 64 0x151b4) tail
    (transactionValueFrame sp w0 w1 w2 w3 P).
Global Instance : LithiumUnfold (@transactionValuePost) := I.

Definition transactionValueEntry `{!islaG Sigma} `{!threadG}
    (sp w0 w1 w2 w3 oldra old5 : bv 64) tail (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x1" ↦ᵣ RVal_Bits oldra ∗ "x5" ↦ᵣ RVal_Bits old5 ∗
   reg_col [(KindReg "x10", BitsShape 64); (KindReg "x11", BitsShape 64);
     (KindReg "x12", BitsShape 64); (KindReg "x13", BitsShape 64)] ∗
   (bv_unsigned sp - 48) ↦ₘ? 48 ∗ mmio_range 0x2401a0c0 16 ∗
   spec_trace (writeOutputEvents (sp - BV 64 48)%bv (BV 64 32)
     (writeSuccessU256WordsPayload w0 w1 w2 w3) tail) ∗
   transactionValueFrame sp w0 w1 w2 w3 P ∗
   instr_pre 0x151b4 (transactionValuePost sp w0 w1 w2 w3 tail P) ∗ True)%I.
Global Instance : LithiumUnfold (@transactionValueEntry) := I.

Lemma transactions_value_call_correct `{!islaG Sigma} `{!threadG}
    sp w0 w1 w2 w3 oldra old5 tail (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_49.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_08.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x1519c (transactionValueEntry sp w0 w1 w2 w3 oldra old5 tail P).
Proof.
  iStartProof. iIntros "#Hcaller #Hencoder #Houtput".
  iPoseProof (encoder_u256_exact_correct w0 w1 w2 w3 sp (BV 64 0x151b4) tail
    (transactionValueFrame sp w0 w1 w2 w3 P) with "Hencoder Houtput") as "Hcallee".
  iEval (rewrite /IslaTraces.write_success_49.instrs.instr_map /=) in "Hcaller".
  iDestruct "Hcaller" as "#(H0 & H1 & H2 & H3 & H4 & H5 & _)".
  zesu_run. Unshelve. all: unLET. all: try bv_solve.
Qed.
Print Assumptions transactions_value_call_correct.
