Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputSemantic.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactEncoderIntFramedCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsGasLoads.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith.
From IslaTraces.write_success_56 Require Import instrs.
Import ZesuSsz.Automation.Calls.FramedContinuations.

Definition accessCountWholeFrame `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (bytes : list (bv 8)) (P : iProp Sigma) : iProp Sigma :=
  ((bv_unsigned sp + 1744) ↦ₘ∗ bytes ∗ ⌜length bytes = 40%nat⌝ ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗ ⌜0x20000000 <= bv_unsigned sp - 16⌝ ∗
   ⌜bv_unsigned sp + 1784 < 0x40000000⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@accessCountWholeFrame) := I.

Definition accessCountWholePost `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (bytes : list (bv 8)) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  encoderIntExactFramedPost sp (BV 64 0x1521c) tail (accessCountWholeFrame sp bytes P).
Global Instance : LithiumUnfold (@accessCountWholePost) := I.

Definition accessCountWholeEntry `{!islaG Sigma} `{!threadG}
    (sp old_ra old5 old_data old_size : bv 64) (bytes : list (bv 8))
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x1" ↦ᵣ RVal_Bits old_ra ∗ "x5" ↦ᵣ RVal_Bits old5 ∗
   "x10" ↦ᵣ RVal_Bits old_data ∗ "x11" ↦ᵣ RVal_Bits old_size ∗
   (bv_unsigned sp - 16) ↦ₘ? 16 ∗ mmio_range 0x2401a0c0 16 ∗
   spec_trace (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
     (writeSuccessPrivateBytes (writeSuccessEncodeU64
       (bv_unsigned (transactionRowWord bytes 0 8)))) tail) ∗
   accessCountWholeFrame sp bytes P ∗
   instr_pre 0x1521c (accessCountWholePost sp bytes tail P) ∗ True)%I.
Global Instance : LithiumUnfold (@accessCountWholeEntry) := I.

Lemma access_count_whole_correct `{!islaG Sigma} `{!threadG}
    sp old_ra old5 old_data old_size bytes tail (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_56.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15210 (accessCountWholeEntry sp old_ra old5 old_data old_size bytes tail P).
Proof.
  iStartProof. iIntros "#Hcaller #Hencoder #Houtput".
  iPoseProof (encoder_int_exact_framed_correct (transactionRowWord bytes 0 8)
    sp (BV 64 0x1521c) old5 old_size tail (accessCountWholeFrame sp bytes P)
    with "Hencoder Houtput") as "Hcallee".
  iEval (rewrite /IslaTraces.write_success_56.instrs.instr_map /=) in "Hcaller".
  iDestruct "Hcaller" as "#(H0 & H1 & H2 & _)".
  zesu_run.
  Unshelve. all: prepare_sidecond.
  all: try assumption; try bv_solve.
  Unshelve. all: liShow.
  all: have Hoffset : bv_unsigned (sp + BV 64 1752)%bv -
    (bv_unsigned sp + 1744) = 8 by bv_solve.
  all: rewrite Hoffset; unfold transactionRowWord; cbn; done.
Qed.
Print Assumptions access_count_whole_correct.
