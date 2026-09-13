Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactEncoderIntFramedCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputSemantic.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith.
From IslaTraces.write_success_64 Require Import instrs.

Definition accessReturnCountFrame `{!islaG Sigma} `{!threadG}
    (sp savedX22 : bv 64) (P : iProp Sigma) : iProp Sigma :=
  ("x22" ↦ᵣ RVal_Bits savedX22 ∗ (bv_unsigned sp + 136) ↦ₘ savedX22 ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@accessReturnCountFrame) := I.

Definition accessReturnCountPost `{!islaG Sigma} `{!threadG}
    (sp savedX22 : bv 64) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  encoderIntExactFramedPost sp (BV 64 0x153d0) tail (accessReturnCountFrame sp savedX22 P).
Global Instance : LithiumUnfold (@accessReturnCountPost) := I.

Definition accessReturnCountEntry `{!islaG Sigma} `{!threadG}
    (sp savedX22 old22 old_ra old5 old_data old_size : bv 64)
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x22" ↦ᵣ RVal_Bits old22 ∗
   "x1" ↦ᵣ RVal_Bits old_ra ∗ "x5" ↦ᵣ RVal_Bits old5 ∗
   "x10" ↦ᵣ RVal_Bits old_data ∗ "x11" ↦ᵣ RVal_Bits old_size ∗
   (bv_unsigned sp + 136) ↦ₘ savedX22 ∗ (bv_unsigned sp - 16) ↦ₘ? 16 ∗
   mmio_range 0x2401a0c0 16 ∗
   spec_trace (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
     (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned savedX22))) tail) ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜0x20000000 <= bv_unsigned sp - 16⌝ ∗ ⌜bv_unsigned sp + 144 < 0x40000000⌝ ∗
   instr_pre 0x153d0 (accessReturnCountPost sp savedX22 tail P) ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@accessReturnCountEntry) := I.

Lemma access_return_count_correct `{!islaG Sigma} `{!threadG}
    sp savedX22 old22 old_ra old5 old_data old_size tail (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_64.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x153c0 (accessReturnCountEntry sp savedX22 old22 old_ra old5 old_data old_size tail P).
Proof.
  iStartProof. iIntros "#Hcaller #Hencoder #Houtput".
  iPoseProof (encoder_int_exact_framed_correct savedX22 sp (BV 64 0x153d0)
    old5 old_size tail (accessReturnCountFrame sp savedX22 P)
    with "Hencoder Houtput") as "Hcallee".
  iEval (rewrite /IslaTraces.write_success_64.instrs.instr_map /=) in "Hcaller".
  iDestruct "Hcaller" as "#(H0 & H1 & H2 & H3 & _)".
  zesu_run. Unshelve. all: prepare_sidecond.
  all: try assumption; try bv_solve.
Qed.
Print Assumptions access_return_count_correct.
