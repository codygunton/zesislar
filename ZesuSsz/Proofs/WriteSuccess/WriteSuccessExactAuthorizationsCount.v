Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactEncoderIntFramedCall WriteSuccessObservation WriteSuccessOutputSemantic.
From IslaTraces.write_success_73 Require Import instrs.
Local Remove Hints IslaTraces.write_success_73.a15574_spec.a15574_spec_inst : typeclass_instances.
Local Remove Hints IslaTraces.write_success_73.a15580_spec.a15580_spec_inst : typeclass_instances.

Definition authorizationCountFrame `{!islaG Sigma} `{!threadG}
    (sp count : bv 64) (P : iProp Sigma) : iProp Sigma :=
  ((bv_unsigned sp + 160) ↦ₘ count ∗ "x18" ↦ᵣ RVal_Bits count ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗ ⌜0x20000000 <= bv_unsigned sp - 16⌝ ∗
   ⌜bv_unsigned sp + 176 < 0x40000000⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@authorizationCountFrame) := I.

Definition authorizationCountPost `{!islaG Sigma} `{!threadG}
    (sp count : bv 64) tail (P : iProp Sigma) : iProp Sigma :=
  encoderIntExactFramedPost sp (BV 64 0x15584) tail (authorizationCountFrame sp count P).
Global Instance : LithiumUnfold (@authorizationCountPost) := I.

Definition authorizationCountEntry `{!islaG Sigma} `{!threadG}
    (sp count oldra old5 old11 : bv 64) tail (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x1" ↦ᵣ RVal_Bits oldra ∗ "x5" ↦ᵣ RVal_Bits old5 ∗
   "x11" ↦ᵣ RVal_Bits old11 ∗
   reg_col [(KindReg "x10", BitsShape 64); (KindReg "x18", BitsShape 64)] ∗
   (bv_unsigned sp + 160) ↦ₘ count ∗ (bv_unsigned sp - 16) ↦ₘ? 16 ∗
   mmio_range 0x2401a0c0 16 ∗
   spec_trace (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
     (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned count))) tail) ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗ ⌜0x20000000 <= bv_unsigned sp - 16⌝ ∗
   ⌜bv_unsigned sp + 176 < 0x40000000⌝ ∗ P ∗
   instr_pre 0x15584 (authorizationCountPost sp count tail P) ∗ True)%I.
Global Instance : LithiumUnfold (@authorizationCountEntry) := I.

Lemma authorization_count_correct `{!islaG Sigma} `{!threadG}
    sp count oldra old5 old11 tail (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_73.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15574 (authorizationCountEntry sp count oldra old5 old11 tail P).
Proof.
  iStartProof. iIntros "#Hcaller #Hencoder #Houtput".
  iPoseProof (encoder_int_exact_framed_correct count sp (BV 64 0x15584) old5 old11 tail
    (authorizationCountFrame sp count P) with "Hencoder Houtput") as "Hcallee".
  iEval (rewrite /IslaTraces.write_success_73.instrs.instr_map /=) in "Hcaller".
  iDestruct "Hcaller" as "#(H0 & H1 & H2 & H3 & _)".
  zesu_run. Unshelve. all: unLET. all: try bv_solve.
Qed.
Print Assumptions authorization_count_correct.
