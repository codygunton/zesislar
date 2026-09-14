Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.StackArrayIndices.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsGasLoads
  WriteSuccessExactEncoderIntFramedCall WriteSuccessObservation WriteSuccessOutputSemantic.
From IslaTraces.write_success_91 Require Import instrs.
Local Remove Hints IslaTraces.write_success_91.a156a8_spec.a156a8_spec_inst : typeclass_instances.
Local Remove Hints IslaTraces.write_success_91.a156b0_spec.a156b0_spec_inst : typeclass_instances.

Definition withdrawalFieldsFrame `{!islaG Sigma}
    (sp : bv 64) (bytes : list (bv 8)) (P : iProp Sigma) : iProp Sigma :=
  ((bv_unsigned sp + 1744) ↦ₘ∗ bytes ∗ ⌜length bytes = 48%nat⌝ ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗ ⌜(0x20000000 <= bv_unsigned sp - 48)%Z⌝ ∗
   ⌜(bv_unsigned sp + 1896 < 0x40000000)%Z⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@withdrawalFieldsFrame) := I.

Definition withdrawalIntPost `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (bytes : list (bv 8)) (ret : bv 64)
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  encoderIntExactFramedPost sp ret tail (withdrawalFieldsFrame sp bytes P).
Global Instance : LithiumUnfold (@withdrawalIntPost) := I.

Definition withdrawalIntEntry `{!islaG Sigma} `{!threadG}
    (sp oldra old5 old11 : bv 64) (bytes : list (bv 8)) (offset : nat) (ret : bv 64)
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x1" ↦ᵣ RVal_Bits oldra ∗ "x5" ↦ᵣ RVal_Bits old5 ∗
   "x11" ↦ᵣ RVal_Bits old11 ∗ reg_col [(KindReg "x10", BitsShape 64)] ∗
   (bv_unsigned sp + 1744) ↦ₘ∗ bytes ∗ (bv_unsigned sp - 16) ↦ₘ? 16 ∗
   mmio_range 0x2401a0c0 16 ∗
   spec_trace (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
     (writeSuccessPrivateBytes (writeSuccessEncodeU64
       (bv_unsigned (transactionRowWord bytes 0 offset)))) tail) ∗
   ⌜length bytes = 48%nat⌝ ∗ ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜(0x20000000 <= bv_unsigned sp - 48)%Z⌝ ∗
   ⌜(bv_unsigned sp + 1896 < 0x40000000)%Z⌝ ∗ P ∗
   instr_pre (bv_unsigned ret) (withdrawalIntPost sp bytes ret tail P) ∗ True)%I.
Global Instance : LithiumUnfold (@withdrawalIntEntry) := I.

Lemma withdrawal_first_int_correct `{!islaG Sigma} `{!threadG}
    sp oldra old5 old11 bytes tail (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_91.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x156a8 (withdrawalIntEntry sp oldra old5 old11 bytes 0 (BV 64 0x156b4) tail P).
Proof.
  iStartProof. iIntros "#Hcaller #Hencoder #Houtput".
  iPoseProof (encoder_int_exact_framed_correct (transactionRowWord bytes 0 0)
    sp (BV 64 0x156b4) old5 old11 tail
    (withdrawalFieldsFrame sp bytes P) with "Hencoder Houtput") as "Hcallee".
  iEval (rewrite /IslaTraces.write_success_91.instrs.instr_map /=) in "Hcaller".
  iDestruct "Hcaller" as "#(H0 & H1 & H2 & _)".
  zesu_run. Unshelve. all: unLET.
  all: unfold transactionRowWord; zesu_normalize_stack_array_indices; reflexivity.
Qed.
Print Assumptions withdrawal_first_int_correct.
