Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.StackArrayIndices.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactAuthorizationsU256 WriteSuccessExactTransactionsGasLoads
  WriteSuccessExactEncoderIntFramedCall WriteSuccessObservation WriteSuccessOutputSemantic.
From IslaTraces.write_success_78 Require Import instrs.
Local Remove Hints IslaTraces.write_success_78.a155cc_spec.a155cc_spec_inst : typeclass_instances.
Local Remove Hints IslaTraces.write_success_78.a155d4_spec.a155d4_spec_inst : typeclass_instances.

Definition authorizationIntPost `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (bytes : list (bv 8)) (ret : bv 64)
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  encoderIntExactFramedPost sp ret tail (authorizationU256Frame sp bytes P).
Global Instance : LithiumUnfold (@authorizationIntPost) := I.

Definition authorizationIntEntry `{!islaG Sigma} `{!threadG}
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
   ⌜length bytes = 144%nat⌝ ∗ ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜(0x20000000 <= bv_unsigned sp - 48)%Z⌝ ∗
   ⌜(bv_unsigned sp + 1896 < 0x40000000)%Z⌝ ∗ P ∗
   instr_pre (bv_unsigned ret) (authorizationIntPost sp bytes ret tail P) ∗ True)%I.
Global Instance : LithiumUnfold (@authorizationIntEntry) := I.

Lemma authorization_first_int_correct `{!islaG Sigma} `{!threadG}
    sp oldra old5 old11 bytes tail (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_78.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x155cc (authorizationIntEntry sp oldra old5 old11 bytes 96 (BV 64 0x155d8) tail P).
Proof.
  iStartProof. iIntros "#Hcaller #Hencoder #Houtput".
  iPoseProof (encoder_int_exact_framed_correct (transactionRowWord bytes 0 96)
    sp (BV 64 0x155d8) old5 old11 tail
    (authorizationU256Frame sp bytes P) with "Hencoder Houtput") as "Hcallee".
  iEval (rewrite /IslaTraces.write_success_78.instrs.instr_map /=) in "Hcaller".
  iDestruct "Hcaller" as "#(H0 & H1 & H2 & _)".
  zesu_run. Unshelve. all: unLET.
  all: unfold transactionRowWord; zesu_normalize_stack_array_indices; reflexivity.
Qed.
Print Assumptions authorization_first_int_correct.
