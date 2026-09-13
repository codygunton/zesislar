Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.StackArrayIndices.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsGasLoads
  WriteSuccessExactEncoderU256 WriteSuccessExactEncoderU256Spec.
From IslaTraces.write_success_76 Require Import instrs.
Local Remove Hints IslaTraces.write_success_76.a155a4_spec.a155a4_spec_inst : typeclass_instances.
Local Remove Hints IslaTraces.write_success_76.a155a8_spec.a155a8_spec_inst : typeclass_instances.
Local Remove Hints IslaTraces.write_success_76.a155ac_spec.a155ac_spec_inst : typeclass_instances.
Local Remove Hints IslaTraces.write_success_76.a155b0_spec.a155b0_spec_inst : typeclass_instances.
Local Remove Hints IslaTraces.write_success_76.a155b8_spec.a155b8_spec_inst : typeclass_instances.

Definition authorizationU256Frame `{!islaG Sigma}
    (sp : bv 64) (bytes : list (bv 8)) (P : iProp Sigma) : iProp Sigma :=
  ((bv_unsigned sp + 1744) ↦ₘ∗ bytes ∗ ⌜length bytes = 144%nat⌝ ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗ ⌜(0x20000000 <= bv_unsigned sp - 48)%Z⌝ ∗
   ⌜(bv_unsigned sp + 1896 < 0x40000000)%Z⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@authorizationU256Frame) := I.

Definition authorizationU256Post `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (bytes : list (bv 8)) (offset : nat) (ret : bv 64)
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  encoderU256ExactPost (transactionRowWord bytes offset 0)
    (transactionRowWord bytes offset 8) (transactionRowWord bytes offset 16)
    (transactionRowWord bytes offset 24) sp ret tail (authorizationU256Frame sp bytes P).
Global Instance : LithiumUnfold (@authorizationU256Post) := I.

Definition authorizationU256Entry `{!islaG Sigma} `{!threadG}
    (sp oldra old5 : bv 64) (bytes : list (bv 8)) (offset : nat) (ret : bv 64)
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x1" ↦ᵣ RVal_Bits oldra ∗ "x5" ↦ᵣ RVal_Bits old5 ∗
   reg_col [(KindReg "x10", BitsShape 64); (KindReg "x11", BitsShape 64);
     (KindReg "x12", BitsShape 64); (KindReg "x13", BitsShape 64)] ∗
   (bv_unsigned sp + 1744) ↦ₘ∗ bytes ∗ (bv_unsigned sp - 48) ↦ₘ? 48 ∗
   mmio_range 0x2401a0c0 16 ∗
   spec_trace (writeOutputEvents (sp - BV 64 48)%bv (BV 64 32)
     (writeSuccessU256WordsPayload (transactionRowWord bytes offset 0)
       (transactionRowWord bytes offset 8) (transactionRowWord bytes offset 16)
       (transactionRowWord bytes offset 24)) tail) ∗
   ⌜length bytes = 144%nat⌝ ∗ ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜(0x20000000 <= bv_unsigned sp - 48)%Z⌝ ∗
   ⌜(bv_unsigned sp + 1896 < 0x40000000)%Z⌝ ∗ P ∗
   instr_pre (bv_unsigned ret) (authorizationU256Post sp bytes offset ret tail P) ∗ True)%I.
Global Instance : LithiumUnfold (@authorizationU256Entry) := I.

Lemma authorization_first_u256_correct `{!islaG Sigma} `{!threadG}
    sp oldra old5 bytes tail (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_76.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_08.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x155a4 (authorizationU256Entry sp oldra old5 bytes 0 (BV 64 0x155bc) tail P).
Proof.
  iStartProof. iIntros "#Hcaller #Hencoder #Houtput".
  iPoseProof (encoder_u256_exact_correct (transactionRowWord bytes 0 0)
    (transactionRowWord bytes 0 8) (transactionRowWord bytes 0 16)
    (transactionRowWord bytes 0 24) sp (BV 64 0x155bc) tail
    (authorizationU256Frame sp bytes P) with "Hencoder Houtput") as "Hcallee".
  iEval (rewrite /IslaTraces.write_success_76.instrs.instr_map /=) in "Hcaller".
  iDestruct "Hcaller" as "#(H0 & H1 & H2 & H3 & H4 & H5 & _)".
  zesu_run. Unshelve. all: unLET.
  all: unfold transactionRowWord; zesu_normalize_stack_array_indices; reflexivity.
Qed.
Print Assumptions authorization_first_u256_correct.
