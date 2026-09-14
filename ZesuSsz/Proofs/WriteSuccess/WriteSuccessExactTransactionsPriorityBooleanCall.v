Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From ZesuSsz.Proofs.WriteSuccess Require Import WriteSuccessExactBooleanSpec.
From IslaTraces.write_success_39 Require Import instrs.
From IslaTraces.write_success_42 Require Import instrs.
Local Remove Hints IslaTraces.write_success_39.a15124_spec.a15124_spec_inst : typeclass_instances.
Local Remove Hints IslaTraces.write_success_42.a15144_spec.a15144_spec_inst : typeclass_instances.

Definition transactionPriorityBooleanEntry `{!islaG Sigma} `{!threadG}
    (present : bool) (sp oldra olddata old5 old11 : bv 64) tail (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits oldra ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x10" ↦ᵣ RVal_Bits olddata ∗ (bv_unsigned sp - 16) ↦ₘ? 16 ∗
   ⌜bv_extract 0 4 sp = BV 4 0⌝ ∗ ⌜bv_extract 0 3 sp = BV 3 0⌝ ∗
   ⌜0x20000000 <= bv_unsigned sp - 16⌝ ∗ ⌜bv_unsigned sp < 0x40000000⌝ ∗
   encoderBooleanExactPrefixFrame (if present then BV 64 1 else BV 64 0) sp
     (if present then BV 64 0x15128 else BV 64 0x15148) old5 old11 tail P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionPriorityBooleanEntry) := I.

Lemma transactions_priority_boolean_call_correct `{!islaG Sigma} `{!threadG}
    (present : bool) sp oldra olddata old5 old11 tail (P : iProp Sigma) :
  ([∗ list] instruction ∈ (if present then IslaTraces.write_success_39.instrs.instr_map
    else IslaTraces.write_success_42.instrs.instr_map),
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_03.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body (if present then 0x1511c else 0x1513c)
    (transactionPriorityBooleanEntry present sp oldra olddata old5 old11 tail P).
Proof.
  destruct present; iStartProof; iIntros "#Hcaller #Hboolean #Houtput".
  - iPoseProof (encoder_boolean_exact_framed_correct (BV 64 1) sp (BV 64 0x15128)
      old5 old11 tail P with "Hboolean Houtput") as "Hcallee".
    iEval (rewrite /IslaTraces.write_success_39.instrs.instr_map /=) in "Hcaller".
    iDestruct "Hcaller" as "#(H0 & H1 & H2 & _)".
    zesu_run. Unshelve. all: unLET. all: try bv_solve.
  - iPoseProof (encoder_boolean_exact_framed_correct (BV 64 0) sp (BV 64 0x15148)
      old5 old11 tail P with "Hboolean Houtput") as "Hcallee".
    iEval (rewrite /IslaTraces.write_success_42.instrs.instr_map /=) in "Hcaller".
    iDestruct "Hcaller" as "#(H0 & H1 & H2 & _)".
    zesu_run. Unshelve. all: unLET. all: try bv_solve.
Qed.
Print Assumptions transactions_priority_boolean_call_correct.
