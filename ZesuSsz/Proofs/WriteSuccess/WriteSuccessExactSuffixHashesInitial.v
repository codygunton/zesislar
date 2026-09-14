Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.CounterShapes.
Require Import ZesuSsz.Automation.CounterZero.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactSuffixHashesLoopSpec.
From IslaTraces.write_success_102 Require Import instrs.
Local Existing Instance subsume_instr_pre_guard_inst | 0.
Local Instance : LithiumUnfold (@suffixLoopFacts) := I.

Lemma suffix_initial_nonempty `{!islaG Sigma} `{!threadG}
    sp base total source tail (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_102.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15754 (suffixLoopSpec sp base total source tail P) -∗
  instr_body 0x15750 (suffixLoopSpec sp base total source tail P).
Proof.
  zesu_block.
  all: try (exfalso;
    match goal with
    | Hfacts : suffixLoopFacts _ _ _ _ _ _ _,
      Hzero : Z_to_bv 64 (Z.of_nat (S ?remaining)) = BV 64 0 |- _ =>
        have Hbound := (proj1 (proj2 (proj2 (proj2 Hfacts))));
        have Hcount := zesu_counter_zero_z_bound (S remaining) Hbound Hzero;
        discriminate
    end).
  liInst (fun x => x.1ₗ = processed).
  zesu_run.
Qed.
Print Assumptions suffix_initial_nonempty.
