Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.CounterShapes.
Require Import ZesuSsz.Automation.CounterZero.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactAuthorizationsLoopSpec WriteSuccessExactAuthorizationsTail
  WriteSuccessExactAuthorizationsTailPositive WriteSuccessExactAuthorizationsTailZero
  WriteSuccessExactAuthorizationsReturnFacts.
Global Instance : LithiumUnfold (@authorizationLoopFacts) := I.

Lemma authorization_tail_native `{!islaG Sigma} `{!threadG}
    sp pointer base rows prefix row rest source tail (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_82.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15590 (authorizationLoopSpec sp base rows source tail P) -∗
  instr_body 0x15614 (authorizationTailState pointer
    (Z_to_bv 64 (Z.of_nat (S (length rest))))
    (authorizationTailPayload sp pointer base rows prefix row rest source tail P)).
Proof.
  destruct rest as [|next rest].
  - zesu_block.
    all: try reflexivity.
    exact (authorization_facts_end_pointer sp pointer base rows prefix row source H0).
  - zesu_block.
    1,2: exfalso; have Hbound := (proj1 (proj2 (proj2 (proj2 (proj2 H0)))));
      have Hzero := zesu_counter_zero_z_bound (S (length rest)) ltac:(cbn in Hbound; lia) H4;
      discriminate.
    liInst (fun x => x.1ₗ = next /\ x.2ₗ = prefix ++ [row]).
    zesu_run.
    exact (authorization_facts_advance sp pointer base rows prefix row next rest source H0).
Qed.
Print Assumptions authorization_tail_native.
