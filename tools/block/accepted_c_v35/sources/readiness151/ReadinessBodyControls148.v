(* Focused readiness controls against the exact bound guard source. *)
Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.EntryWitnessReadiness.

Lemma readiness_pure_package `{!islaG Sigma} `{!threadG} (word : bv 64) : True.
Proof.
  let body := constr:(fun witness : bv 64 => ((⌜witness = word⌝)%I : iProp Sigma)) in
  EntryWitnessReadiness.zesu_entry_witness_body_ready body.
  exact I.
Qed.

Lemma readiness_independent_frame `{!islaG Sigma} `{!threadG}
    (word : bv 64) (K : iProp Sigma) : True.
Proof.
  let body := constr:(fun witness : bv 64 => (⌜witness = word⌝ ∗ K)%I) in
  EntryWitnessReadiness.zesu_entry_witness_body_ready body.
  exact I.
Qed.

Lemma readiness_register_then_local_goal_refuses `{!islaG Sigma} `{!threadG}
    (word : bv 64) : True.
Proof.
  Fail let LET_GOAL := constr:(fun witness : bv 64 => ("x10" ↦ᵣ RVal_Bits witness)%I) in
  let body := constr:(fun witness : bv 64 =>
    (⌜RVal_Bits word = RVal_Bits witness⌝ ∗ LET_GOAL witness)%I) in
  EntryWitnessReadiness.zesu_entry_witness_body_ready body.
  exact I.
Qed.

Lemma readiness_dependent_spatial_refuses `{!islaG Sigma} `{!threadG} : True.
Proof.
  Fail let body := constr:(fun witness : bv 64 => ("x10" ↦ᵣ RVal_Bits witness)%I) in
  EntryWitnessReadiness.zesu_entry_witness_body_ready body.
  exact I.
Qed.

Lemma dependent_guard_fallback_diagnostic148 `{!islaG Sigma} `{!threadG}
    (word : bv 64) : True.
Proof.
 let LET_GOAL := constr:(fun witness : bv 64 => ("x10" ↦ᵣ RVal_Bits witness)%I) in
 let body := constr:(fun witness : bv 64 =>
   (⌜RVal_Bits word = RVal_Bits witness⌝ ∗ LET_GOAL witness)%I) in
 first [
   first [EntryWitnessReadiness.zesu_entry_witness_body_ready body;
          idtac "GUARD_ACCEPTED" | idtac "GUARD_REFUSED"];
   idtac "INNER_FALLBACK_RETURNED"
 | idtac "GUARD_ESCAPED_ONE_FIRST" ].
 exact I.
Qed.
