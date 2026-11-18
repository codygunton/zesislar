Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.EntryWitnessReadiness.

Lemma entry_witness_nested_pure_frame `{!islaG Sigma} `{!threadG}
    (word : bv 64) (K : iProp Sigma) : True.
Proof.
  let body := constr:(fun witness : bv 64 =>
    (⌜witness = word⌝ ∗ (⌜witness = witness⌝ ∗ K))%I) in
  EntryWitnessReadiness.zesu_entry_witness_body_ready body.
  exact I.
Qed.

Lemma entry_witness_local_alias_frame `{!islaG Sigma} `{!threadG}
    (word : bv 64) (K : iProp Sigma) : True.
Proof.
  let tail := constr:(fun witness : bv 64 => (⌜witness = witness⌝ ∗ K)%I) in
  let body := constr:(fun witness : bv 64 => (⌜witness = word⌝ ∗ tail witness)%I) in
  EntryWitnessReadiness.zesu_entry_witness_body_ready body.
  exact I.
Qed.

Lemma entry_witness_dependent_frame_refuses `{!islaG Sigma} `{!threadG}
    (word : bv 64) : True.
Proof.
  Fail let tail := constr:(fun witness : bv 64 => ("x10" ↦ᵣ RVal_Bits witness)%I) in
  let body := constr:(fun witness : bv 64 =>
    (⌜witness = word⌝ ∗ (⌜witness = witness⌝ ∗ tail witness))%I) in
  EntryWitnessReadiness.zesu_entry_witness_body_ready body.
  exact I.
Qed.

Lemma entry_witness_symbolic_body_refuses `{!islaG Sigma} `{!threadG}
    (body : bv 64 -> iProp Sigma) : True.
Proof.
  Fail EntryWitnessReadiness.zesu_entry_witness_body_ready body.
  exact I.
Qed.

Lemma entry_witness_unresolved_body_refuses `{!islaG Sigma} `{!threadG} : True.
Proof.
  Fail let body := open_constr:(_ : bv 64 -> iProp Sigma) in
  EntryWitnessReadiness.zesu_entry_witness_body_ready body.
  exact I.
Qed.
