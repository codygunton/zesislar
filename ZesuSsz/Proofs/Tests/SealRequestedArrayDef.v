From Coq Require Import ZArith.ZArith Lists.List NArith.NArith.
From stdpp.bitvector Require Import definitions.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* `StoreMemoryLookup.zesu_seal_requested_array_def`: a goal that asks for a
   byte array in the unsealed spelling `mem_mapsto_array_def` asks for the
   sealed array instead. *)

(* Head of a separating conjunction. *)
Lemma seal_requested_array_def_sep `{!islaG Σ} `{!threadG} (a : Z) (l : list (bv 8)) (K : iProp Σ) :
  (a ↦ₘ∗ l) -∗ K -∗ (isla.ghost_state.mem_mapsto_array_def a (DfracOwn 1) l ∗ K).
Proof.
  iIntros "Ha HK".
  ZesuSsz.Automation2.StoreMemoryLookup.zesu_seal_requested_array_def.
  iFrame.
Qed.

(* Under an existential package: the witness is opened as an evar and fixed
   by the package's resource. *)
Lemma seal_requested_array_def_exist `{!islaG Σ} `{!threadG} (a b : Z) (l m : list (bv 8)) :
  (a ↦ₘ∗ l) -∗ (b ↦ₘ∗ m) -∗
  (∃ x : list (bv 8), isla.ghost_state.mem_mapsto_array_def a (DfracOwn 1) l ∗ b ↦ₘ∗ x).
Proof.
  iIntros "Ha Hb".
  ZesuSsz.Automation2.StoreMemoryLookup.zesu_seal_requested_array_def.
  iFrame.
Qed.

(* A package whose component is a record (a call's outcome) fixed by a
   resource through its projection: the component is opened as an evar too;
   the primitive tuple witness refuses a record component. *)
Record seal_outcome := { seal_outcome_bytes : list (bv 8) }.

Lemma seal_requested_array_def_record `{!islaG Σ} `{!threadG} (a b : Z) (l : list (bv 8))
    (o : seal_outcome) :
  (a ↦ₘ∗ l) -∗ (b ↦ₘ∗ seal_outcome_bytes o) -∗
  (∃ x : li_prod seal_outcome unit,
    isla.ghost_state.mem_mapsto_array_def a (DfracOwn 1) l ∗
    b ↦ₘ∗ seal_outcome_bytes (li_fst x)).
Proof.
  iIntros "Ha Hb".
  Fail let w := ZesuSsz.Automation2.Hooks.zesu_constraint_witness
    (li_prod seal_outcome unit) in idtac.
  ZesuSsz.Automation2.StoreMemoryLookup.zesu_seal_requested_array_def.
  iFrame.
Qed.

(* A goal that already asks for the sealed array is left to the other steps. *)
Lemma seal_requested_array_def_sealed `{!islaG Σ} `{!threadG} (a : Z) (l : list (bv 8)) (K : iProp Σ) :
  (a ↦ₘ∗ l) -∗ K -∗ (a ↦ₘ∗ l ∗ K).
Proof.
  iIntros "Ha HK".
  Fail ZesuSsz.Automation2.StoreMemoryLookup.zesu_seal_requested_array_def.
  iFrame.
Qed.

Print Assumptions seal_requested_array_def_sep.
Print Assumptions seal_requested_array_def_exist.
