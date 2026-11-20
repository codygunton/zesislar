From Coq Require Import ZArith.ZArith Lists.List NArith.NArith.
From stdpp.bitvector Require Import definitions.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* `StoreMemoryLookup.zesu_seal_requested_array_def`: a goal that asks for a
   byte array in the unsealed spelling `mem_mapsto_array_def` asks for the
   sealed array instead. `Hooks.zesu_liAStep` tries it only after
   `Hooks.zesu_seal_requested_array`, which seals a request whose bytes the
   context holds as the same sealed array and leaves the package closed. *)

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

(* Through the step selector, the context holds the bytes in another spelling
   (the requested list is `[b0; b1] ++ [b2]`): only this step applies; it
   seals the request and opens the package as evars. *)
Lemma seal_requested_array_def_step_other_spelling `{!islaG Σ} `{!threadG}
    (a : Z) (b0 b1 b2 : bv 8) (w : bv 64) :
  (a ↦ₘ∗ [b0; b1; b2]) -∗
  (∃ x : li_prod (bv 64) unit,
    isla.ghost_state.mem_mapsto_array_def a (DfracOwn 1) ([b0; b1] ++ [b2]) ∗
    ⌜li_fst x = w⌝).
Proof.
  iIntros "Ha".
  Fail ZesuSsz.Automation2.Hooks.zesu_seal_requested_array.
  ZesuSsz.Automation2.Hooks.zesu_liAStep.
  lazymatch goal with
  | |- environments.envs_entails _ (bi_sep (@mem_mapsto_array _ _ 8%N _ _ _) _) => idtac
  end.
  iSplitL "Ha"; [iFrame | iPureIntro; reflexivity].
Qed.

(* Through the step selector, the context holds the same bytes as a sealed
   array at that base (decodeItem's stored frame words): the earlier step
   seals the request and the package stays closed for its own witness step. *)
Lemma seal_requested_array_def_step_held `{!islaG Σ} `{!threadG}
    (a : Z) (l : list (bv 8)) (w : bv 64) :
  (a ↦ₘ∗ l) -∗
  (∃ x : li_prod (bv 64) unit,
    isla.ghost_state.mem_mapsto_array_def a (DfracOwn 1) l ∗ ⌜li_fst x = w⌝).
Proof.
  iIntros "Ha".
  ZesuSsz.Automation2.Hooks.zesu_liAStep.
  lazymatch goal with
  | |- environments.envs_entails _ (@bi_exist _ _ _) => idtac
  end.
  iExists (li_pair w tt). iFrame. done.
Qed.

Print Assumptions seal_requested_array_def_sep.
Print Assumptions seal_requested_array_def_exist.
