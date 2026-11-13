From Coq Require Import Lists.List ZArith.ZArith NArith.NArith Lia.
From stdpp Require Import list bitvector.definitions.
Require Import isla.riscv64.riscv64.
Local Open Scope Z_scope.

(* A word load from a byte array whose cells were opened into one
   hypothesis: `(a + 0 * 1) ↦ₘ b0 ∗ ... ∗ (a + 7 * 1) ↦ₘ b7 ∗ emp`. No
   memory lookup rule reads a word across single-byte cells. The rule folds
   the cells back into the byte array `a ↦ₘ∗ [b0; ...; b7]`, which the array
   read rules accept. The cells carry their own address range, so the fold
   needs no pure fact. *)

Section byte_cells.
  Context `{!islaG Sigma}.

  Lemma zesu_byte_cells_to_array (base : Z) q (first : bv 8) (rest : list (bv 8)) :
    ([∗ list] i ↦ v ∈ first :: rest, (base + Z.of_nat i * 1) ↦ₘ{q} v) -∗
    base ↦ₘ{q}∗ (first :: rest).
  Proof.
    iIntros "Hcells".
    iAssert (⌜0 ≤ base⌝)%I as %Hlow.
    { iDestruct (big_sepL_lookup_acc _ _ 0 first with "Hcells") as "[Hfirst _]"; [done|].
      iDestruct (mem_mapsto_in_range with "Hfirst") as %Hrange. iPureIntro. lia. }
    destruct (lookup_lt_is_Some_2 (first :: rest) (length rest)) as [last Hlast];
      [cbn; lia|].
    iAssert (⌜base + Z.of_nat (length rest) * 1 + 1 ≤ 2 ^ 64⌝)%I as %Hhigh.
    { iDestruct (big_sepL_lookup_acc _ _ _ last with "Hcells") as "[Hlast _]"; [exact Hlast|].
      iDestruct (mem_mapsto_in_range with "Hlast") as %Hrange. iPureIntro.
      cbn in Hrange. lia. }
    rewrite mem_mapsto_array_eq /mem_mapsto_array_def.
    iExists 1%N. iSplit; [done|]. iSplit.
    { iPureIntro. cbn [length]. lia. }
    iExact "Hcells".
  Qed.
End byte_cells.

(* The byte values of a chain of single-byte cells that ends in emp. *)
Ltac zesu_byte_cell_values chain :=
  lazymatch chain with
  | bi_emp => constr:(@nil (bv 8))
  | @monoid_unit _ _ _ => constr:(@nil (bv 8))
  | bi_sep (@mem_mapsto _ _ 8%N _ _ ?value) ?tail =>
      let rest := zesu_byte_cell_values tail in constr:(value :: rest)
  end.

(* At a memory lookup that no other rule takes, fold one hypothesis of at
   least eight consecutive byte cells (unit stride from index 0) back into
   its byte array. Each fold removes a cell chain, so the loop ends. *)
Ltac zesu_byte_cells_fold :=
  lazymatch goal with
  | |- iris.proofmode.environments.envs_entails _ (find_in_context (FindMemMapsTo _) _) => idtac
  end;
  iMatchHyp ltac:(fun H body =>
    lazymatch body with
    | bi_sep (@mem_mapsto _ _ 8%N (?base + Z.mul (Z.of_nat O) ?stride) ?fraction ?first) ?tail =>
        let rest := zesu_byte_cell_values tail in
        lazymatch rest with _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ => idtac end;
        lazymatch stride with 1%Z => idtac | Z.of_N 1%N => idtac end;
        iDestruct (zesu_byte_cells_to_array base fraction first rest with H) as H
    end).
