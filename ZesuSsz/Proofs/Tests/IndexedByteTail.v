Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

Lemma fold_nested_control `{!islaG Sigma} (base : Z) (q : dfrac)
 (cells : list (bv 8)) (prefix suffix : iProp Sigma) :
 (0 <= base + 3 /\ base + 3 + Z.of_nat (length cells) <= 2^64) ->
 (prefix ∗ ([∗ list] i ↦ v ∈ cells, mem_mapsto (base + Z.of_nat (3+i)) q v) ∗ suffix) -∗
 (prefix ∗ mem_mapsto_array (base + 3) q cells ∗ suffix).
Proof.
 intros Hbound. iIntros "Howners".
 ZesuSsz.Automation2.StoreMemoryLookup.zesu_store_fold_indexed_byte_tail.
 iExact "Howners".
Qed.
Lemma refuse_word_cells `{!islaG Sigma} (base : Z) (q : dfrac) (cells : list (bv 64)) :
 ([∗ list] i ↦ v ∈ cells, mem_mapsto (base + Z.of_nat (3+i)) q v) -∗
 ([∗ list] i ↦ v ∈ cells, mem_mapsto (base + Z.of_nat (3+i)) q v).
Proof.
 iIntros "Hcells". assert_fails ZesuSsz.Automation2.StoreMemoryLookup.zesu_store_fold_indexed_byte_tail.
 idtac "WORD_OWNER_REFUSAL_EXECUTED". iAssumption.
Qed.
Lemma refuse_nonaffine_cells `{!islaG Sigma} (base : Z) (q : dfrac) (cells : list (bv 8)) :
 ([∗ list] i ↦ v ∈ cells, mem_mapsto (base + 2 * Z.of_nat i) q v) -∗
 ([∗ list] i ↦ v ∈ cells, mem_mapsto (base + 2 * Z.of_nat i) q v).
Proof.
 iIntros "Hcells". assert_fails ZesuSsz.Automation2.StoreMemoryLookup.zesu_store_fold_indexed_byte_tail.
 idtac "NONAFFINE_OWNER_REFUSAL_EXECUTED". iAssumption.
Qed.
Print Assumptions fold_nested_control.
Print Assumptions refuse_word_cells.
Print Assumptions refuse_nonaffine_cells.
