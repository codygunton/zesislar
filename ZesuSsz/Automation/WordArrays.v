Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMemory.
From Coq Require Import Lists.List ZArith.ZArith.

Section word_arrays.
  Context `{!islaG Sigma}.

  Lemma subsume_u64_byte_array_prefix A address (value : bv 64)
      (requested : A -> list (bv 8)) G :
    (∃ x : A, ⌜(8 <= length (requested x))%nat⌝ ∗
      ⌜bv_to_little_endian 8 8 (bv_unsigned value) = take 8 (requested x)⌝ ∗
      (address + 8) ↦ₘ∗ drop 8 (requested x) ∗ G x)%I ⊢
    subsume (address ↦ₘ value) (fun x => address ↦ₘ∗ requested x) G.
  Proof.
    iIntros "Hrule Hvalue".
    iDestruct "Hrule" as (x) "(%Hbound & %Hhead & Htail & HG)".
    iDestruct (mem_mapsto_mapsto_to_byte_array with "Hvalue") as "Hhead".
    iEval (rewrite Hhead) in "Hhead".
    iExists x. iFrame "HG".
    iEval (rewrite -(take_drop 8 (requested x))).
    iApply (mem_mapsto_array_app_combine 8 address (DfracOwn 1)
      (take 8 (requested x)) (drop 8 (requested x)) with "Hhead").
    have Hlength : length (take 8 (requested x)) = 8%nat.
    { rewrite length_take. lia. }
    rewrite Hlength. cbn. iExact "Htail".
  Qed.
  Definition subsume_u64_byte_array_prefix_inst :=
    [instance subsume_u64_byte_array_prefix].

  Lemma byte_array_empty address :
    ⌜0 <= address <= 2 ^ 64⌝ ⊢ address ↦ₘ∗ ([] : list (bv 8)).
  Proof.
    rewrite mem_mapsto_array_eq /mem_mapsto_array_def. cbn.
    iIntros "%Hrange". iExists 1%N.
    iSplit; [done |]. iSplit; [iPureIntro; lia | done].
  Qed.

  Lemma simplify_goal_empty_byte_array address G :
    (⌜0 <= address <= 2 ^ 64⌝ ∗ G)%I ⊢
    simplify_goal (address ↦ₘ∗ ([] : list (bv 8))) G.
  Proof.
    iIntros "[%Hrange HG]". iFrame "HG".
    iApply byte_array_empty. done.
  Qed.
  Definition simplify_goal_empty_byte_array_inst :=
    [instance simplify_goal_empty_byte_array with 0%N].
End word_arrays.

Module WordMatching.
  #[export] Hint Rewrite @length_drop @drop_drop : zesu_indices.
  #[export] Existing Instance subsume_u64_byte_array_prefix_inst | 10.
  #[export] Existing Instance simplify_goal_empty_byte_array_inst | 0.
  #[export] Hint Rewrite @drop_ge using (rewrite ?length_drop; lia)
    : lithium_rewrite isla_coq_rewrite zesu_indices.
  #[export] Hint Rewrite u64_bytes_roundtrip using
    (rewrite length_take ?length_drop; lia)
    : lithium_rewrite isla_coq_rewrite zesu_indices.
End WordMatching.
Print Assumptions subsume_u64_byte_array_prefix.
Print Assumptions byte_array_empty.
Print Assumptions simplify_goal_empty_byte_array.
