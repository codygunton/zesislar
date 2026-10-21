Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.RawWordArrayWitness.
Require Import ZesuSsz.Automation.Switches.WordArrayHandoff.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import isla.riscv64.riscv64.
Import ListNotations.
Open Scope Z_scope.

Lemma raw_array_pair_positive `{!islaG Sigma} `{!threadG}
 (base : Z) (low high : bv 64) :
 base ↦ₘ low -∗ (base+8) ↦ₘ high -∗
 ∃ bytes : list (bv 8), base ↦ₘ∗ bytes ∗ ⌜bytes =
 bv_to_little_endian 8 8 (bv_unsigned low) ++
 bv_to_little_endian 8 8 (bv_unsigned high)⌝.
Proof.
 iIntros "Hlow Hhigh". iExists _.
 zesu_raw_array_witness_if_enabled.
 iSplitL "Hlow Hhigh".
 - iDestruct (mem_mapsto_mapsto_to_byte_array_len 8 base (DfracOwn 1) low with "Hlow") as "Hlow".
   iDestruct (mem_mapsto_mapsto_to_byte_array_len 8 (base+8) (DfracOwn 1) high with "Hhigh") as "Hhigh".
   iApply (mem_mapsto_array_app_combine_at 8 base (DfracOwn 1)
     (bv_to_little_endian 8 8 (bv_unsigned low))
     (bv_to_little_endian 8 8 (bv_unsigned high)) 8 with "Hlow").
   { rewrite length_bv_to_little_endian; lia. }
   cbn. iExact "Hhigh".
 - iPureIntro. reflexivity.
Qed.
Print Assumptions raw_array_pair_positive.

Lemma raw_array_concrete_refuses `{!islaG Sigma} `{!threadG}
 (base : Z) (low high : bv 64) :
 base ↦ₘ low -∗ (base+8) ↦ₘ high -∗ base ↦ₘ∗ [(0%bv : bv 8)] -∗
 base ↦ₘ∗ [(0%bv : bv 8)] ∗ True.
Proof.
 iIntros "Hlow Hhigh Harray".
 Fail zesu_raw_array_witness_if_enabled.
 iFrame "Harray".
Qed.
Print Assumptions raw_array_concrete_refuses.

Lemma raw_array_wrong_base_refuses `{!islaG Sigma} `{!threadG}
 (base : Z) (low high : bv 64) (seed : list (bv 8)) :
 (base+1) ↦ₘ low -∗ (base+9) ↦ₘ high -∗ base ↦ₘ∗ seed -∗
 ∃ bytes : list (bv 8), base ↦ₘ∗ bytes ∗ True.
Proof.
 iIntros "Hlow Hhigh Harray". iExists _.
 Fail zesu_raw_array_witness_if_enabled.
 iFrame "Harray".
Qed.
Print Assumptions raw_array_wrong_base_refuses.

Lemma raw_array_nonadjacent_refuses `{!islaG Sigma} `{!threadG}
 (base : Z) (low high : bv 64) (seed : list (bv 8)) :
 base ↦ₘ low -∗ (base+16) ↦ₘ high -∗ base ↦ₘ∗ seed -∗
 ∃ bytes : list (bv 8), base ↦ₘ∗ bytes ∗ True.
Proof.
 iIntros "Hlow Hhigh Harray". iExists _.
 Fail zesu_raw_array_witness_if_enabled.
 iFrame "Harray".
Qed.
Print Assumptions raw_array_nonadjacent_refuses.

Lemma raw_array_ambiguous_refuses `{!islaG Sigma} `{!threadG}
 (base : Z) (low high1 high2 : bv 64) (seed : list (bv 8)) :
 base ↦ₘ low -∗ (base+8) ↦ₘ high1 -∗ (base+8) ↦ₘ high2 -∗ base ↦ₘ∗ seed -∗
 ∃ bytes : list (bv 8), base ↦ₘ∗ bytes ∗ True.
Proof.
 iIntros "Hlow Hhigh1 Hhigh2 Harray". iExists _.
 Fail zesu_raw_array_witness_if_enabled.
 iFrame "Harray".
Qed.
Print Assumptions raw_array_ambiguous_refuses.
