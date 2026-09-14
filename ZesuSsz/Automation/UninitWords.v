Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.UninitRegions.
Require Import isla.riscv64.riscv64.

(* Reveal the stored word without assigning it a new value. *)
Lemma subsume_scratch_word `{!islaG Sigma} A a1 a2 count
    (value : A -> bv 64) G
    `{!ZesuRegionBounds (a1 = a2 /\ 8 <= count)%Z} :
  (∀ word : bv 64, (a2 + 8) ↦ₘ? (count - 8) -∗
    ∃ x, ⌜word = value x⌝ ∗ G x) ⊢
  subsume (a1 ↦ₘ? count) (fun x : A => a2 ↦ₘ value x) G.
Proof.
  have Hbounds : (a1 = a2 /\ 8 <= count)%Z.
  { exact zesu_region_bounds_proof. }
  destruct Hbounds as [-> Hcount]. iIntros "Hnext Hscratch".
  iDestruct (mem_mapsto_uninit_split 8 with "Hscratch") as "[Hword Htail]"; first lia.
  iDestruct (mem_mapsto_uninit_to_mapsto with "Hword") as (bits word Hbits) "Hword".
  change (bits = 64%N) in Hbits. subst bits.
  iDestruct ("Hnext" $! word with "Htail") as (x ->) "HG".
  iExists x. iFrame.
Qed.
Print Assumptions subsume_scratch_word.
Definition subsume_scratch_word_inst := [instance @subsume_scratch_word].
Global Existing Instance subsume_scratch_word_inst | 80.

Lemma subsume_mem_word_uninit_exact `{!islaG Sigma} A (a1 a2 : Z) n
    (word : bv n) count G
    `{!ZesuRegionBounds (a1 = a2 /\ count = Z.of_N (n `div` 8)%N)%Z} :
  (∃ x : A, G x) ⊢
    subsume (a1 ↦ₘ word) (fun _ : A => a2 ↦ₘ? count) G.
Proof.
  iDestruct 1 as (x) "HG". iIntros "Hword".
  have Hbounds : (a1 = a2 /\ count = Z.of_N (n `div` 8)%N)%Z
    by exact zesu_region_bounds_proof.
  destruct Hbounds as [-> ->].
  iExists x. iFrame "HG".
  iApply (mem_mapsto_mapsto_to_uninit with "Hword").
Qed.
Definition subsume_mem_word_uninit_exact_inst := [instance @subsume_mem_word_uninit_exact].
Global Existing Instance subsume_mem_word_uninit_exact_inst | 0.
Print Assumptions subsume_mem_word_uninit_exact.
