Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.WordArrayBytes.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import isla.riscv64.riscv64.

(* The rule is not exported from `Automation.All`; this module imports it
   directly, which is how a generated module will take it.

   The rule fires only on a word array the block actually built, so the
   tests use a literal list, as a segment does. *)

(* The instance itself: a word array hands over as the bytes it holds,
   with the two spellings of the address reconciled by the side
   condition. *)
Lemma test_word_array_as_bytes_instance `{!islaG Sigma} `{!threadG}
    (base : Z) (first second : bv 64) :
  base ↦ₘ∗ [first; second] -∗
  (∃ _ : unit, base ↦ₘ∗ IslarisMemory.bytes_of_u64s [first; second]).
Proof.
  iIntros "Hwords".
  iDestruct (subsume_mem_array_u64_as_bytes unit base base (DfracOwn 1)
    [first; second] (fun _ => IslarisMemory.bytes_of_u64s [first; second])
    (fun _ => True)%I with "[] Hwords") as (x) "[Hbytes _]".
  { iSplit; [done |]. iExists tt. iSplit; [done | done]. }
  iExists tt. iFrame.
Qed.
Print Assumptions test_word_array_as_bytes_instance.

(* The same handover reached by the block automation, in the shape a
   segment meets it: the wanted byte list is the existential, and the
   instance is what tells the search what it must be. *)
Lemma test_word_array_as_bytes_matching `{!islaG Sigma} `{!threadG}
    (base : Z) (first second : bv 64) :
  base ↦ₘ∗ [first; second] -∗
  (∃ bytes : list (bv 8), base ↦ₘ∗ bytes ∗
     ⌜bytes = IslarisMemory.bytes_of_u64s [first; second]⌝).
Proof. iStartProof. iIntros "Hwords". zesu_run. Qed.
Print Assumptions test_word_array_as_bytes_matching.

(* An abstract array is left alone: the guard is what keeps the rule from
   firing where it is sound but never wanted. *)
Lemma test_word_array_abstract_untouched `{!islaG Sigma} `{!threadG}
    (base : Z) (words : list (bv 64)) :
  base ↦ₘ∗ words -∗ base ↦ₘ∗ words.
Proof. iStartProof. iIntros "Hwords". zesu_run. Qed.
Print Assumptions test_word_array_abstract_untouched.
