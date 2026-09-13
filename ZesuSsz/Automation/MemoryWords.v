Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.

(* An unknown prefix determines the requested word. The caller retains
   the rest of the region through the subsumption continuation. *)
Lemma subsume_mem_uninit_word `{!islaG Sigma}
    (A : Type) (address target count : Z) (value : A -> bv 64)
    (G : A -> iProp Sigma)
    `{!BvSolve (address = target /\ 8 <= count)%Z} :
  (∀ word : bv 64,
    (address + 8)%Z ↦ₘ? (count - 8)%Z -∗
    ∃ x : A, ⌜value x = word⌝ ∗ G x) ⊢
  subsume (address ↦ₘ? count) (fun x => target ↦ₘ value x) G.
Proof.
  unfold BvSolve in *.
  match goal with Hrange : address = target /\ _ |- _ =>
    destruct Hrange as [<- Hcount]
  end.
  iIntros "Hcontinuation Hmemory".
  iDestruct (mem_mapsto_uninit_split 8 with "Hmemory")
    as "[Hword Htail]"; first lia.
  iDestruct (mem_mapsto_uninit_to_mapsto with "Hword")
    as (width word ->) "Hword".
  iDestruct ("Hcontinuation" $! word with "Htail")
    as (x) "[%Hvalue Hcontinuation]".
  iExists x. rewrite Hvalue. iFrame "Hword".
  iExact "Hcontinuation".
Qed.
Print Assumptions subsume_mem_uninit_word.

Definition subsume_mem_uninit_word_inst := [instance @subsume_mem_uninit_word].
Global Existing Instance subsume_mem_uninit_word_inst | 80.
