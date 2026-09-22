(* Candidate C2 rule: a word array satisfies a wanted byte array.

   The stall is
     subsume (a ↦ₘ∗ (words : list (bv 64)))
             (λ x, b ↦ₘ∗ x.2ₗ) (λ x, …)
   and the hand proof answers it with `mem_mapsto_u64_array_to_bytes`,
   a `replace … by bv_solve` to reconcile the two spellings of the
   address, and an `iExists` for the tuple. Eight lines, and the backlog
   puts about 65 proofs and 380 lines behind this shape.

   The address is left as a side condition: the available resource says
   `bv_unsigned sp + 296` and the wanted says `bv_unsigned (sp + 296)`,
   which is a `bv_solve` away. *)

Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import isla.riscv64.riscv64.

Section word_array_bytes.
  Context `{!islaG Sigma} `{!threadG}.

  Lemma subsume_mem_array_u64_as_bytes A (available wanted : Z) q
      (words : list (bv 64)) (bytes : A → list (bv 8)) G :
    (⌜available = wanted⌝ ∗
     ∃ x : A, ⌜bytes x = IslarisMemory.bytes_of_u64s words⌝ ∗ G x)%I ⊢
    subsume (available ↦ₘ{q}∗ words) (fun x => wanted ↦ₘ{q}∗ bytes x) G.
  Proof.
    iIntros "(%Haddress & %x & %Hbytes & HG) Hwords".
    iExists x. rewrite Hbytes -Haddress.
    iSplitL "Hwords"; last done.
    by iApply IslarisMemory.mem_mapsto_u64_array_to_bytes.
  Qed.

  Definition subsume_mem_array_u64_as_bytes_inst :=
    [instance subsume_mem_array_u64_as_bytes].
  Global Existing Instance subsume_mem_array_u64_as_bytes_inst.

End word_array_bytes.
