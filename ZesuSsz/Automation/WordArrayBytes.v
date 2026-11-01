(* C2: a word array satisfies a wanted byte array.

   NOT exported from `Automation/All.v`. A module opts in by importing
   this one. The rule is sound, tested, and it clears the stall it was
   written for, but installing it everywhere breaks a merged proof, and
   for a reason worth recording rather than working around: see "Why it
   is opt-in" at the end of this file.

   A block loads words and the next boundary wants the same memory as
   bytes. The stall is

     subsume (a ↦ₘ∗ (words : list (bv 64))) (λ x, b ↦ₘ∗ x.2ₗ) (λ x, …)

   and the hand proof answers it in eight lines: convert with
   `mem_mapsto_u64_array_to_bytes`, `replace` one spelling of the address
   with the other by `bv_solve`, then `iExists` the tuple and split. The
   backlog puts about 65 proofs and 380 hand lines behind this shape
   (rows 5, 6, 10, 17, 19).

   The two addresses are left as a side condition rather than required to
   match: the available resource says `bv_unsigned sp + 296` where the
   wanted says `bv_unsigned (sp + 296)`, and that is a `bv_solve` away.

   The continuation comes before the byte equation in the premise, and the
   order matters. With the equation first, the search solves it by taking
   the byte list to be `bytes_of_u64s words` spelled out, and the boundary
   that names those bytes no longer matches. With the continuation first,
   the boundary pins the list and the equation becomes a closed fact about
   the name. *)

Require Import ZesuSsz.Automation.Finish.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import isla.riscv64.riscv64.

(* The rule fires only on a word array the block actually built, which is
   always a literal list. On an abstract array it is still sound but never
   the right move: at the default priority it fired inside
   `WriteSuccessPostWithdrawalsOptional.v` and that module ran out of
   memory against its 6 GiB job cap, and moving it last instead broke the
   tail-fields segment, whose hand proof takes the same subsumption. The
   shape guard settles both. *)
Class ZesuConcreteWords (words : list (bv 64)) : Prop :=
  zesu_concrete_words : True.
Global Instance zesu_concrete_words_cons word words :
  ZesuConcreteWords (word :: words) := I.

Set Default Proof Using "Type".

Section word_array_bytes.
  Context `{!islaG Sigma} `{!threadG}.

  Lemma subsume_mem_array_u64_as_bytes A (available wanted : Z) q
      (words : list (bv 64)) `{!ZesuConcreteWords words}
      (bytes : A → list (bv 8)) G :
    (⌜available = wanted⌝ ∗
     ∃ x : A, G x ∗ ⌜bytes x = IslarisMemory.bytes_of_u64s words⌝)%I ⊢
    subsume (available ↦ₘ{q}∗ words) (fun x => wanted ↦ₘ{q}∗ bytes x) G.
  Proof.
    iIntros "(%Haddress & %x & HG & %Hbytes) Hwords".
    iExists x. rewrite Hbytes -Haddress.
    iSplitL "Hwords"; last done.
    by iApply IslarisMemory.mem_mapsto_u64_array_to_bytes.
  Qed.

  Definition subsume_mem_array_u64_as_bytes_inst :=
    [instance subsume_mem_array_u64_as_bytes].
  Global Existing Instance subsume_mem_array_u64_as_bytes_inst.

End word_array_bytes.

(* Why it is opt-in.

   With the rule installed, the eight hand lines that
   `WriteSuccessExactTailFieldsThirdSegment.v` spends on this subsumption
   have nothing left to do, so they have to go; and once they are gone the
   rule's own side condition surfaces as

     writeSuccessExactTailOptional159b0Bytes witness
       = [Z_to_bv 8 (Z.land (bv_unsigned (writeSuccessPostWord … 10)) …); …]

   -- the boundary's name for the bytes against the bytes the block is
   holding. That is not a reduction. `cbn`, `vm_compute`, `reflexivity`
   and `done` all fail on it, with or without unfolding the definition;
   it is the representation lemma the plan's WP6 lists as a frontier item
   rather than a rule.

   A generated module does not meet it: WP5 states the boundary as the
   bytes the block holds, and the equation never arises. So the rule waits
   for its first generated caller instead of being forced on a hand proof
   that names its arrays differently. *)
