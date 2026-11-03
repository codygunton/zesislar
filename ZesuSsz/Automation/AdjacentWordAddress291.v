Require Export ZesuSsz.Automation.AdjacentFractionalFinder285.
Require Import ZesuSsz.Automation.AdjacentWordResources140.
Require Import ZesuSsz.Automation.AdjacentWordSubsumption278.
Require Import isla.riscv64.riscv64.
From lithium Require Import instances.
Require Import stdpp.bitvector.definitions.
From iris.algebra Require Import dfrac.
From Coq Require Import List NArith ZArith.
Import ListNotations.
Set Default Proof Mode "Classic".

Section address_independent_selection.
  Context `{!islaG Sigma}.
  Lemma subsume_adjacent_address291 A (base wanted : Z) (q : dfrac)
      (n m : nat) (low : bv (8 * N.of_nat n))
      (high : bv (8 * N.of_nat m)) (bytes : list (bv 8))
      (G : A -> iProp Sigma) :
    (⌜base = wanted⌝ ∗ ∃ x : A,
      find_in_context
        (FindDirect (fun next : Z => (next ↦ₘ{q} high)%I))
        (fun next =>
          ⌜next = (base + Z.of_nat n)%Z⌝ ∗
          ⌜bytes = bv_to_little_endian (Z.of_nat n) 8 (bv_unsigned low) ++
            bv_to_little_endian (Z.of_nat m) 8 (bv_unsigned high)⌝ ∗ G x))%I
    ⊢ subsume (base ↦ₘ{q} low) (fun _ : A => wanted ↦ₘ{q}∗ bytes) G.
  Proof.
    rewrite /find_in_context /FindDirect /=.
    iIntros "(%Haddress & %x & %next & Hhigh & %Hadjacent & %Hbytes & HG) Hlow".
    iExists x. iFrame "HG". rewrite Hbytes. rewrite -Haddress.
    iApply (adjacent_words_to_bytes140 Sigma _ q base next
      n m low high Hadjacent with "Hlow Hhigh").
  Qed.
  Definition subsume_adjacent_address291_inst := [instance subsume_adjacent_address291].
End address_independent_selection.

#[export] Hint Extern 80
  (Subsume (mem_mapsto ?base ?q ?low)
    (fun _ : ?A => mem_mapsto_array ?wanted ?q ?bytes)) =>
    tryif has_evar low then fail 1 "The available word contains an evar." else idtac;
    tryif has_evar bytes then fail 1 "The target bytes contain an evar." else idtac;
    adjacent_word_counts low bytes ltac:(fun n m =>
      let next_byte := eval cbn [List.nth_error] in (List.nth_error bytes n) in
      lazymatch next_byte with
      | Some (bv_extract 0 8 ?high) =>
          let actual_type := type of high in
          let required_type := constr:(bv (8 * N.of_nat m)) in
          unify actual_type required_type;
          apply (subsume_adjacent_address291_inst A base wanted q n m low high bytes)
      end)
  : typeclass_instances.
