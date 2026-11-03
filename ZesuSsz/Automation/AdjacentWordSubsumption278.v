Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Automation.AdjacentWordResources140.
Require Import isla.riscv64.riscv64.
Require Import stdpp.bitvector.definitions.
From iris.algebra Require Import dfrac.
From Coq Require Import List NArith ZArith.

Section adjacent_word_subsumption.
  Context `{!islaG Sigma}.
  Lemma subsume_adjacent_words A (base wanted : Z) (q : dfrac)
      (n m : nat) (low : bv (8 * N.of_nat n))
      (bytes : list (bv 8)) (G : A -> iProp Sigma) :
    (⌜base = wanted⌝ ∗
     ∃ (x : A) (high : bv (8 * N.of_nat m)),
       (base + Z.of_nat n)%Z ↦ₘ{q} high ∗
       ⌜bytes = bv_to_little_endian (Z.of_nat n) 8 (bv_unsigned low) ++
          bv_to_little_endian (Z.of_nat m) 8 (bv_unsigned high)⌝ ∗ G x)%I
    ⊢ subsume (base ↦ₘ{q} low) (fun _ : A => wanted ↦ₘ{q}∗ bytes) G.
  Proof.
    iIntros "(%Haddress & %x & %high & Hhigh & %Hbytes & HG) Hlow".
    iExists x. iFrame "HG". rewrite Hbytes. rewrite -Haddress.
    iApply (adjacent_words_to_bytes140 Sigma _ q base (base + Z.of_nat n)%Z
      n m low high eq_refl with "Hlow Hhigh").
  Qed.
  Definition subsume_adjacent_words_inst := [instance subsume_adjacent_words].
End adjacent_word_subsumption.

Ltac adjacent_word_counts low bytes continuation :=
  let low_type := type of low in
  lazymatch low_type with
  | bv ?width =>
      tryif has_evar width then fail 1 "The word width contains an evar." else idtac;
      tryif is_closed_term width then idtac else fail 1 "The word width is symbolic.";
      let width := eval vm_compute in width in
      let whole := eval cbn [List.length] in (List.length bytes) in
      tryif has_evar whole then fail 1 "The array length contains an evar." else idtac;
      tryif is_closed_term whole then idtac else fail 1 "The array length is symbolic.";
      let n := eval vm_compute in (Nat.div (N.to_nat width) 8) in
      let m := eval vm_compute in (whole - n)%nat in
      let permitted := eval vm_compute in
        (N.eqb width (8 * N.of_nat n) && Nat.ltb 0 n && Nat.ltb 0 m)%bool in
      lazymatch permitted with
      | true => continuation n m
      | false => fail 1 "The target does not require two positive whole-byte words."
      end
  end.

#[export] Hint Extern 90
  (Subsume (mem_mapsto ?base ?q ?low)
    (fun _ : ?A => mem_mapsto_array ?wanted ?q ?bytes)) =>
  tryif has_evar low then fail 1 "The available word contains an evar." else idtac;
  tryif has_evar bytes then fail 1 "The target bytes contain an evar." else idtac;
  adjacent_word_counts low bytes
    ltac:(fun n m => apply (subsume_adjacent_words_inst A base wanted q n m low bytes))
  : typeclass_instances.
