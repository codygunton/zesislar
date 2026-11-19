Require Import isla.riscv64.riscv64.
From Coq Require Import ZArith.
Require Import SailStdpp.MachineWord.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* The cursor range premise before the requested count was restated at the
   requested element type: linear arithmetic over the fact as stated. *)
Ltac previous_cursor_range_premise :=
  lazymatch goal with
  | |- ((?lower <= ?address < ?lower + _ * Z.of_N (?width `div` 8)) \/ _)%Z =>
      match goal with
      | Hrange : (lower <= address < _)%Z |- _ =>
          left;
          let stride := eval vm_compute in (Z.of_N (width `div` 8)) in
          change (Z.of_N (width `div` 8)) with stride;
          clear - Hrange; zesu_lia
      end
  end.

Section cursor_tests.
  Context `{!islaG Sigma} `{!threadG}.

  (* The array's elements are `bv (Z_idx 8)`; the range fact counts them at
     `bv 8`. The two lengths are equal by computation only. *)
  Lemma cursor_range_element_type (P a : Z) (L : list (bv (MachineWord.Z_idx 8)))
      (Hrange : P <= a < P + Z.of_nat (@length (bv 8) L)) :
    FindHypEqual (FICMemMapstoSemantic a) (P ↦ₘ∗ L)
      (mem_mapsto_kind_prop a (MKArray _ P L)) (P ↦ₘ∗ L).
  Proof.
    Fail apply tac_mem_mapsto_array_eq; previous_cursor_range_premise.
    assert_succeeds (apply tac_mem_mapsto_array_eq;
      ZesuSsz.Automation2.RegisterArrayCursor.zesu_cursor_range_premise).
    typeclasses eauto.
  Qed.

  (* The fact stated at the requested element type keeps the original
     path. *)
  Lemma cursor_range_same_type (P a : Z) (L : list (bv 8))
      (Hrange : P <= a < P + Z.of_nat (length L)) :
    FindHypEqual (FICMemMapstoSemantic a) (P ↦ₘ∗ L)
      (mem_mapsto_kind_prop a (MKArray _ P L)) (P ↦ₘ∗ L).
  Proof.
    assert_succeeds (apply tac_mem_mapsto_array_eq; previous_cursor_range_premise).
    apply tac_mem_mapsto_array_eq.
    ZesuSsz.Automation2.RegisterArrayCursor.zesu_cursor_range_premise.
  Qed.

  (* An address past the counted elements is refused. *)
  Lemma cursor_range_outside (P a : Z) (L : list (bv (MachineWord.Z_idx 8)))
      (Hrange : P <= a < P + Z.of_nat (@length (bv 8) L) + 1) : True.
  Proof.
    Fail assert (Hfind : FindHypEqual (FICMemMapstoSemantic a) (P ↦ₘ∗ L)
      (mem_mapsto_kind_prop a (MKArray _ P L)) (P ↦ₘ∗ L)) by
      (apply tac_mem_mapsto_array_eq;
       ZesuSsz.Automation2.RegisterArrayCursor.zesu_cursor_range_premise).
    exact I.
  Qed.
End cursor_tests.
