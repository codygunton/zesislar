Require Import isla.riscv64.riscv64.

(* Reject unrelated regions without expanding the caller's validity predicates.
   The upstream rules and their resource continuations remain unchanged. *)
Class ZesuRegionBounds (P : Prop) : Prop := zesu_region_bounds_proof : P.

Ltac zesu_region_bounds :=
  first [repeat match goal with H : _ |- _ => clear H end; lia |
    repeat match goal with
    | H : ?T |- _ =>
      lazymatch T with
      | Z.le _ _ => fail
      | Z.lt _ _ => fail
      | @eq Z _ _ => fail
      | _ => clear H
      end
    end;
    timeout 2 bv_solve].

Global Hint Extern 0 (ZesuRegionBounds ?P) =>
  (change P; zesu_region_bounds) : typeclass_instances.

Inductive ZesuMemRegionSearch (address : Z) : Set :=.
Definition find_mem_region_inst `{!islaG Sigma} address :=
  [instance find_in_context_mem_mapsto_semantic address with ZesuMemRegionSearch address].
Global Existing Instance find_mem_region_inst | 5.

Lemma find_mem_region_word `{!islaG Sigma} address a1 n (word : bv n) a2 :
  a1 = a2 ->
  FindHypEqual (ZesuMemRegionSearch address) (a1 ↦ₘ word)
    (mem_mapsto_kind_prop a2 (MKMapsTo n word)) (a1 ↦ₘ word).
Proof. by move => ->. Qed.
Global Hint Extern 0 (FindHypEqual (ZesuMemRegionSearch _) (_ ↦ₘ _)
    (mem_mapsto_kind_prop _ _) _) =>
  (apply find_mem_region_word; zesu_region_bounds) : typeclass_instances.

Lemma find_mem_region_array `{!islaG Sigma} address a1 a2 n (bytes : list (bv n)) :
  a1 <= address < a1 + length bytes * Z.of_N (n `div` 8)%N \/ a1 = address ->
  FindHypEqual (ZesuMemRegionSearch address) (a1 ↦ₘ∗ bytes)
    (mem_mapsto_kind_prop a2 (MKArray n a1 bytes)) (a1 ↦ₘ∗ bytes).
Proof. done. Qed.
Global Hint Extern 0 (FindHypEqual (ZesuMemRegionSearch _) (_ ↦ₘ∗ _)
    (mem_mapsto_kind_prop _ _) _) =>
  (apply find_mem_region_array; zesu_region_bounds) : typeclass_instances.

Lemma find_mem_region_uninit `{!islaG Sigma} address a1 a2 count :
  a1 <= address < a1 + count \/ a1 = address ->
  FindHypEqual (ZesuMemRegionSearch address) (a1 ↦ₘ? count)
    (mem_mapsto_kind_prop a2 (MKUninit a1 count)) (a1 ↦ₘ? count).
Proof. done. Qed.
Global Hint Extern 0 (FindHypEqual (ZesuMemRegionSearch _) (_ ↦ₘ? _)
    (mem_mapsto_kind_prop _ _) _) =>
  (apply find_mem_region_uninit; zesu_region_bounds) : typeclass_instances.

Lemma find_mem_region_mmio `{!islaG Sigma} address a1 a2 count :
  a1 <= address <= a1 + count ->
  FindHypEqual (ZesuMemRegionSearch address) (mmio_range a1 count)
    (mem_mapsto_kind_prop a2 (MKMMIO a1 count)) (mmio_range a1 count).
Proof. done. Qed.
Global Hint Extern 0 (FindHypEqual (ZesuMemRegionSearch _) (mmio_range _ _)
    (mem_mapsto_kind_prop _ _) _) =>
  (apply find_mem_region_mmio; zesu_region_bounds) : typeclass_instances.

Lemma subsume_uninit_region `{!islaG Sigma} A a1 a2 n1 n2 G
    `{!ZesuRegionBounds (0 <= n2 /\ a1 <= a2 /\ a2 + n2 <= a1 + n1)%Z} :
  (li_tactic (normalize_bv_wrap (a2 - a1)) (fun m1 => ⌜0 <= m1 < 2 ^ 64⌝ ∗
   li_tactic (normalize_bv_wrap (n1 - n2 - m1)) (fun m2 =>
     ⌜0 <= m2 < 2 ^ 64 /\ n1 < 2 ^ 64⌝ ∗
     (a1 ↦ₘ? m1 -∗ (a2 + n2) ↦ₘ? m2 -∗ ∃ x, G x)))) ⊢
  subsume (a1 ↦ₘ? n1) (fun x : A => a2 ↦ₘ? n2) G.
Proof.
  have Hbounds : BvSolve (0 <= n2 /\ a1 <= a2 /\ a2 + n2 <= a1 + n1)%Z.
  { unfold BvSolve. exact zesu_region_bounds_proof. }
  exact (subsume_mem_uninit_mem_uninit A a1 a2 n1 n2 G).
Qed.
Print Assumptions subsume_uninit_region.

Definition subsume_uninit_region_inst := [instance @subsume_uninit_region].
Global Existing Instance subsume_uninit_region_inst.
Global Remove Hints subsume_mem_uninit_mem_uninit_inst : typeclass_instances.

Lemma subsume_uninit_region_crossing `{!islaG Sigma} A a1 a2 n1 n2 G
    `{!ZesuRegionBounds (0 <= n2 /\ a1 <= a2 /\ a2 <= a1 + n1 /\ a1 + n1 <= a2 + n2)%Z} :
  (li_tactic (normalize_bv_wrap (a2 - a1)) (fun m1 => ⌜0 <= m1 < 2 ^ 64⌝ ∗
   li_tactic (normalize_bv_wrap (n2 - (n1 - m1))) (fun m2 => ⌜0 <= m2 < 2 ^ 64⌝ ∗
   li_tactic (normalize_bv_wrap (a2 + n1 - m1)) (fun m3 =>
     ⌜a2 + n2 < 2 ^ 64 /\ m3 + m2 < 2 ^ 64⌝ ∗
     (a1 ↦ₘ? m1 -∗ m3 ↦ₘ? m2 ∗ ∃ x, G x))))) ⊢
  subsume (a1 ↦ₘ? n1) (fun x : A => a2 ↦ₘ? n2) G.
Proof.
  have Hbounds : BvSolve (0 <= n2 /\ a1 <= a2 /\ a2 <= a1 + n1 /\ a1 + n1 <= a2 + n2)%Z.
  { unfold BvSolve. exact zesu_region_bounds_proof. }
  exact (subsume_mem_uninit_mem_uninit2 A a1 a2 n1 n2 G).
Qed.
Print Assumptions subsume_uninit_region_crossing.

Definition subsume_uninit_region_crossing_inst := [instance @subsume_uninit_region_crossing].
Global Existing Instance subsume_uninit_region_crossing_inst.
Global Remove Hints subsume_mem_uninit_mem_uninit2_inst : typeclass_instances.

Lemma simplify_uninit_empty_hyp `{!islaG Sigma} a n G
    `{!ZesuRegionBounds (n = 0)%Z} :
  G ⊢ simplify_hyp (a ↦ₘ? n) G.
Proof. by iIntros "$ ?". Qed.
Definition simplify_uninit_empty_hyp_inst := [instance @simplify_uninit_empty_hyp with 0%N].
Global Existing Instance simplify_uninit_empty_hyp_inst.
Global Remove Hints simpl_hyp_uninit_0_inst : typeclass_instances.

Lemma simplify_uninit_empty_goal `{!islaG Sigma} a n G
    `{!ZesuRegionBounds (n = 0)%Z} :
  ⌜0 <= a <= 2 ^ 64⌝ ∗ G ⊢ simplify_goal (a ↦ₘ? n) G.
Proof.
  have Hbounds : BvSolve (n = 0)%Z.
  { unfold BvSolve. exact zesu_region_bounds_proof. }
  exact (simpl_goal_uninit_0 a n G).
Qed.
Print Assumptions simplify_uninit_empty_goal.
Definition simplify_uninit_empty_goal_inst := [instance @simplify_uninit_empty_goal with 0%N].
Global Existing Instance simplify_uninit_empty_goal_inst.
Global Remove Hints simpl_goal_uninit_0_inst : typeclass_instances.
