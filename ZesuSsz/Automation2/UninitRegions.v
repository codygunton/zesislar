Require ZesuSsz.Automation.UninitRegions.
Require Import isla.riscv64.riscv64.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation2.ByteArrayLengths.
Require Import ZesuSsz.Automation2.RangeFacts.
Require ZesuSsz.Contracts.IslarisMemory.
Require ZesuSsz.Automation2.ContextCollection.
Require ZesuSsz.Automation2.PureFacts.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

(* Reject unrelated regions without expanding the caller's validity predicates.
   The upstream rules and their resource continuations remain unchanged. *)

Ltac zesu_nat_literal number :=
  lazymatch number with
  | O => idtac
  | S ?rest => zesu_nat_literal rest
  end.

Ltac zesu_region_bounds_legacy :=
  cbv [mapRamBase mapRamSize machineRamEnd defaultMap] in *;
  repeat lazymatch goal with
  | |- context [length (take ?count ?values)] =>
      let valuesType := type of values in
      constr_eq valuesType (list (bv 64));
      rewrite length_take;
      lazymatch goal with
      | Hlength : length values = ?size |- _ => rewrite Hlength
      | Hlength : ?size = length values |- _ => rewrite <- Hlength
      end
  end;
  first [repeat match goal with H : _ |- _ => clear H end; lia |
    repeat match goal with
    | H : ?T |- _ =>
      lazymatch T with
      | Z.le _ _ => fail
      | Z.lt _ _ => fail
      | @eq Z _ _ => fail
      | @eq nat (length _) ?number =>
          tryif zesu_nat_literal number then fail else clear H
      | @eq nat ?number (length _) =>
          tryif zesu_nat_literal number then fail else clear H
      | _ => clear H
      end
    end;
    bv_solve].

(* Bounds search uses only facts connected to the candidate region. *)
Ltac zesu_region_address_carries base address :=
  first [lazymatch address with context[base] => idtac end |
    let rec carries term :=
      first [assert_fails (has_evar term);
        assert_fails (ZesuSsz.Automation2.VmClosed.zesu_vm_closed term);
        lazymatch address with context[term] => idtac end |
        lazymatch term with
        | Z.add ?left ?right => first [carries left | carries right]
        | Z.sub ?left ?right => first [carries left | carries right]
        | Z.mul ?left ?right => first [carries left | carries right]
        end] in
    carries base].

Ltac zesu_region_collect base address :=
  let collect := ltac2:(b a |-
    let base := Option.get (Ltac1.to_constr b) in
    let address := Option.get (Ltac1.to_constr a) in
    let original := Control.hyps () in
    List.iter (fun h => let (name, _, _) := h in
      Ltac1.apply
        (Ltac1.ref [@ZesuSsz; @Automation2; @RangeFacts; @zesu_range_project])
        [Ltac1.of_constr constr:(8%nat); Ltac1.of_constr base;
         Ltac1.of_constr address; Ltac1.of_constr base;
         Ltac1.of_constr (Control.hyp name)] Ltac1.run) original) in
  let rec choose_atom term :=
    first [assert_fails (has_evar term);
      assert_fails (ZesuSsz.Automation2.VmClosed.zesu_vm_closed term);
      lazymatch address with context[term] => collect term address end |
      lazymatch term with
      | Z.add ?left ?right => first [choose_atom left | choose_atom right]
      | Z.sub ?left ?right => first [choose_atom left | choose_atom right]
      | Z.mul ?left ?right => first [choose_atom left | choose_atom right]
      end] in
  first [choose_atom base | collect address address].

Ltac zesu_region_selected_facts :=
  repeat match goal with
  | Hlocal := _ |- ?target =>
      lazymatch target with context[Hlocal] => unfold Hlocal in *; clear Hlocal end
  end;
  let choose_atom base address :=
    zesu_region_address_carries base address;
    zesu_region_collect base address in
  lazymatch goal with
  | |- ((?base <= ?address < ?upper)%Z \/ _) => choose_atom base address
  | |- (?base <= ?address <= ?upper)%Z => choose_atom base address
  | |- (?base <= ?address < ?upper)%Z => choose_atom base address
  | |- @eq Z ?base ?address => choose_atom base address
  | |- ?target =>
      let rec collect target :=
        lazymatch target with
        | ?left /\ ?right => collect left; collect right
        | ?left \/ ?right => collect left; collect right
        | @eq Z ?left ?right => zesu_region_collect left right
        | Z.le ?left ?right => zesu_region_collect left right
        | Z.lt ?left ?right => zesu_region_collect left right
        end in
      collect target
  end;
  ltac2:(ZesuSsz.Automation2.RangeFacts.zesu_range_isolate ()).

(* A bound can sit inside a folded hypothesis, such as a contract's domain
   predicate. The fact selection keeps only arithmetic facts, so split such
   hypotheses first; the split is local to this side condition. *)
Ltac zesu_region_bounds := once (
  ZesuSsz.Automation2.PureFacts.zesu_split_folded_pure;
  zesu_region_selected_facts;
  first [
    ZesuSsz.Automation2.ByteArrayLengths.zesu_byte_array_bound_goal_if_enabled;
    first [solve [lia] |
      ZesuSsz.Automation2.ByteArrayLengths.zesu_byte_array_lengths_if_enabled; solve [lia | bv_solve]]
  | ZesuSsz.Automation2.UninitRegions.zesu_region_bounds_legacy]).

(* Its own class: the frozen core keeps a priority-0 extern on its class,
   and with a shared class that extern ran its legacy bound solver on every
   side condition that this rule refused. *)
Class ZesuRegionBounds (P : Prop) : Prop := zesu_region_bounds_proof : P.
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

(* The contract's fallback rule for an uninitialized region raises the
   containment as an obligation. Refuse it when the facts already show the
   containment fails, so the search does not commit to a false goal. The
   class carries no proof; its instance only checks the refutation. *)
Class ZesuRegionNotRefuted (P : Prop) : Prop := zesu_region_not_refuted : True.
Ltac zesu_region_refute :=
  first [zesu_region_bounds |
    ZesuSsz.Automation2.ContextCollection.zesu_solve_goal_selected
      ("region.refute"%string) ltac:(first [lia | bv_solve])].
Global Hint Extern 0 (ZesuRegionNotRefuted (0 <= ?n2 /\ ?a1 <= ?a2 /\ ?a2 + ?n2 <= ?a1 + ?n1)%Z) =>
  (assert_fails (assert (n2 < 0 \/ a2 < a1 \/ a1 + n1 < a2 + n2)%Z by zesu_region_refute);
   exact I) : typeclass_instances.

Lemma subsume_mem_uninit_region_checked `{!islaG Sigma} A a1 a2 n1 n2 G
    `{!ZesuRegionNotRefuted (0 <= n2 /\ a1 <= a2 /\ a2 + n2 <= a1 + n1)%Z} :
  ((⌜(0 <= n2 /\ a1 <= a2 /\ a2 + n2 <= a1 + n1)%Z⌝ ∗
    (a1 ↦ₘ? (a2 - a1) -∗
     (a2 + n2) ↦ₘ? (a1 + n1 - (a2 + n2)) -∗
     ∃ x : A, G x))%I)
  ⊢ subsume (a1 ↦ₘ? n1) (fun _ : A => a2 ↦ₘ? n2) G.
Proof. exact (ZesuSsz.Contracts.IslarisMemory.subsume_mem_uninit_region A a1 a2 n1 n2 G). Qed.

Definition subsume_mem_uninit_region_checked_inst :=
  [instance @subsume_mem_uninit_region_checked].
Global Existing Instance subsume_mem_uninit_region_checked_inst | 100.
Global Remove Hints ZesuSsz.Contracts.IslarisMemory.subsume_mem_uninit_region_inst : typeclass_instances.

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

Lemma subsume_mem_word_address `{!islaG Sigma} A (a1 a2 : Z) n (word : bv n) G
    `{!ZesuRegionBounds (a1 = a2)%Z} :
  (∃ x : A, G x) ⊢ subsume (a1 ↦ₘ word) (fun _ : A => a2 ↦ₘ word) G.
Proof.
  iDestruct 1 as (x) "HG". iIntros "Hword".
  have -> : a1 = a2 by exact zesu_region_bounds_proof.
  iExists x. iFrame.
Qed.
Definition subsume_mem_word_address_inst := [instance @subsume_mem_word_address].

Global Existing Instance subsume_mem_word_address_inst | 1.
Print Assumptions subsume_mem_word_address.
