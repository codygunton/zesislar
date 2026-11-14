Require Import ZesuSsz.Automation2.VmClosed.
Require Import ZesuSsz.Automation2.Hooks.
Require Import ZesuSsz.Automation2.PureFacts.
Require Import ZesuSsz.Automation2.ResourceGroups.
Require Import ZesuSsz.Automation2.TracePrefixTail.
From iris.proofmode Require Import environments.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import isla.riscv64.riscv64.
Require SailStdpp.MachineWord.

Section interior_byte_slice.
Context `{!islaG Sigma}.

(* The continuation restores the same bytes after the callee returns. *)
Lemma zesu_byte_array_lend_slice (base : Z) (bytes : list (bv 8))
    (start count : nat) :
  (start + count <= length bytes)%nat ->
  base ↦ₘ∗ bytes -∗
  (base + Z.of_nat start) ↦ₘ∗ take count (drop start bytes) ∗
  ((base + Z.of_nat start) ↦ₘ∗ take count (drop start bytes) -∗
    base ↦ₘ∗ bytes).
Proof.
  iIntros (Hbounds) "Harray".
  iDestruct (mem_mapsto_array_region 8%N base (DfracOwn 1)
    bytes start count with "Harray") as "(Hprefix & Hslice & Hsuffix)"; [done|].
  have Hstride : Z.of_N (8 / 8) = 1%Z by (vm_cast_no_check (eq_refl (1%Z))).
  iEval (rewrite Hstride Z.mul_1_l) in "Hslice Hsuffix".
  iFrame "Hslice". iIntros "Hslice".
  iPoseProof (mem_mapsto_array_app_combine_at 8%N base (DfracOwn 1)
    (take start bytes) (take count (drop start bytes)) start
    with "Hprefix [Hslice]") as "Hfirst".
  { rewrite length_take. lia. }
  { rewrite Hstride Z.mul_1_l. iExact "Hslice". }
  iPoseProof (mem_mapsto_array_app_combine_at 8%N base (DfracOwn 1)
    (take start bytes ++ take count (drop start bytes))
    (drop (start + count) bytes) (start + count)
    with "Hfirst [Hsuffix]") as "Hwhole".
  { rewrite length_app !length_take length_drop. lia. }
  { rewrite Hstride Z.mul_1_l. iExact "Hsuffix". }
  rewrite -drop_drop -app_assoc take_drop take_drop.
  iExact "Hwhole".
Qed.
End interior_byte_slice.
Print Assumptions zesu_byte_array_lend_slice.

Class ZesuStepInteriorByteSlice : Prop := zesu_step_interior_byte_slice : True.

Ltac zesu_byte_slice_start address base :=
  lazymatch address with
  | bv_unsigned (?register + ?offset)%bv =>
      lazymatch base with
      | (bv_unsigned register + ?baseOffset)%Z =>
          let start := ZesuSsz.Automation2.VmClosed.zesu_vm_eval_closed (Z.to_nat (bv_unsigned offset - baseOffset)) in
          constr:(start)
      | _ => constr:(Z.to_nat (address - base))
      end
  | _ => constr:(Z.to_nat (address - base))
  end.

(* The size that a pure fact states for the requested slice, as a value: a
   fact `size = Z.of_nat (length slice)`, or such an equation among the
   conjuncts of a fact that mentions the slice (unfolded at each head). *)
Ltac zesu_byte_slice_size_in fact slice :=
  let fact := eval hnf in fact in
  match fact with
  | ?left /\ _ => zesu_byte_slice_size_in left slice
  | _ /\ ?right => zesu_byte_slice_size_in right slice
  | @eq Z ?size ?measure =>
      let measure := eval cbn in measure in
      lazymatch measure with
      | Z.of_nat (@length _ ?measured) =>
          let measured := eval cbn in measured in
          lazymatch constr:((measured, slice)) with
          | (?same, ?same) => let size := eval cbn in size in constr:(size)
          end
      end
  end.

Ltac zesu_byte_slice_size rest slice :=
  match rest with
  | context[(⌜?size = Z.of_nat (length slice)⌝)%I] => constr:(size)
  | context[@bi_pure _ ?fact] =>
      lazymatch fact with context[slice] => zesu_byte_slice_size_in fact slice end
  end.

(* A closed size is evaluated; any other size is counted as it stands. *)
Ltac zesu_byte_slice_count size :=
  match constr:(tt) with
  | _ => ZesuSsz.Automation2.VmClosed.zesu_vm_eval_closed (Z.to_nat size)
  | _ => constr:(Z.to_nat size)
  end.

(* Bounds of a slice whose start or size is symbolic: the derived facts of
   the context (a callee's consumed count, its input length), slice lengths
   unfolded, sums and differences of words without wrap, and element-type and
   width aliases normalized so that the arithmetic sees one atom per term. *)
Ltac zesu_byte_slice_alias_normalize :=
  repeat match goal with
  | H : context[SailStdpp.MachineWord.MachineWord.Z_idx ?z] |- _ =>
      let v := eval vm_compute in (SailStdpp.MachineWord.MachineWord.Z_idx z) in
      change (SailStdpp.MachineWord.MachineWord.Z_idx z) with v in H
  | |- context[SailStdpp.MachineWord.MachineWord.Z_idx ?z] =>
      let v := eval vm_compute in (SailStdpp.MachineWord.MachineWord.Z_idx z) in
      change (SailStdpp.MachineWord.MachineWord.Z_idx z) with v
  | H : context[@length ?T ?l] |- _ =>
      let T' := eval cbv in T in assert_fails (constr_eq T T');
      change (@length T l) with (@length T' l) in H
  | |- context[@length ?T ?l] =>
      let T' := eval cbv in T in assert_fails (constr_eq T T');
      change (@length T l) with (@length T' l)
  | H : context[@List.nth ?T ?k ?l ?d] |- _ =>
      let T' := eval cbv in T in assert_fails (constr_eq T T');
      change (@List.nth T k l d) with (@List.nth T' k l d) in H
  | |- context[@List.nth ?T ?k ?l ?d] =>
      let T' := eval cbv in T in assert_fails (constr_eq T T');
      change (@List.nth T k l d) with (@List.nth T' k l d)
  end.

(* A hypothesis word convertible to a goal word is restated in the goal's
   form, whatever alias it was elaborated at. *)
Ltac zesu_byte_slice_goal_atoms :=
  repeat match goal with
  | |- context[@bv_unsigned ?n ?a] =>
      match goal with
      | H : context[@bv_unsigned ?m ?b] |- _ =>
          assert_fails (constr_eq a b);
          assert_fails (has_evar b);
          unify (@bv_unsigned m b) (@bv_unsigned n a);
          change (@bv_unsigned m b) with (@bv_unsigned n a) in H
      end
  end.

Ltac zesu_byte_slice_unsigned_range n x :=
  assert_fails (has_evar x);
  lazymatch goal with
  | _ : (0 <= @bv_unsigned n x < _)%Z |- _ => fail
  | _ => pose proof (bv_unsigned_in_range n x)
  end.

Ltac zesu_byte_slice_unsigned_ranges :=
  repeat match goal with
  | |- context[@bv_unsigned ?n ?x] => zesu_byte_slice_unsigned_range n x
  | _ : context[@bv_unsigned ?n ?x] |- _ => zesu_byte_slice_unsigned_range n x
  end.

(* A derived fact stated under premises: each premise the context shows,
   directly or by arithmetic, is discharged. *)
Ltac zesu_byte_slice_discharge_premises :=
  repeat match goal with
  | H : ?P -> ?Q |- _ =>
      lazymatch type of P with Prop => idtac end;
      let Hp := fresh "Hpremise" in
      assert (Hp : P) by (first [assumption | lia]);
      specialize (H Hp); clear Hp
  end;
  repeat match goal with H : _ /\ _ |- _ => destruct H end.

Ltac zesu_byte_slice_moduli :=
  repeat match goal with
  | H : context[bv_modulus ?n] |- _ =>
      let v := eval vm_compute in (bv_modulus n) in change (bv_modulus n) with v in H
  | |- context[bv_modulus ?n] =>
      let v := eval vm_compute in (bv_modulus n) in change (bv_modulus n) with v
  end.

Ltac zesu_byte_slice_bound_arith :=
  ZesuSsz.Automation.PureFacts.zesu_saturate_derived_facts;
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  repeat match goal with
  | H : context[length (take _ _)] |- _ => rewrite length_take in H
  | H : context[length (drop _ _)] |- _ => rewrite length_drop in H
  end;
  rewrite ?length_take ?length_drop ?bv_add_unsigned ?bv_sub_unsigned; unfold bv_wrap;
  zesu_byte_slice_unsigned_ranges;
  zesu_byte_slice_alias_normalize;
  zesu_byte_slice_moduli;
  zesu_byte_slice_discharge_premises;
  zesu_byte_slice_goal_atoms;
  repeat match goal with
  | |- context[(?a mod ?m)%Z] => rewrite (Z.mod_small a m); [|lia]
  end;
  lia.

Ltac zesu_lend_interior_byte_slice :=
  zesu_expose_environment_alias;
  lazymatch goal with
  | |- envs_entails _ (@bi_exist _ ?T ?body) =>
      let witness := zesu_tuple_witness T in
      let opened := eval cbv beta iota delta [li_fst] in (body witness) in
      lazymatch opened with
      | ((?address ↦ₘ∗ ?slice) ∗ ?rest)%I =>
          has_evar slice;
          assert_fails (has_evar address);
          let size := zesu_byte_slice_size rest slice in
          let count := zesu_byte_slice_count size in
          assert_fails (has_evar count);
              iMatchHyp ltac:(fun Harray resource =>
                lazymatch resource with
                | (?base ↦ₘ∗ ?bytes)%I =>
                    lazymatch type of bytes with list (bv 8) => idtac end;
                    assert_fails (unify address base);
                    let start := zesu_byte_slice_start address base in
                    let Haddress := fresh "HsliceAddress" in
                    let Hbounds := fresh "HsliceBounds" in
                    assert (Haddress : (base + Z.of_nat start = address)%Z)
                      by (rewrite ?length_take ?length_drop;
                          first [lia | bv_solve | zesu_byte_slice_bound_arith]);
                    assert (Hbounds : (start + count <= length bytes)%nat)
                      by (rewrite ?length_take ?length_drop;
                          first [lia | bv_solve | zesu_byte_slice_bound_arith]);
                    let Hsize := fresh "HsliceSize" in
                    let Hlength := fresh "HsliceLength" in
                    assert (Hsize : size = Z.of_nat count)
                      by (first [reflexivity | lia | bv_solve
                                | (rewrite Z2Nat.id; [reflexivity | first [lia | bv_solve]])]);
                    assert (Hlength :
                      size = Z.of_nat (length (take count (drop start bytes))))
                      by (rewrite Hsize length_take length_drop; lia);
                    iDestruct (zesu_byte_array_lend_slice base bytes start count
                      Hbounds with Harray) as "[Hslice Hrestore]";
                    iEval (rewrite Haddress) in "Hslice Hrestore";
                    unify slice (take count (drop start bytes));
                    first [
                      lazymatch rest with
                      | context[spec_trace ?generated] =>
                          let candidate := eval cbv beta iota delta [li_fst] in
                            (witness.1ₗ) in
                          let abstracted := eval pattern candidate in generated in
                          lazymatch abstracted with
                          | ?prefix _ =>
                              let marker := constr:(fun _ : list seq_label => False) in
                              let probe := eval cbv beta in (prefix marker) in
                              iMatchHyp ltac:(fun Htrace resource =>
                                lazymatch resource with
                                | spec_trace ?declared =>
                                    let tail := zesu_matching_trace_tail marker probe declared in
                                    unify candidate tail;
                                    iPoseProof (spec_trace_mono declared generated
                                      with Htrace) as "HsliceTrace";
                                    [zesu_trace_prefix_inclusion |]
                                end)
                          end
                      end
                    | idtac];
                    iExists witness
                end)
      end
  end.

Ltac zesu_lend_interior_byte_slice_if_enabled :=
  let _ := constr:(_ : ZesuStepInteriorByteSlice) in
  zesu_lend_interior_byte_slice.

Ltac zesu_restore_interior_byte_slice :=
  zesu_expose_environment_alias;
  lazymatch goal with
  | |- envs_entails _ ((?address ↦ₘ∗ ?bytes) ∗ _)%I =>
      let target := constr:((address ↦ₘ∗ bytes)%I) in
      assert_fails (has_evar target);
      iMatchHyp ltac:(fun Hrestore resource =>
        lazymatch resource with
        | (?borrowed -∗ ?whole)%I =>
            constr_eq whole target;
            iMatchHyp ltac:(fun Hslice returned =>
              constr_eq returned borrowed;
              iPoseProof (Hrestore with Hslice) as "?")
        end)
  end.

Ltac zesu_restore_interior_byte_slice_if_enabled :=
  let _ := constr:(_ : ZesuStepInteriorByteSlice) in
  zesu_restore_interior_byte_slice.
