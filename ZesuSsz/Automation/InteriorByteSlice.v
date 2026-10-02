Require Import ZesuSsz.Automation.Hooks.
Require Import ZesuSsz.Automation.PureFacts.
Require Import ZesuSsz.Automation.ResourceGroups.
Require Import ZesuSsz.Automation.TracePrefixTail.
Require Import ZesuSsz.Automation.SealedCoverage.
Require Import ZesuSsz.Automation.BoundedArithmetic.
From iris.proofmode Require Import environments.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import isla.riscv64.riscv64.

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
  have Hstride : Z.of_N (8 / 8) = 1%Z by vm_compute.
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
          let start := eval vm_compute in
            (Z.to_nat (bv_unsigned offset - baseOffset)) in
          constr:(start)
      | _ => constr:(Z.to_nat (address - base))
      end
  | _ => constr:(Z.to_nat (address - base))
  end.

Ltac zesu_open_declared_byte_slice address count :=
  iMatchHyp ltac:(fun H sealed =>
    let instance := constr:(_ : ZesuSealed sealed _ _ _) in
    lazymatch type of instance with
    | ZesuSealed _ ?raw ?ranges _ =>
        let head := get_head raw in
        let opened := eval unfold head in raw in
        let bytes := lazymatch opened with
          | context[(_ ↦ₘ∗ ?bytes)%I] => bytes
          end in
        lazymatch type of bytes with list (bv 8) => idtac end;
        let rec covered ranges :=
          lazymatch ranges with
          | (?low, ?high) :: ?rest =>
              first [
                let Hcoverage := fresh "HsliceCoverage" in
                assert (Hcoverage :
                  (low <= address /\ address + Z.of_nat count <= high)%Z)
                  by (first [lia |
                    lazymatch address with
                    | bv_unsigned (?pointer + ?offset)%bv =>
                        zesu_select_index_facts bytes count pointer low
                    | bv_unsigned ?pointer =>
                        zesu_select_index_facts bytes count pointer low
                    end;
                    zesu_bounded_arithmetic ltac:(bv_solve)]);
                clear Hcoverage
              | covered rest]
          end in
        covered ranges;
        iEval (rewrite (zesu_sealed_unfold (ZesuSealed := instance)); unfold head) in H
    end);
  repeat iDestruct select (_ ∗ _)%I as "[? ?]".

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
          lazymatch rest with
          | context[(⌜?size = Z.of_nat (length slice)⌝)%I] =>
              let count := eval vm_compute in (Z.to_nat size) in
              assert_fails (has_evar count);
              first [iMatchHyp ltac:(fun Harray resource =>
                lazymatch resource with
                | (?base ↦ₘ∗ ?bytes)%I =>
                    lazymatch type of bytes with list (bv 8) => idtac end;
                    assert_fails (unify address base);
                    let start := zesu_byte_slice_start address base in
                    let Haddress := fresh "HsliceAddress" in
                    let Hbounds := fresh "HsliceBounds" in
                    assert (Haddress : (base + Z.of_nat start = address)%Z)
                      by (rewrite ?length_take ?length_drop; first [lia | bv_solve]);
                    assert (Hbounds : (start + count <= length bytes)%nat)
                      by (rewrite ?length_take ?length_drop; first [lia | bv_solve]);
                    let Hsize := fresh "HsliceSize" in
                    let Hlength := fresh "HsliceLength" in
                    assert (Hsize : size = Z.of_nat count)
                      by (first [reflexivity | lia | bv_solve]);
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
              | zesu_open_declared_byte_slice address count;
                zesu_lend_interior_byte_slice]
          end
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
