From Coq Require Import List ZArith Lia.
From stdpp Require Import list.
From stdpp.bitvector Require Import bitvector tactics.
Require Export ZesuSsz.Automation.ListImageFacts.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.ByteArrays.
Require Import ZesuSsz.Automation.UninitRegions.
Require Import ZesuSsz.Automation.ResourceGroups.
Require Import ZesuSsz.Automation.SwitchDispatch.
From iris.proofmode Require Import environments.

Local Open Scope Z_scope.

Class ZesuStepMemoryAccess : Prop := {}.

Lemma memory_access_unsigned_address (base offset : Z) :
  0 <= base + offset < 2 ^ 64 ->
  bv_unsigned (bv_add (Z_to_bv 64 base) (Z_to_bv 64 offset)) = base + offset.
Proof.
  intros Hrange.
  rewrite bv_add_unsigned !Z_to_bv_unsigned bv_wrap_add_idemp.
  apply bv_wrap_small. exact Hrange.
Qed.

Lemma memory_access_index_extent {A : Type} (values : list A)
    (offset : Z) (width : nat) :
  0 <= offset ->
  offset + Z.of_nat width <= Z.of_nat (length values) ->
  Z.of_nat (Z.to_nat offset) = offset /\
  (Z.to_nat offset + width <= length values)%nat.
Proof.
  intros Hoffset Hextent. split.
  - apply Z2Nat.id. exact Hoffset.
  - apply Nat2Z.inj_le. rewrite Nat2Z.inj_add Z2Nat.id; [|exact Hoffset].
    exact Hextent.
Qed.

Lemma memory_access_full_interval {A : Type} (values : list A)
    (base offset : Z) (width : nat) :
  (0 < width)%nat -> 0 <= base -> 0 <= offset ->
  offset + Z.of_nat width <= Z.of_nat (length values) ->
  base + Z.of_nat (length values) <= 2 ^ 64 ->
  (base <= base + offset < base + Z.of_nat (length values)) /\
  (0 <= base + offset < 2 ^ 64).
Proof. intros Hwidth Hbase Hoffset Hextent Hnowrap. split; lia. Qed.

Ltac zesu_memory_offset_integer offset :=
  lazymatch offset with
  | Z_to_bv 64 ?value => constr:(value)
  | @BV _ ?value _ =>
      let closed := constr:((ltac:(tryif is_closed_term value
        then exact true else exact false)) : bool) in
      lazymatch closed with
      | true => constr:(value)
      | false => constr:(bv_unsigned offset)
      end
  | bv_add ?left ?right =>
      let leftZ := zesu_memory_offset_integer left in
      let rightZ := zesu_memory_offset_integer right in
      constr:((leftZ + rightZ)%Z)
  | bv_sub ?left ?right =>
      let leftZ := zesu_memory_offset_integer left in
      let rightZ := zesu_memory_offset_integer right in
      constr:((leftZ - rightZ)%Z)
  | bv_mul ?left ?right =>
      let leftZ := zesu_memory_offset_integer left in
      let rightZ := zesu_memory_offset_integer right in
      constr:((leftZ * rightZ)%Z)
  | _ => constr:(bv_unsigned offset)
  end.

Ltac zesu_memory_pointer_parts pointer continuation :=
  lazymatch pointer with
  | Z_to_bv 64 ?base => continuation base constr:(0%Z)
  | bv_add ?left ?right =>
      let rightZ := zesu_memory_offset_integer right in
      zesu_memory_pointer_parts left ltac:(fun base offset =>
        continuation base constr:((offset + rightZ)%Z))
  | bv_sub ?left ?right =>
      let rightZ := zesu_memory_offset_integer right in
      zesu_memory_pointer_parts left ltac:(fun base offset =>
        continuation base constr:((offset - rightZ)%Z))
  end.

Ltac zesu_memory_array_count base spatial continuation :=
  lazymatch spatial with
  | Enil => continuation constr:(0%nat)
  | Esnoc ?rest _ ?resource =>
      zesu_memory_array_count base rest ltac:(fun count =>
        lazymatch resource with
        | (?actual ↦ₘ{_}∗ _)%I =>
            tryif constr_eq base actual
            then continuation constr:(S count)
            else continuation count
        | _ => continuation count
        end)
  end.

Ltac zesu_memory_access_arithmetic facts :=
  facts;
  autorewrite with zesu_image in *;
  cbn [N.to_nat Z.of_nat length] in *;
  first [lia | bv_solve].

(* The complete extent and no-wrap proofs precede region and index selection. *)
Ltac zesu_memory_access_prepare facts pointer byteLength continuation :=
  assert_fails (has_evar pointer);
  assert_fails (has_evar byteLength);
  lazymatch byteLength with
  | 1%N => idtac | 2%N => idtac | 8%N => idtac
  end;
  let bytes := eval cbv in (N.to_nat byteLength) in
  zesu_memory_pointer_parts pointer ltac:(fun base offset =>
    assert_fails (has_evar base);
    lazymatch goal with
    | |- envs_entails (Envs _ ?spatial _) _ =>
        zesu_memory_array_count base spatial ltac:(fun count =>
          lazymatch count with
          | 1%nat => idtac
          | S (S _) => fail 100 "Two owned arrays have the same memory base"
          end)
    end;
    iMatchHyp ltac:(fun name resource =>
      lazymatch resource with
      | (?actual ↦ₘ∗ ?values)%I =>
          constr_eq base actual;
          let valuesType := type of values in
          constr_eq valuesType (list (bv 8));
          assert_fails (has_evar values);
          let Hbase := fresh "HaccessBase" in
          let Hoffset := fresh "HaccessOffset" in
          let Hextent := fresh "HaccessExtent" in
          let Hnowrap := fresh "HaccessNoWrap" in
          assert (Hbase : (0 <= base)%Z) by (zesu_memory_access_arithmetic facts);
          assert (Hoffset : (0 <= offset)%Z) by (zesu_memory_access_arithmetic facts);
          assert (Hextent : (offset + Z.of_nat bytes <= Z.of_nat (length values))%Z)
            by (zesu_memory_access_arithmetic facts);
          assert (Hnowrap : (base + Z.of_nat (length values) <= 2 ^ 64)%Z)
            by (zesu_memory_access_arithmetic facts);
          let Hinterval := fresh "HaccessInterval" in
          pose proof (memory_access_full_interval values base offset bytes
            ltac:(cbn; lia) Hbase Hoffset Hextent Hnowrap) as Hinterval;
          let Haddress := fresh "HaccessAddress" in
          assert (Haddress : bv_unsigned pointer = (base + offset)%Z) by
            (rewrite ?bv_add_unsigned ?bv_sub_unsigned ?bv_mul_unsigned
              !Z_to_bv_unsigned ?bv_unsigned_BV;
             repeat first [progress rewrite bv_wrap_add_idemp |
               progress rewrite bv_wrap_add_idemp_l |
               progress rewrite bv_wrap_add_idemp_r |
               progress rewrite bv_wrap_sub_idemp |
               progress rewrite bv_wrap_sub_idemp_l |
               progress rewrite bv_wrap_sub_idemp_r |
               progress rewrite bv_wrap_mul_idemp |
               progress rewrite bv_wrap_mul_idemp_l |
               progress rewrite bv_wrap_mul_idemp_r |
               lazymatch goal with
               | |- context[bv_wrap 64 ((bv_wrap 64 ?x + ?y) + ?z)] =>
                   rewrite -(Z.add_assoc (bv_wrap 64 x) y z);
                   rewrite bv_wrap_add_idemp_l;
                   rewrite (Z.add_assoc x y z)
               end |
               lazymatch goal with
               | |- context[bv_wrap 64 ((?x + bv_wrap 64 ?y) + ?z)] =>
                   rewrite -(Z.add_assoc x (bv_wrap 64 y) z);
                   rewrite (Z.add_comm (bv_wrap 64 y) z);
                   rewrite (Z.add_assoc x z (bv_wrap 64 y));
                   rewrite bv_wrap_add_idemp_r
               end];
             lazymatch goal with |- bv_wrap 64 ?integer = _ =>
               replace integer with (base + offset)%Z by ring
             end;
             apply bv_wrap_small; exact (proj2 Hinterval));
          let Hindex := fresh "HaccessIndex" in
          pose proof (memory_access_index_extent values offset bytes Hoffset Hextent)
            as Hindex;
          continuation name resource base offset values Haddress Hinterval Hindex
      end)).

(* This local certificate exists only during one checked region selection. *)
Class MemoryAccessSelection (address : Z) : Type := {
  memory_selection_base : Z;
  memory_selection_values : list (bv 8);
  memory_selection_width : nat;
  memory_selection_bounds :
    0 <= memory_selection_base /\ memory_selection_base <= address /\
    address + Z.of_nat memory_selection_width <=
      memory_selection_base + Z.of_nat (length memory_selection_values) /\
    memory_selection_base + Z.of_nat (length memory_selection_values) <= 2 ^ 64
}.
Global Hint Mode MemoryAccessSelection + : typeclass_instances.

Lemma memory_access_find_array `{!islaG Sigma} (address : Z)
    (choice : MemoryAccessSelection address) (T : mem_mapsto_kind -> iProp Sigma) :
  ((@memory_selection_base address choice) ↦ₘ∗ (@memory_selection_values address choice) ∗
    T (MKArray 8 (@memory_selection_base address choice) (@memory_selection_values address choice))) ⊢
  find_in_context (FindMemMapsTo address) T.
Proof.
  iIntros "[Hbytes HT]".
  iExists (MKArray 8 (@memory_selection_base address choice) (@memory_selection_values address choice)).
  by iFrame.
Qed.

Definition memory_access_array_inst `{!islaG Sigma} `{!ZesuStepMemoryAccess}
    (address : Z) {choice : MemoryAccessSelection address} :=
  [instance memory_access_find_array address choice with FICSyntactic].
Global Existing Instance memory_access_array_inst | 0.

Ltac zesu_memory_continuation_width target continuation :=
  lazymatch target with
  | context [N.to_nat ?width] => continuation width
  | context [Z.of_N ?width] => continuation width
  end.

Ltac zesu_memory_access_if_enabled facts :=
  lazymatch goal with
  | |- envs_entails _ (find_in_context (FindMemMapsTo _) _) => idtac
  end;
  zesu_switch_enabled constr:(ZesuStepMemoryAccess);
  zesu_expose_environment_alias;
  unLET;
  lazymatch goal with
  | |- envs_entails _
      (find_in_context (FindMemMapsTo (bv_unsigned ?pointer)) ?K) =>
      zesu_memory_pointer_parts pointer ltac:(fun base offset =>
        iMatchHyp ltac:(fun name resource =>
          lazymatch resource with
          | (?actual ↦ₘ∗ ?values)%I =>
              constr_eq base actual;
              let target := eval cbn [N.eqb Pos.eqb
                zesu_byte_access_size] in (K (MKArray 8 base values)) in
              zesu_memory_continuation_width target ltac:(fun width =>
                zesu_memory_access_prepare facts pointer width
                  ltac:(fun selected resource base offset values Haddress
                      Hinterval Hindex =>
                    let count := eval cbv in (N.to_nat width) in
                    let Hbounds := fresh "HselectionBounds" in
                    assert (Hbounds :
                      0 <= base /\ base <= base + offset /\
                      base + offset + Z.of_nat count <=
                        base + Z.of_nat (length values) /\
                      base + Z.of_nat (length values) <= 2 ^ 64)
                      by (repeat split; lia);
                    let certificate := constr:(@Build_MemoryAccessSelection
                      (base + offset) base values count Hbounds) in
                    assert_fails (has_evar certificate);
                    let selected := fresh "memorySelection" in
                    pose (selected := certificate);
                    rewrite Haddress;
                    liFindInContext;
                    unfold selected in *; clear selected))
          end))
  end.
