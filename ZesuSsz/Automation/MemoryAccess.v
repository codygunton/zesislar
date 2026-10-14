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

Ltac zesu_memory_access_select name resource base offset values Haddress Hinterval Hindex :=
  rewrite Haddress;
  notypeclasses refine (tac_find_in_context (ZesuMemRegionSearch (base + offset))
    (find_mem_region_inst (base + offset)) _);
  unfold find_mem_region_inst; simpl; repeat liExist false;
  notypeclasses refine (tac_find_hyp_equal (ZesuMemRegionSearch (base + offset))
    resource _ _ _ _ _);
  [apply find_mem_region_array; left;
    change (base <= base + offset < base + Z.of_nat (length values) * 1)%Z;
    rewrite Z.mul_1_r; exact (proj1 Hinterval) | ];
  iFrame name;
  cbn [N.eqb Pos.eqb zesu_byte_access_size];
  iSplitR; [iPureIntro; first [reflexivity | rewrite Z.mod_1_r; reflexivity] | ];
  iExists (Z.to_nat offset);
  iSplitR; [iPureIntro; rewrite ?Z.div_1_r; cbn [N.to_nat]; lia | ];
  iSplitR; [iPureIntro; cbn [N.to_nat]; lia | ];
  try (iExists eq_refl).

Ltac zesu_memory_access_if_enabled facts :=
  zesu_switch_enabled constr:(ZesuStepMemoryAccess);
  zesu_expose_environment_alias;
  unLET;
  lazymatch goal with
  | |- envs_entails _ (WPasm (WriteMem _ _
      (RVal_Bits (bv_to_bvn ?pointer)) _ ?length _ _ :t: _)) =>
      zesu_memory_access_prepare facts pointer length
        ltac:(fun name resource base offset values Haddress Hinterval Hindex =>
          unshelve (notypeclasses refine
            (tac_fast_apply (li_wp_write_mem_zesu _ _ _ _ _ _ _ _ _) _));
          iSplitR; [iPureIntro; reflexivity | ];
          iSplitR; [iPureIntro; discriminate | ];
          zesu_memory_access_select name resource base offset values
            Haddress Hinterval Hindex)
  | |- envs_entails _ (WPasm (ReadMem _ _
      (RVal_Bits (bv_to_bvn ?pointer)) ?length _ _ :t: _)) =>
      zesu_memory_access_prepare facts pointer length
        ltac:(fun name resource base offset values Haddress Hinterval Hindex =>
          notypeclasses refine
            (tac_fast_apply (li_wp_read_mem_zesu _ _ _ _ _ _ _ _) _);
          iSplitR; [iPureIntro; reflexivity | ];
          iSplitR; [iPureIntro; discriminate | ];
          zesu_memory_access_select name resource base offset values
            Haddress Hinterval Hindex)
  end.

