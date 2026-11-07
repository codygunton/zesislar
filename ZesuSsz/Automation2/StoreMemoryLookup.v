Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.SwitchDispatch.
Require Import ZesuSsz.Automation2.BitvectorFacts.
Require Import ZesuSsz.Automation2.Hooks.
From stdpp Require Import bitvector.definitions bitvector.tactics list.
From Coq Require Import ZArith.ZArith NArith.NArith Lia Lists.List.
Local Open Scope Z_scope.
Require Import ZesuSsz.Automation2.ByteArrayLengths.
Require Import ZesuSsz.Automation2.ResourceGroups.
Require Import ZesuSsz.Automation2.RangeFacts.
Require Import iris.proofmode.environments.
Local Open Scope Z_scope.

Class ZesuStepStoreMemoryLookup : Prop := {}.

#[export] Instance zesu_store_integer_address `{ZesuStepStoreMemoryLookup} :
  ZesuSsz.Automation2.Hooks.ZesuStepIntegerArrayAddress := I.
#[export] Instance zesu_store_array_bounds `{ZesuStepStoreMemoryLookup} :
  ZesuSsz.Automation2.Hooks.ZesuStepArrayBounds := I.
#[export] Instance zesu_store_region_bounds `{ZesuStepStoreMemoryLookup} :
  ZesuSsz.Automation2.ByteArrayLengths.ZesuStepArrayRegionBounds := I.

(* Prove each complete address equality before rewriting a splice index.
   The root recognizer rejects symbolic offsets before closed evaluation. *)
Ltac zesu_store_unsigned_splice_indices :=
  repeat multimatch goal with
  | |- context [Z.to_nat (bv_unsigned ?pointer - ?base)] =>
      assert_fails (has_evar pointer);
      assert_fails (has_evar base);
      let expanded := eval cbv beta zeta in pointer in
      ZesuSsz.Automation2.MemoryAddress.zesu_integer_pointer_root expanded
        ltac:(fun _ =>
          let integer := ZesuSsz.Automation2.MemoryAddress.zesu_stack_integer_address expanded in
          let equality := fresh "HstoreUnsignedAddress" in
          assert (equality : bv_unsigned pointer = integer) by
            ZesuSsz.Automation2.MemoryAddress.zesu_stack_arithmetic;
          progress rewrite equality;
          clear equality)
  end.

(* Isolate the proved address and the matching length before linear arithmetic. *)
Ltac zesu_store_selected_linear :=
  cbn [Z.of_N Z.of_nat];
  repeat match goal with
  | |- context [(?left - ?right)%Z] =>
      replace (left - right)%Z with 0%Z by lia
  end;
  rewrite ?Z.sub_diag ?Z.div_1_r ?Z.mod_1_r;
  cbn; solve [lia].

Ltac zesu_store_select_length continuation :=
  match goal with
  | Hlength : List.length ?values = ?count |- context [List.length ?values] =>
      let selected := fresh "HstoreSelectedLength" in
      pose proof Hlength as selected;
      continuation selected
  end.

Ltac zesu_store_splice_bounds :=
  ZesuSsz.Automation2.SwitchDispatch.zesu_switch_enabled
    constr:(ZesuStepStoreMemoryLookup);
  lazymatch goal with
  | |- environments.envs_entails _ _ => fail 0 "store bounds require a pure side condition"
  | |- SHELVED_SIDECOND _ => unshelve_sidecond
  | _ => idtac
  end;
  first [
    lazymatch goal with
    | |- context [bv_unsigned ?pointer] =>
        let expanded := eval cbv beta zeta in pointer in
        let integer := ZesuSsz.Automation2.MemoryAddress.zesu_stack_integer_address expanded in
        let equality := fresh "HstoreSelectedAddress" in
        assert (equality : bv_unsigned pointer = integer) by
          solve [ZesuSsz.Automation2.RangeFacts.zesu_address_equality];
        rewrite equality;
        first [zesu_store_select_length ltac:(fun selected =>
          clear - equality selected; rewrite selected) | clear - equality];
        zesu_store_selected_linear
    end
  | zesu_store_select_length ltac:(fun selected =>
      clear - selected; rewrite selected; zesu_store_selected_linear)
  | solve [reflexivity] ].

(* Rebase indexed byte cells without changing their addresses or fractions. *)
Lemma zesu_indexed_byte_cells_array `{!islaG Sigma}
    (address : nat -> Z) (base : Z) (q : dfrac) (cells : list (bv 8)) :
  (0 <= base /\ base + Z.of_nat (length cells) <= 2^64) ->
  (forall i, address i = base + Z.of_nat i) ->
  ([∗ list] i ↦ v ∈ cells, mem_mapsto (address i) q v) ⊣⊢
  mem_mapsto_array base q cells.
Proof.
 intros Hbound Haddress. rewrite mem_mapsto_array_eq. iSplit.
 - iIntros "Hcells". iExists 1%N. iSplit; first done.
   cbn [Z.of_N]. iSplit; first (iPureIntro; lia).
   iApply (big_sepL_mono with "Hcells"). intros i v Hlookup.
   rewrite Haddress. replace (Z.of_nat i * 1) with (Z.of_nat i) by lia. done.
 - iIntros "[%len [%Hwidth [%Hrange Hcells]]]".
   assert (len = 1)%N by lia. subst len. cbn [Z.of_N].
   iApply (big_sepL_mono with "Hcells"). intros i v Hlookup.
   rewrite Haddress. replace (Z.of_nat i * 1) with (Z.of_nat i) by lia. done.
Qed.
(* Test the owner before traversing its pure source facts. *)
Ltac zesu_store_has_indexed_byte_tail :=
  iMatchHyp ltac:(fun _ body =>
    multimatch body with
    | context [@big_opL _ _ _ _ ?function ?cells] =>
        let atom := eval cbv beta in (function 0%nat (BV 8 0)) in
        lazymatch atom with @mem_mapsto _ _ 8 _ _ _ => idtac end
    end).

(* Retain the structural length equation; the range bound alone is insufficient. *)
Ltac zesu_store_retain_tail_length cells :=
  ZesuSsz.Automation2.PureFacts.zesu_integer_array_facts;
  let count := fresh "storeTailCount" in
  evar (count : nat);
  let fact := fresh "HstoreTailLength" in
  assert (fact : List.length cells = count) by
    (unfold count;
     repeat progress (rewrite ?skipn_length ?firstn_length ?length_app; cbn [List.length]);
     repeat match goal with
     | Hlength : List.length ?values = ?size |- context [List.length ?values] =>
         progress rewrite Hlength
     end;
     reflexivity);
  unfold count in fact; clear count.

Ltac zesu_store_fold_indexed_byte_tail :=
  zesu_store_has_indexed_byte_tail;
  ZesuSsz.Automation2.ByteArrayAssemblyCodec.zesu_byte_array_normalize_stride;
  iMatchHyp ltac:(fun name body =>
    multimatch body with
    | context [@big_opL _ _ _ _ ?function ?cells] =>
      let atom := eval cbv beta in (function 0%nat (BV 8 0)) in
      lazymatch atom with
      | @mem_mapsto ?Sigma ?heap 8 ?base ?fraction _ =>
        zesu_store_retain_tail_length cells;
        let address := constr:(fun i : nat => ltac:(
          let atom := eval cbv beta in (function i (BV 8 0)) in
          lazymatch atom with @mem_mapsto _ _ 8 ?value _ _ => exact value end)) in
        let base := eval cbn [Z.of_nat Nat.add Nat.mul] in base in
        let Haddress := fresh "HindexedAddress" in
        assert (Haddress : forall i, address i = base + Z.of_nat i) by
          (intro i; cbn [Nat.add Nat.mul]; rewrite ?Nat2Z.inj_succ ?Nat2Z.inj_add; lia);
        let Hbound := fresh "HindexedBound" in
        assert (Hbound : 0 <= base /\ base + Z.of_nat (length cells) <= 2^64) by
          (first [assumption |
            multimatch goal with
            | Hrange : 0 <= ?origin /\ ?upper <= 2^64 |- _ =>
                let Hcopy := fresh "HindexedSourceRange" in
                pose proof Hrange as Hcopy;
                clear - Hcopy;
                cbn [List.length Z.of_N] in Hcopy;
                rewrite ?Nat2Z.inj_succ in Hcopy;
                lia
            end]);
        iEval (rewrite (zesu_indexed_byte_cells_array address base fraction cells Hbound Haddress)) in name;
        clear Haddress Hbound
      end
    end).

(* Derive a lookup from an actual owned image and the public semantic rule.
   The typed root limits candidate selection. The range is still proved. *)
Ltac zesu_store_codec_array_lookup :=
  ZesuSsz.Automation2.SwitchDispatch.zesu_switch_enabled
    constr:(ZesuStepStoreMemoryLookup);
  ZesuSsz.Automation2.ResourceGroups.zesu_expose_environment_alias;
  repeat match goal with
  | Hlocal := _ |- environments.envs_entails _
      (find_in_context (FindMemMapsTo ?address) _) =>
      lazymatch address with context[Hlocal] =>
        unfold Hlocal in *; clear Hlocal
      end
  end;
  lazymatch goal with
  | |- environments.envs_entails _
      (find_in_context (FindMemMapsTo (bv_unsigned ?pointer)) _) =>
      let expanded := eval cbv beta zeta in pointer in
      ZesuSsz.Automation2.MemoryAddress.zesu_integer_pointer_root expanded ltac:(fun base =>
        let integer := ZesuSsz.Automation2.MemoryAddress.zesu_stack_integer_address expanded in
        iMatchHyp ltac:(fun name body =>
          lazymatch body with
          | @mem_mapsto_array ?sigma ?heap ?width ?lower ?fraction ?values =>
              assert_fails (has_evar lower);
              assert_fails (has_evar values);
              constr_eq fraction (DfracOwn 1);
              lazymatch lower with context[base] =>
                let sourceIsla := constr:(_ : islaG sigma) in
                constr_eq heap (@islaG_gen_heapG sigma sourceIsla);
                let range := fresh "HownedCodecArrayRange" in
                assert (range : (lower <= integer < lower +
                  Z.of_nat (length values) * Z.of_N (N.div width 8))%Z) by
                  (first [solve [ZesuSsz.Automation2.RangeFacts.zesu_selected_array_range] |
                    cbn [length N.to_nat];
                    repeat (rewrite length_bv_to_little_endian; [|lia]);
                    cbn [length N.to_nat];
                    try (autounfold with zesu_contract_constants);
                    ZesuSsz.Automation2.MemoryAddress.zesu_stack_arithmetic]);
                let found := fresh "HownedArraySemanticLookup" in
                pose proof (@tac_mem_mapsto_array_eq sigma sourceIsla integer
                  width lower integer values (or_introl range)) as found;
                let equality := fresh "HownedArrayReadAddress" in
                assert (equality : bv_unsigned pointer = integer) by
                  (first [solve [ZesuSsz.Automation2.RangeFacts.zesu_address_equality] |
                    ZesuSsz.Automation2.MemoryAddress.zesu_stack_arithmetic]);
                rewrite equality;
                liEnsureInvariant;
                liStep
              end
          end))
  end.

Ltac zesu_store_memory_lookup_core :=
  first [ zesu_store_codec_array_lookup
  | ZesuSsz.Automation2.ResourceGroups.zesu_expose_environment_alias;
    zesu_store_unsigned_splice_indices;
    progress ZesuSsz.Automation2.Hooks.zesu_integer_array_address_if_enabled;
    liEnsureInvariant;
    liStep ].

Ltac zesu_store_memory_lookup :=
  ZesuSsz.Automation2.SwitchDispatch.zesu_switch_enabled
    constr:(ZesuStepStoreMemoryLookup);
  first [ zesu_store_memory_lookup_core
  | lazymatch goal with
    | |- environments.envs_entails _ (find_in_context (FindMemMapsTo _) _) => idtac
    end;
    progress (zesu_store_fold_indexed_byte_tail;
      ZesuSsz.Automation2.ResourceGroups.zesu_open_resource_groups) ].
