Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.SwitchDispatch.
Require Import ZesuSsz.Automation.BitvectorFacts.
Require Import ZesuSsz.Automation.Hooks.
From stdpp Require Import bitvector.definitions bitvector.tactics list.
From Coq Require Import ZArith.ZArith NArith.NArith Lia Lists.List.
Local Open Scope Z_scope.
Require Import ZesuSsz.Automation.ByteArrayLengths.
Require Import ZesuSsz.Automation.ResourceGroups.
Require Import iris.proofmode.environments.

Class ZesuStepStoreMemoryLookup : Prop := {}.

#[export] Instance zesu_store_integer_address `{ZesuStepStoreMemoryLookup} :
  ZesuSsz.Automation.Hooks.ZesuStepIntegerArrayAddress := I.
#[export] Instance zesu_store_array_bounds `{ZesuStepStoreMemoryLookup} :
  ZesuSsz.Automation.Hooks.ZesuStepArrayBounds := I.
#[export] Instance zesu_store_region_bounds `{ZesuStepStoreMemoryLookup} :
  ZesuSsz.Automation.ByteArrayLengths.ZesuStepArrayRegionBounds := I.

(* Prove each complete address equality before rewriting a splice index.
   The root recognizer rejects symbolic offsets before closed evaluation. *)
Ltac zesu_store_unsigned_splice_indices :=
  repeat multimatch goal with
  | |- context [Z.to_nat (bv_unsigned ?pointer - ?base)] =>
      assert_fails (has_evar pointer);
      assert_fails (has_evar base);
      let expanded := eval cbv beta zeta in pointer in
      ZesuSsz.Automation.MemoryAddress.zesu_integer_pointer_root expanded
        ltac:(fun _ =>
          let integer := ZesuSsz.Automation.MemoryAddress.zesu_stack_integer_address expanded in
          let equality := fresh "HstoreUnsignedAddress" in
          assert (equality : bv_unsigned pointer = integer) by
            ZesuSsz.Automation.MemoryAddress.zesu_stack_arithmetic;
          progress rewrite equality;
          clear equality)
  end.

Ltac zesu_store_splice_bounds :=
  ZesuSsz.Automation.SwitchDispatch.zesu_switch_enabled
    constr:(ZesuStepStoreMemoryLookup);
  lazymatch goal with
  | |- environments.envs_entails _ _ => fail 0 "store bounds require a pure side condition"
  | |- SHELVED_SIDECOND _ => unshelve_sidecond
  | _ => idtac
  end;
  ZesuSsz.Automation.MemoryAddress.zesu_integer_array_facts;
  zesu_store_unsigned_splice_indices;
  repeat match goal with
  | |- context [?base + ?offset - ?base] =>
      assert_fails (has_evar base);
      assert_fails (has_evar offset);
      replace (base + offset - base) with offset by lia
  | |- context [?base - ?base] =>
      assert_fails (has_evar base);
      replace (base - base) with 0 by lia
  end;
  repeat progress
    (rewrite ?length_app ?length_take ?length_drop ?length_insert;
     cbn [length N.to_nat]);
  lia.

(* Derive a lookup from an actual owned image and the public semantic rule.
   The typed root limits candidate selection. The range is still proved. *)
Ltac zesu_store_codec_array_lookup :=
  ZesuSsz.Automation.SwitchDispatch.zesu_switch_enabled
    constr:(ZesuStepStoreMemoryLookup);
  ZesuSsz.Automation.ResourceGroups.zesu_expose_environment_alias;
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
      ZesuSsz.Automation.MemoryAddress.zesu_integer_pointer_root expanded ltac:(fun base =>
        let integer := ZesuSsz.Automation.MemoryAddress.zesu_stack_integer_address expanded in
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
                  (cbn [length N.to_nat];
                   repeat (rewrite length_bv_to_little_endian; [|lia]);
                   cbn [length N.to_nat];
                   try (autounfold with zesu_contract_constants);
                   ZesuSsz.Automation.MemoryAddress.zesu_stack_arithmetic);
                let found := fresh "HownedArraySemanticLookup" in
                pose proof (@tac_mem_mapsto_array_eq sigma sourceIsla integer
                  width lower integer values (or_introl range)) as found;
                let equality := fresh "HownedArrayReadAddress" in
                assert (equality : bv_unsigned pointer = integer) by
                  ZesuSsz.Automation.MemoryAddress.zesu_stack_arithmetic;
                rewrite equality;
                liEnsureInvariant;
                liStep
              end
          end))
  end.

Ltac zesu_store_memory_lookup :=
  ZesuSsz.Automation.SwitchDispatch.zesu_switch_enabled
    constr:(ZesuStepStoreMemoryLookup);
  first [ zesu_store_codec_array_lookup
  | ZesuSsz.Automation.ResourceGroups.zesu_expose_environment_alias;
    zesu_store_unsigned_splice_indices;
    progress ZesuSsz.Automation.Hooks.zesu_integer_array_address_if_enabled;
    liEnsureInvariant;
    liStep ].
