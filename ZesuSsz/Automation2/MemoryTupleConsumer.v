Require Import ZesuSsz.Automation2.MemoryAddress.
Require Import ZesuSsz.Automation2.Hooks.
Require Import ZesuSsz.Automation2.ResourceGroups.
Require Import ZesuSsz.Automation2.ByteArrayAssemblyCodec.
Require Import ZesuSsz.Automation2.ArrayAffineImage.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.AdjacentWordAddress291.
Require Import ZesuSsz.Automation2.AdjacentWordResources140.
Require Import lithium.interpreter lithium.pure_definitions.
From iris.proofmode Require Import tactics environments spec_patterns.
From Coq Require Import ZArith Lia.
From stdpp Require Import bitvector.definitions list.
Local Open Scope Z_scope.

Ltac zesu_memory_witness_occurs candidate expression :=
  multimatch expression with
  | context [?part] => constr_eq_strict candidate part
  end.

(* Every value is fresh. Only syntactically absent byte-vector fields get zero. *)
Ltac zesu_memory_default_unused value requested :=
  let bare := eval cbv beta iota zeta in value in
  lazymatch bare with
  | @li_pair _ _ ?head ?tail =>
      zesu_memory_default_unused head requested;
      zesu_memory_default_unused tail requested
  | tt => idtac
  | _ =>
      is_evar bare;
      let T := type of bare in
      lazymatch T with
      | bv ?width =>
          tryif zesu_memory_witness_occurs bare requested then idtac
          else unify bare (Z_to_bv width 0)
      end
  end.

Ltac zesu_memory_open_tuple fuel :=
  lazymatch fuel with
  | S ?remaining =>
      lazymatch goal with
      | |- environments.envs_entails _ (@bi_exist _ ?T ?body) =>
          let witness := Hooks.zesu_constraint_witness T in
          let requested := eval cbv beta iota zeta delta [li_fst li_snd]
            in (body witness) in
          zesu_memory_default_unused witness requested;
          notypeclasses refine (tac_ex_evar _ witness _ _); red_li_prod;
          zesu_memory_open_tuple remaining
      | _ => idtac
      end
  | O => fail 0 "The memory package exceeds its existential step bound."
  end.

(* Use the registered introduction without changing the selected rule set. *)
Ltac zesu_memory_registered_intro :=
  lazymatch goal with
  | |- environments.envs_entails _ ?target =>
      let head := get_head target in
      assert_fails (constr_eq head constr:(@bi_exist));
      assert_fails (constr_eq head constr:(@bi_sep));
      let evidence := constr:(_ : Hooks.ZesuPureFactIntro target _) in
      assert_fails (has_evar evidence);
      lazymatch type of evidence with
      | Hooks.ZesuPureFactIntro _ ?source =>
          iApply (@Hooks.zesu_pure_fact_intro _ target source evidence)
      end
  end.

Ltac zesu_memory_byte_owner owner continuation :=
  lazymatch owner with
  | @mem_mapsto_array _ _ 8%N ?address ?fraction ?bytes =>
      continuation address fraction bytes constr:(@None (bv 64))
  | @mem_mapsto _ _ 64%N ?address ?fraction ?word =>
      let bytes := constr:(bv_to_little_endian 8 8 (bv_unsigned word)) in
      continuation address fraction bytes constr:(Some word)
  end.

Ltac zesu_memory_address_equal available requested :=
  first [solve [constr_eq available requested; reflexivity] |
    MemoryAddress.zesu_handoff_closed_Z available ltac:(fun left =>
      MemoryAddress.zesu_handoff_closed_Z requested ltac:(fun right =>
        change (left = right); solve [ring | MemoryAddress.zesu_stack_arithmetic]))].

Ltac zesu_memory_array_count bytes word continuation :=
  lazymatch word with
  | Some _ => continuation constr:(8%nat)
  | None => lazymatch bytes with
    | bv_to_little_endian ?digits _ _ =>
        tryif is_closed_term digits
        then let count := eval vm_compute in (Z.to_nat digits) in continuation count
        else continuation constr:(length bytes)
    | _ => continuation constr:(length bytes)
    end
  end.

(* Match complete source lists before considering their addresses. *)
Ltac zesu_memory_join_arrays :=
  lazymatch goal with
  | |- environments.envs_entails _
      (@bi_sep _ (mem_mapsto_array_def ?address ?fraction ?bytes) _) =>
    assert_fails (has_evar bytes);
    ResourceGroups.zesu_expose_environment_alias;
    iMatchHyp ltac:(fun leftName leftOwner =>
      zesu_memory_byte_owner leftOwner ltac:(fun leftAddress leftFraction leftBytes leftWord =>
        constr_eq fraction leftFraction;
        iMatchHyp ltac:(fun rightName rightOwner =>
          tryif constr_eq leftName rightName then fail 0 else idtac;
          zesu_memory_byte_owner rightOwner
            ltac:(fun rightAddress rightFraction rightBytes rightWord =>
            constr_eq fraction rightFraction;
            let owners := constr:([SIdent leftName []; SIdent rightName []]) in
            let Hbytes := fresh "HmemoryArrayBytes" in
            assert (Hbytes : bytes = (leftBytes ++ rightBytes)%list) by reflexivity;
            zesu_memory_array_count leftBytes leftWord ltac:(fun count =>
            let Hcount := fresh "HmemoryArrayLength" in
            assert (Hcount : length leftBytes = count) by
              first [reflexivity |
                rewrite length_bv_to_little_endian;
                  [reflexivity | Lia.lia]];
            let Hnext := fresh "HmemoryArrayNext" in
            assert (Hnext : rightAddress =
              (leftAddress + Z.of_N (8 / 8) * Z.of_nat count)%Z) by
              zesu_memory_address_equal rightAddress
                constr:((leftAddress + Z.of_N (8 / 8) * Z.of_nat count)%Z);
            lazymatch leftWord with
            | Some ?low =>
              lazymatch rightWord with
              | Some ?high =>
                iDestruct (adjacent_words_to_bytes140 _ _ fraction
                  leftAddress rightAddress 8%nat 8%nat low high Hnext
                  with owners) as leftName
              | None =>
                iDestruct (mem_mapsto_mapsto_to_byte_array with leftName) as leftName;
                iEval (rewrite Hnext) in rightName;
                iDestruct (mem_mapsto_array_app_combine_at 8 leftAddress fraction
                  leftBytes rightBytes count Hcount with owners) as leftName
              end
            | None =>
              lazymatch rightWord with
              | Some _ =>
                  iDestruct (mem_mapsto_mapsto_to_byte_array with rightName) as rightName
              | None => idtac
              end;
              iEval (rewrite Hnext) in rightName;
              iDestruct (mem_mapsto_array_app_combine_at 8 leftAddress fraction
                leftBytes rightBytes count Hcount with owners) as leftName
            end;
            first [iEval (rewrite <- Hbytes) in leftName | idtac];
            first [constr_eq leftAddress address |
              let Hbase := fresh "HmemoryArrayBase" in
              assert (Hbase : leftAddress = address) by
                zesu_memory_address_equal leftAddress address;
              iEval (rewrite Hbase) in leftName; clear Hbase];
            clear Hbytes Hcount Hnext)))))
  end.

Ltac zesu_memory_frame_first :=
  lazymatch goal with
  | |- environments.envs_entails _ (@bi_sep _ ?first _) =>
      lazymatch first with @bi_pure _ _ => fail 0 | _ => idtac end;
      iMatchHyp ltac:(fun name body => progress (first [iFrame name |
        iEval (rewrite isla.ghost_state.mem_mapsto_array_eq) in name;
        iFrame name]))
  end.

(* Scalar constraints select constrained fields. The array consumer preserves
   the source addresses, fractions, and byte order. Callers supply pure logic. *)
Ltac zesu_memory_array_assemble :=
  first [ByteArrayAssemblyCodec.zesu_byte_array_assemble_codec |
    solve [ArrayAffineImage.zesu_array_affine_presentation]].

(* Assemble a leading byte array from its source owners before framing other owners. *)
Ltac zesu_memory_assemble_leading :=
  lazymatch goal with
  | |- environments.envs_entails _ (@bi_sep _ (isla.ghost_state.mem_mapsto_array_def _ _ _) _) =>
      iSplitL;
      [rewrite <- isla.ghost_state.mem_mapsto_array_eq;
       zesu_memory_array_assemble | idtac]
  end.

Ltac zesu_memory_tuple consume_facts finish :=
  once (try zesu_memory_registered_intro;
  ResourceGroups.zesu_open_resource_groups;
  ByteArrayAssemblyCodec.zesu_byte_array_normalize_stride;
  zesu_memory_open_tuple constr:(16%nat);
  repeat iMatchHyp ltac:(fun name body => is_var body; progress (iFrame name));
  try zesu_memory_assemble_leading;
  repeat first [progress zesu_memory_frame_first |
    progress zesu_memory_join_arrays];
  try zesu_memory_assemble_leading);
  lazymatch goal with
  | |- environments.envs_entails _ ?requested => consume_facts requested
  end;
  finish constr:(tt).
