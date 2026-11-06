From Coq Require Import List ZArith.
From stdpp Require Import list list_numbers tactics bitvector.definitions.
From iris.proofmode Require Import tactics environments spec_patterns.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.ByteArrayAssembly.
Require Import ZesuSsz.Automation.ResourceGroups.
From Coq Require Import Lia.

Ltac zesu_byte_array_closed_counts bytes :=
  lazymatch bytes with
  | @app _ ?left ?right =>
      zesu_byte_array_closed_counts left;
      zesu_byte_array_closed_counts right
  | bv_to_little_endian ?count _ _ => is_closed_term count
  | _ => idtac
  end.

Ltac zesu_byte_array_codec_view :=
  lazymatch goal with
  | |- envs_entails ?environment
      (@mem_mapsto_array ?sigma ?heap 8 ?address ?fraction ?bytes) =>
      zesu_byte_array_closed_counts bytes;
      let expanded := eval cbv beta iota zeta delta [bv_to_little_endian Z_to_little_endian
        Z.iter Pos.iter Pos.of_succ_nat Pos.succ fmap list_fmap List.map app Z.of_N Z.of_nat] in bytes in
      change (envs_entails environment
        (@mem_mapsto_array sigma heap 8 address fraction expanded))
  end.

Ltac zesu_byte_array_assemble_codec :=
  first [ByteArrayAssembly.zesu_byte_array_assemble |
    solve [zesu_byte_array_codec_view;
      ByteArrayAssembly.zesu_byte_array_assemble]].

(* Preserve the width equation supplied by the source array elimination. *)
Ltac zesu_byte_array_normalize_stride :=
  repeat multimatch goal with
  | Hwidth : (8 = ?stride * 8)%N |- _ =>
      is_var stride;
      let Hone := fresh "HbyteStride" in
      assert (Hone : stride = 1%N) by (clear - Hwidth; Lia.lia);
      subst stride
  end.

(* Restore only a complete group of byte cells. The assembler checks every
   address, fraction, and value against the original source list. *)
Ltac zesu_byte_array_restore_source :=
  lazymatch goal with
  | |- envs_entails _ (find_in_context (FindMemMapsTo _) _) => idtac
  end;
  ResourceGroups.zesu_expose_environment_alias;
  zesu_byte_array_normalize_stride;
  multimatch goal with
  | Hbound : ((0 <= ?base)%Z /\
      (?base + ?step * Z.of_nat (length ?bytes) <= ?limit)%Z) |- _ =>
      assert_fails (has_evar base);
      assert_fails (has_evar bytes);
      zesu_byte_array_closed_counts bytes;
      iMatchHyp ltac:(fun source owner =>
        lazymatch owner with
        | ((?available ↦ₘ{?fraction} ?first) ∗ ?tail)%I =>
            let T := type of first in constr_eq T constr:(bv 8);
            assert_fails (has_evar fraction);
            let rec byte_cells rest :=
              lazymatch rest with
              | ((?address ↦ₘ{?q} ?byte) ∗ ?more)%I =>
                  let T := type of byte in constr_eq T constr:(bv 8);
                  constr_eq fraction q; byte_cells more
              | emp%I => idtac
              end in
            byte_cells owner;
            ByteArrayAssembly.zesu_byte_array_same_address available base;
            let restored := iFresh in
            let selected := constr:(SGoal (SpecGoal GSpatial false nil (cons source nil) false)) in
            iAssert (base ↦ₘ{fraction}∗ bytes)%I with selected as restored;
            [ResourceGroups.zesu_open_resource_groups;
             zesu_byte_array_assemble_codec | idtac]
        end)
  end.
