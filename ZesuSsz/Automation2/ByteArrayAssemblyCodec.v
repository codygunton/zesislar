From Coq Require Import List ZArith.
From stdpp Require Import list list_numbers tactics bitvector.definitions.
From iris.proofmode Require Import tactics environments spec_patterns.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.ByteArrayAssembly.
Require Import ZesuSsz.Automation2.ResourceGroups.
Require Import ZesuSsz.Automation2.MemoryAddress.
Require Import ZesuSsz.Contracts.IslarisMemory.
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

Ltac zesu_byte_array_assemble_owned_codec :=
  first [ByteArrayAssembly.zesu_byte_array_assemble_owned |
    solve [zesu_byte_array_codec_view;
      ByteArrayAssembly.zesu_byte_array_assemble_owned]].

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

(* The owners of one requested byte array, read off the spatial environment:
   every byte cell or byte array with the same fraction at `base` or at
   `base + _`. The assembler checks each address and value, so this selection
   only bounds it. *)
Ltac zesu_byte_cells_at base fraction environment :=
  lazymatch environment with
  | Enil => constr:(@nil ident)
  | Esnoc ?rest ?name ?body =>
      let tail := zesu_byte_cells_at base fraction rest in
      lazymatch body with
      | @mem_mapsto _ _ 8%N base fraction _ => constr:(cons name tail)
      | @mem_mapsto _ _ 8%N (base + _)%Z fraction _ => constr:(cons name tail)
      | @mem_mapsto_array _ _ 8%N base fraction _ => constr:(cons name tail)
      | @mem_mapsto_array _ _ 8%N (base + _)%Z fraction _ => constr:(cons name tail)
      | _ => tail
      end
  end.

(* Owners with the requested fraction that may hold part of the array but are
   not written at `base` or `base + _`: 64-bit word cells, byte cells, and byte
   arrays. Their addresses are matched arithmetically below. *)
Ltac zesu_byte_owners_off_base base fraction environment :=
  lazymatch environment with
  | Enil => constr:(@nil ident)
  | Esnoc ?rest ?name ?body =>
      let tail := zesu_byte_owners_off_base base fraction rest in
      lazymatch body with
      | @mem_mapsto _ _ 8%N base _ _ => tail
      | @mem_mapsto _ _ 8%N (base + _)%Z _ _ => tail
      | @mem_mapsto_array _ _ 8%N base _ _ => tail
      | @mem_mapsto_array _ _ 8%N (base + _)%Z _ _ => tail
      | @mem_mapsto _ _ 64%N _ fraction _ => constr:(cons name tail)
      | @mem_mapsto _ _ 8%N _ fraction _ => constr:(cons name tail)
      | @mem_mapsto_array _ _ 8%N _ fraction _ => constr:(cons name tail)
      | _ => tail
      end
  end.

(* Prove an owned address equal to a requested one in 64-bit address
   arithmetic: by ring after closed-term evaluation, or by the stack address
   solver, which normalizes wrapped `bv_unsigned` sums. *)
Ltac zesu_byte_array_address_equal :=
  lazymatch goal with
  | |- ?available = ?requested =>
      ZesuSsz.Automation2.MemoryAddress.zesu_handoff_closed_Z available
        ltac:(fun closed_available =>
        ZesuSsz.Automation2.MemoryAddress.zesu_handoff_closed_Z requested
          ltac:(fun closed_requested => change (closed_available = closed_requested)))
  end;
  solve [ring | bv_solve | ZesuSsz.Automation2.MemoryAddress.zesu_stack_arithmetic].

(* Unfold the local definitions inside an address. *)
Ltac zesu_byte_array_expand_locals term :=
  match term with
  | context [?local] =>
      let _ := constr:(ltac:(is_var local; exact tt) : unit) in
      let unfolded := eval unfold local in term in
      zesu_byte_array_expand_locals unfolded
  | _ => term
  end.

(* An integer expression congruent to `term` modulo 2^64: `bv_unsigned` of a
   sum or difference becomes the sum or difference of the parts, a hypothesis
   `bv_unsigned v = e` supplies `e`, and closed parts are evaluated. If the
   address equals `base + d` with 0 <= d < 2^64, this expression minus `base`
   is d modulo 2^64. *)
Ltac zesu_byte_array_mod_image term :=
  match constr:(tt) with
  | _ =>
      let _ := constr:(ltac:(ZesuSsz.Automation2.MemoryAddress.zesu_handoff_closed_term term; exact tt) : unit) in
      ZesuSsz.Automation2.VmClosed.zesu_vm_eval_closed term
  | _ => zesu_byte_array_mod_image_open term
  end
with zesu_byte_array_mod_image_open term :=
  lazymatch term with
  | bv_unsigned (bv_add ?left ?right) =>
      let image_left := zesu_byte_array_mod_image (bv_unsigned left) in
      let image_right := zesu_byte_array_mod_image (bv_unsigned right) in
      constr:((image_left + image_right)%Z)
  | bv_unsigned (bv_sub ?left ?right) =>
      let image_left := zesu_byte_array_mod_image (bv_unsigned left) in
      let image_right := zesu_byte_array_mod_image (bv_unsigned right) in
      constr:((image_left - image_right)%Z)
  | bv_unsigned (Z_to_bv _ ?value) => zesu_byte_array_mod_image value
  | bv_unsigned ?vector =>
      match goal with
      | _ : @eq Z (bv_unsigned vector) ?value |- _ => zesu_byte_array_mod_image value
      | _ => term
      end
  | Z.add ?left ?right =>
      let image_left := zesu_byte_array_mod_image left in
      let image_right := zesu_byte_array_mod_image right in
      constr:((image_left + image_right)%Z)
  | Z.sub ?left ?right =>
      let image_left := zesu_byte_array_mod_image left in
      let image_right := zesu_byte_array_mod_image right in
      constr:((image_left - image_right)%Z)
  | _ => term
  end.

Ltac zesu_byte_array_offset_requested base offset :=
  lazymatch offset with
  | 0%Z => base
  | _ => constr:((base + offset)%Z)
  end.

(* The one offset that an owner of `width` bytes can have: its address's
   modular image minus `base` must ring-normalize to a constant, taken modulo
   2^64, with the whole owner below `count`. Fails when there is no such
   offset. *)
Ltac zesu_byte_array_owner_offset expanded base width count continuation :=
  let image := zesu_byte_array_mod_image expanded in
  (* A difference can only be constant if the image mentions a variable of
     the base, or the base has none. *)
  first [assert_fails (multimatch base with context [?atom] => is_var atom end) |
    multimatch base with
    | context [?atom] => is_var atom; lazymatch image with context [atom] => idtac end
    end];
  let H := fresh "HarrayDifference" in
  assert (H : (image - base = image - base)%Z) by reflexivity;
  ring_simplify (image - base)%Z in H;
  lazymatch type of H with
  | ?difference = _ =>
      clear H;
      lazymatch difference with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end;
      let offset := eval vm_compute in (difference mod 2^64)%Z in
      lazymatch eval vm_compute in (Z.leb (offset + width) count) with
      | true => continuation offset
      end
  end.

(* Place one owner at `base + offset`; a word cell then becomes its eight
   little-endian bytes. The offset comes from the modular image, so an owner
   that cannot match costs no solver call. The equality is closed by ring or
   by the stack address solver, which normalizes wrapped `bv_unsigned` sums.
   An owner that matches no offset stays as it is. *)
Ltac zesu_byte_array_place_owner name base count :=
  iMatchHyp ltac:(fun H owner =>
    constr_eq H name;
    let place := ltac:(fun available width convert =>
      let expanded := zesu_byte_array_expand_locals available in
      zesu_byte_array_owner_offset expanded base width count ltac:(fun offset =>
        let requested := zesu_byte_array_offset_requested base offset in
        let Heq := fresh "HarrayOwnerAddress" in
        assert (Heq : available = requested) by
          (change (expanded = requested);
           first [ring | zesu_byte_array_address_equal]);
        iEval (rewrite Heq) in H; clear Heq;
        convert H)) in
    lazymatch owner with
    | @mem_mapsto _ _ 64%N ?available _ _ =>
        place available 8%Z ltac:(fun H =>
          iDestruct (mem_mapsto_mapsto_to_byte_array with H) as H)
    | @mem_mapsto _ _ 8%N ?available _ _ =>
        place available 1%Z ltac:(fun _ => idtac)
    | @mem_mapsto_array _ _ 8%N ?available _ ?values =>
        let width := eval vm_compute in (Z.of_nat (length values)) in
        place available width ltac:(fun _ => idtac)
    end).

Ltac zesu_byte_array_place_owners names base count :=
  lazymatch names with
  | nil => idtac
  | cons ?name ?rest =>
      try zesu_byte_array_place_owner name base count;
      zesu_byte_array_place_owners rest base count
  end.

(* A separating chain of memory cells and arrays, all with `fraction`, that
   ends in a cell, an array or `emp`. *)
Ltac zesu_byte_array_owner_chain fraction body :=
  lazymatch body with
  | emp%I => idtac
  | (?owner ∗ ?rest)%I =>
      zesu_byte_array_owner_chain fraction owner;
      zesu_byte_array_owner_chain fraction rest
  | @mem_mapsto _ _ _ _ ?q _ => constr_eq q fraction
  | @mem_mapsto_array _ _ _ _ ?q _ => constr_eq q fraction
  end.

(* The package opener can leave an opened array as one chain of cells, for
   example when the cells appear only after a later simplification. Split
   such chains, so the owners below see each cell. *)
Ltac zesu_byte_array_split_owner_chains fraction :=
  repeat iMatchHyp ltac:(fun H body =>
    lazymatch body with
    | (_ ∗ ?rest)%I =>
        zesu_byte_array_owner_chain fraction body;
        lazymatch rest with
        | emp%I => iDestruct H as "[? _]"
        | _ => iDestruct H as "[? ?]"
        end
    end).

(* A goal asks for a byte array that the context owns in pieces: byte cells
   after the package opener split the array, 64-bit word cells, or byte arrays,
   possibly at addresses that equal `base + k` only after wrapped arithmetic.
   The cells can also appear late, as one chain, after the opener splits a
   word's byte array. Split those chains and place the owners, rebuild the
   array from exactly the owners at the base
   with the existing assembler, then frame it. The other resources stay in the
   context. *)
Ltac zesu_byte_array_rebuild_requested :=
  lazymatch goal with
  | |- envs_entails _ (isla.ghost_state.mem_mapsto_array_def _ _ _ ∗ _)%I => idtac
  end;
  ResourceGroups.zesu_expose_environment_alias;
  zesu_byte_array_normalize_stride;
  lazymatch goal with
  | |- envs_entails (Envs _ ?spatial _)
      (@isla.ghost_state.mem_mapsto_array_def _ _ 8%N ?base ?fraction ?bytes ∗ _)%I =>
      assert_fails (has_evar base);
      assert_fails (has_evar fraction);
      assert_fails (has_evar bytes);
      zesu_byte_array_closed_counts bytes;
      zesu_byte_array_split_owner_chains fraction
  end;
  lazymatch goal with
  | |- envs_entails (Envs _ ?spatial _)
      (@isla.ghost_state.mem_mapsto_array_def _ _ 8%N ?base ?fraction ?bytes ∗ _)%I =>
      let count := eval vm_compute in (Z.of_nat (length bytes)) in
      let owners := zesu_byte_owners_off_base base fraction spatial in
      zesu_byte_array_place_owners owners base count
  end;
  lazymatch goal with
  | |- envs_entails (Envs _ ?spatial _)
      (@isla.ghost_state.mem_mapsto_array_def _ _ 8%N ?base ?fraction ?bytes ∗ _)%I =>
      let cells := zesu_byte_cells_at base fraction spatial in
      lazymatch cells with cons _ _ => idtac end;
      let selected := constr:(SGoal (SpecGoal GSpatial false nil cells false)) in
      iAssert (base ↦ₘ{fraction}∗ bytes)%I with selected as "Hzesu_rebuilt_array";
      [ResourceGroups.zesu_open_resource_groups; zesu_byte_array_assemble_owned_codec |
       iEval (rewrite isla.ghost_state.mem_mapsto_array_eq) in "Hzesu_rebuilt_array";
       iFrame "Hzesu_rebuilt_array"]
  end.
