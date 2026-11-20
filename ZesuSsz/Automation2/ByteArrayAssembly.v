From Coq Require Import List ZArith Lia.
From stdpp Require Import list bitvector.definitions.
From iris.proofmode Require Import tactics environments.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMemory.
Import ListNotations.
Local Open Scope Z_scope.

Lemma zesu_byte_array_cons `{!islaG Sigma} (address : Z) (fraction : dfrac)
    (byte : bv 8) (tail : list (bv 8)) :
  address ↦ₘ{fraction} byte -∗
  (address + 1) ↦ₘ{fraction}∗ tail -∗
  address ↦ₘ{fraction}∗ (byte :: tail).
Proof.
  iIntros "Hhead Htail".
  iApply (mem_mapsto_array_app_combine_at 8 address fraction [byte] tail 1
    with "[Hhead] [Htail]").
  - reflexivity.
  - rewrite mem_mapsto_array_singleton. iExact "Hhead".
  - iExact "Htail".
Qed.

Ltac zesu_byte_array_same_address available requested :=
  first [constr_eq available requested |
    let Heq := fresh "HarrayAssemblyAddress" in
    assert (Heq : available = requested) by ring;
    rewrite Heq; clear Heq].

Ltac zesu_byte_array_head spatial address fraction byte :=
  lazymatch spatial with
  | Esnoc ?rest ?name ?owner =>
      first [
        lazymatch owner with
        | @mem_mapsto ?sigma ?heap 8 ?available ?q ?value =>
            constr_eq fraction q; constr_eq byte value;
            zesu_byte_array_same_address available address
        end
      | zesu_byte_array_head rest address fraction byte]
  end.

Ltac zesu_byte_array_whole spatial address fraction bytes :=
  lazymatch spatial with
  | Esnoc ?rest ?name ?owner =>
      first [
        lazymatch owner with
        | @mem_mapsto_array ?sigma ?heap 8 ?available ?q ?values =>
            constr_eq fraction q; constr_eq bytes values;
            zesu_byte_array_same_address available address;
            solve [iFrame]
        end
      | zesu_byte_array_whole rest address fraction bytes]
  end.

(* A list's length as a nat numeral, evaluated only when no variable decides
   the spine: explicit cells, appends, `take`/`drop`/`insert` at closed
   indices, `replicate` and little-endian words with closed counts, closed
   lists. Otherwise fail without evaluating: the length of a list whose spine
   is stuck on a variable (a count `Z.to_nat (bv_unsigned …)`, a list binder)
   is no numeral, and the VM reads that stuck result back with every element
   normalised, which for open byte terms is a very large term. *)
Ltac zesu_byte_array_ground t :=
  assert_fails (has_evar t);
  assert_fails (idtac; match t with context [?x] => is_var x end).

Ltac zesu_byte_array_spine_closed l :=
  lazymatch l with
  | nil => idtac
  | cons _ ?t => zesu_byte_array_spine_closed t
  | app ?a ?b => zesu_byte_array_spine_closed a; zesu_byte_array_spine_closed b
  | firstn ?n ?t => zesu_byte_array_ground n; zesu_byte_array_spine_closed t
  | skipn ?n ?t => zesu_byte_array_ground n; zesu_byte_array_spine_closed t
  | @insert _ _ _ _ ?i _ ?t => zesu_byte_array_ground i; zesu_byte_array_spine_closed t
  | replicate ?n _ => zesu_byte_array_ground n
  | bv_to_little_endian ?n _ _ => zesu_byte_array_ground n
  | _ => zesu_byte_array_ground l
  end.

Ltac zesu_byte_array_nat_numeral n :=
  lazymatch n with
  | O => idtac
  | S ?m => zesu_byte_array_nat_numeral m
  end.

Ltac zesu_byte_array_length_literal l :=
  let _ := constr:(ltac:(zesu_byte_array_spine_closed l; exact tt) : unit) in
  let count := eval vm_compute in (length l) in
  let _ := constr:(ltac:(zesu_byte_array_nat_numeral count; exact tt) : unit) in
  count.

(* An owned byte array at the requested address whose values equal the
   requested list up to conversion, for example a word's little-endian bytes. *)
Ltac zesu_byte_array_whole_converted spatial address fraction bytes :=
  lazymatch spatial with
  | Esnoc ?rest ?name ?owner =>
      first [
        lazymatch owner with
        | @mem_mapsto_array ?sigma ?heap 8 ?available ?q ?values =>
            constr_eq fraction q;
            zesu_byte_array_same_address available address;
            let count := zesu_byte_array_length_literal values in
            let total := zesu_byte_array_length_literal bytes in
            lazymatch eval vm_compute in (Nat.eqb count total) with true => idtac end;
            let _ := constr:(@eq_refl (list (bv 8)) values : values = bytes) in
            lazymatch goal with
            | |- envs_entails ?environment _ =>
                change (envs_entails environment
                  (@mem_mapsto_array sigma heap 8 address fraction values))
            end;
            solve [iFrame]
        end
      | zesu_byte_array_whole_converted rest address fraction bytes]
  end.

(* An owned byte array at the requested address that covers a proper prefix of
   the requested list, up to conversion. Consume it and continue at the end. *)
Ltac zesu_byte_array_prefix spatial address fraction bytes continuation :=
  lazymatch spatial with
  | Esnoc ?rest ?name ?owner =>
      first [
        lazymatch owner with
        | @mem_mapsto_array ?sigma ?heap 8 ?available ?q ?values =>
            constr_eq fraction q;
            zesu_byte_array_same_address available address;
            let count := zesu_byte_array_length_literal values in
            let total := zesu_byte_array_length_literal bytes in
            lazymatch eval vm_compute in (Nat.ltb count total) with true => idtac end;
            let tail := eval cbn [drop app] in (drop count bytes) in
            let _ := constr:(@eq_refl (list (bv 8)) bytes : bytes = values ++ tail) in
            let Hcount := fresh "HarrayPrefixLength" in
            assert (Hcount : length values = count) by (vm_compute; reflexivity);
            lazymatch goal with
            | |- envs_entails ?environment _ =>
                change (envs_entails environment
                  (@mem_mapsto_array sigma heap 8 address fraction (values ++ tail)))
            end;
            iApply (mem_mapsto_array_app_combine_at 8 address fraction values tail count Hcount
              with "[$]");
            clear Hcount;
            let step := eval vm_compute in (Z.of_N (8 `div` 8) * Z.of_nat count)%Z in
            try change (Z.of_N (8 `div` 8) * Z.of_nat count)%Z with step;
            continuation tt
        end
      | zesu_byte_array_prefix rest address fraction bytes continuation]
  end.

Ltac zesu_byte_array_assemble_core :=
  lazymatch goal with
  | |- envs_entails (Envs ?persistent ?spatial ?counter)
      (@mem_mapsto_array ?sigma ?heap 8 ?address ?fraction ?bytes) =>
      first [zesu_byte_array_whole spatial address fraction bytes |
        let expanded := eval cbn [bv_to_little_endian app] in bytes in
        change (envs_entails (Envs persistent spatial counter)
          (@mem_mapsto_array sigma heap 8 address fraction expanded));
        lazymatch expanded with
        | [?byte] =>
            rewrite mem_mapsto_array_singleton;
            zesu_byte_array_head spatial address fraction byte;
            solve [iFrame]
        | ?byte :: ?tail =>
            zesu_byte_array_head spatial address fraction byte;
            iApply (zesu_byte_array_cons address fraction byte tail with "[$]");
            zesu_byte_array_assemble_core
        end]
  end.

Ltac zesu_byte_array_assemble :=
  solve [zesu_byte_array_assemble_core].

(* The same assembler, but owned byte arrays may also match the requested list
   up to conversion, whole or as a prefix. Only callers that first select a
   few owners use it: a conversion check against an unrelated large array can
   be very expensive. *)
Ltac zesu_byte_array_assemble_owned_core :=
  lazymatch goal with
  | |- envs_entails (Envs ?persistent ?spatial ?counter)
      (@mem_mapsto_array ?sigma ?heap 8 ?address ?fraction ?bytes) =>
      first [zesu_byte_array_whole spatial address fraction bytes |
        zesu_byte_array_whole_converted spatial address fraction bytes |
        zesu_byte_array_prefix spatial address fraction bytes
          ltac:(fun _ => zesu_byte_array_assemble_owned_core) |
        let expanded := eval cbn [bv_to_little_endian app] in bytes in
        change (envs_entails (Envs persistent spatial counter)
          (@mem_mapsto_array sigma heap 8 address fraction expanded));
        lazymatch expanded with
        | [?byte] =>
            rewrite mem_mapsto_array_singleton;
            zesu_byte_array_head spatial address fraction byte;
            solve [iFrame]
        | ?byte :: ?tail =>
            zesu_byte_array_head spatial address fraction byte;
            iApply (zesu_byte_array_cons address fraction byte tail with "[$]");
            zesu_byte_array_assemble_owned_core
        end]
  end.

Ltac zesu_byte_array_assemble_owned :=
  solve [zesu_byte_array_assemble_owned_core].
