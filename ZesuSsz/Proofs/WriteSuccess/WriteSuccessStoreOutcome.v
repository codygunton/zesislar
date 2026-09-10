From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.

Import ListNotations.
Open Scope Z_scope.

Inductive WriteSuccessStoreOutcome : Type :=
| WriteSuccessStoreBacked
| WriteSuccessStoreMmio.

Definition writeSuccessStoreBytes (value : bv 64) : list (bv 8) :=
  bv_to_little_endian 8 8 (bv_unsigned value).

Definition writeSuccessStoreOutcomePermitted (global : seq_global_state)
    (address : bv 64) (outcome : WriteSuccessStoreOutcome) : Prop :=
  match outcome with
  | WriteSuccessStoreBacked =>
      exists old, read_mem global.(seq_mem) (bv_unsigned address) 8 = Some old
  | WriteSuccessStoreMmio =>
      read_mem global.(seq_mem) (bv_unsigned address) 8 = None /\
      (bv_unsigned address + 8 <= 2 ^ 64)%Z /\
      set_Forall
        (fun item => ~ (bv_unsigned address <= bv_unsigned item <
          bv_unsigned address + 8)%Z) (dom global.(seq_mem))
  end.

Definition writeSuccessStoreOutcomeMemory (global : seq_global_state)
    (address value : bv 64) (outcome : WriteSuccessStoreOutcome) : mem_map :=
  match outcome with
  | WriteSuccessStoreBacked =>
      write_mem_list global.(seq_mem) address (writeSuccessStoreBytes value)
  | WriteSuccessStoreMmio => global.(seq_mem)
  end.

Definition writeSuccessStoreOutcomeGlobal (global : seq_global_state)
    (address value : bv 64) (outcome : WriteSuccessStoreOutcome) :
    seq_global_state :=
  match outcome with
  | WriteSuccessStoreBacked =>
      global <| seq_mem := writeSuccessStoreOutcomeMemory global address value
        WriteSuccessStoreBacked |>
  | WriteSuccessStoreMmio => global
  end.

Definition writeSuccessStoreOutcomeLabels (address value : bv 64)
    (outcome : WriteSuccessStoreOutcome) : list seq_label :=
  match outcome with
  | WriteSuccessStoreBacked => []
  | WriteSuccessStoreMmio => [SWriteMem address (bv_to_bvn value)]
  end.

Print Assumptions writeSuccessStoreOutcomePermitted.
