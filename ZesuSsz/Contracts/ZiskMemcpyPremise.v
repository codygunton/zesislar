From Coq Require Import List ZArith.
From stdpp Require Import base list bitvector.definitions.
Require Import EvmSailRlp.evm_rlp_types.
Require Import isla.riscv64.riscv64.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Generated.Stock.Symbols.
Require Import ZesuSsz.Contracts.AbiBytes.
Require Import ZesuSsz.Contracts.ZiskRuntime.
Require Import ZesuSsz.Contracts.ParentHeaderMemcpyService.
Require Import ZesuSsz.Automation2.Calls.
Require Import ZesuSsz.Contracts.DecodeItemCallData.
Open Scope Z_scope.
Open Scope stdpp_scope.

(* The runtime domain of a memcpy with any destination, source and length,
   without the return address (machine_call supplies it). A nonzero copy
   reads and writes RAM: both ranges lie in writable RAM. ZisK RAM is
   readable and writable; stockZiskPermissions' readable predicate covers
   only populated ELF sections, not the heap, so the source is stated as
   writable RAM instead. A zero-length copy only stores the count. *)
Definition ziskMemcpyCallDomain (destination source length : Z) : Prop :=
  ziskWord destination /\ ziskWord source /\ ziskWord length /\
  ziskWritableSection stockZiskPermissions ziskExtraParamsAddress 8 /\
  (length <> 0 ->
    ziskMemcpyRange destination length /\
    ziskMemcpyRange source length /\
    ziskWritableSection stockZiskPermissions source length /\
    ziskWritableSection stockZiskPermissions destination length).

(* The ZisK memcpy service (ZiskRuntime.v) in the machine_call shape, for
   any reached copy: memcpy returns to ra with sp and the callee-saved
   registers preserved, stores the count at the extra-params word, and copies
   the source bytes to the destination. The two separately owned ranges
   exclude overlap, so this covers only the non-overlapping case of
   ziskMemcpyMemory. It uses no stack. memcpyCallSpec2
   (ParentHeaderMemcpyService.v) is its instance at one source and length. *)
Definition ziskMemcpyCallSpec `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (machine_call decodeItemCallMap 0
    (fun argv sp RET =>
      ∃ (source scratch : list byte),
      ⌜ziskMemcpyCallDomain (bv_unsigned (argv !!! 0%nat))
        (bv_unsigned (argv !!! 1%nat)) (bv_unsigned (argv !!! 2%nat))⌝ ∗
      reg_col [(KindReg "zisk_input_end", BitsShape 64);
               (KindReg "zisk_free_input", BitsShape 64)] ∗
      bv_unsigned (argv !!! 1%nat) ↦ₘ∗ source ∗
      bv_unsigned (argv !!! 0%nat) ↦ₘ? bv_unsigned (argv !!! 2%nat) ∗
      ziskExtraParamsAddress ↦ₘ∗ scratch ∗
      ⌜Z.of_nat (length source) = bv_unsigned (argv !!! 2%nat)⌝ ∗
      ⌜length scratch = 8%nat⌝ ∗
      RET (fun _ =>
        reg_col [(KindReg "zisk_input_end", BitsShape 64);
                 (KindReg "zisk_free_input", BitsShape 64)] ∗
        bv_unsigned (argv !!! 1%nat) ↦ₘ∗ source ∗
        bv_unsigned (argv !!! 0%nat) ↦ₘ∗ source ∗
        ziskExtraParamsAddress ↦ₘ∗ word64Bytes (bv_unsigned (argv !!! 2%nat)) ∗
        True)))%I.
Global Instance : LithiumUnfold (@ziskMemcpyCallSpec) := I.
Global Typeclasses Opaque ziskMemcpyCallSpec.

(* The trusted runtime premise: the memcpy entry satisfies ziskMemcpyCallSpec. *)
Definition ziskMemcpyCallPremise `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (□ instr_pre sym_memcpy ziskMemcpyCallSpec)%I.
Global Instance : LithiumUnfold (@ziskMemcpyCallPremise) := I.
Global Typeclasses Opaque ziskMemcpyCallPremise.
