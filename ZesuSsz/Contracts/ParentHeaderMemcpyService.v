From Coq Require Import List ZArith.
From stdpp Require Import base list bitvector.definitions.
Require Import EvmSailRlp.evm_rlp_types.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.AbiBytes.
Require Import ZesuSsz.Contracts.ZiskRuntime.
Require Import ZesuSsz.Automation2.Calls.
Require Import ZesuSsz.Contracts.DecodeItemCallData.
Open Scope Z_scope.
Open Scope stdpp_scope.

Notation memcpyCsrPc := ((0x800e06c0) : Z) (only parsing).
Notation parentHeaderMemcpySource := ((0x80114fb8) : Z) (only parsing).
Notation parentHeaderMemcpyLength := ((80) : Z) (only parsing).

(* The ZisK memcpy service (ZiskRuntime.v, from memcpy.s and dma_memcpy.rs)
   in the machine_call shape. It is a runtime boundary, not a proved spec:
   memcpy returns to ra with sp and the callee-saved registers preserved,
   stores the count at the extra-params word, and copies the source bytes
   to the destination. The three separately owned arrays exclude overlap,
   so this covers only the non-overlapping case of ziskMemcpyMemory.
   It uses no stack. The tail transfer at 0x800d5da0 reaches it with the
   caller's ra, so the caller's return continuation follows the copy. *)
Definition memcpyCallSpec2 `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (machine_call decodeItemCallMap 0
    (fun argv sp RET =>
      ∃ (source scratch : list byte) (inputEndBits : bv 64),
      "zisk_input_end" ↦ᵣ RVal_Bits inputEndBits ∗
      reg_col [(KindReg "zisk_free_input", BitsShape 64)] ∗
      bv_unsigned (argv !!! 1%nat) ↦ₘ∗ source ∗
      bv_unsigned (argv !!! 0%nat) ↦ₘ? bv_unsigned (argv !!! 2%nat) ∗
      ziskExtraParamsAddress ↦ₘ∗ scratch ∗
      ⌜Z.of_nat (length source) = bv_unsigned (argv !!! 2%nat)⌝ ∗
      ⌜length scratch = 8%nat⌝ ∗
      RET (fun _ =>
        "zisk_input_end" ↦ᵣ RVal_Bits inputEndBits ∗
        reg_col [(KindReg "zisk_free_input", BitsShape 64)] ∗
        bv_unsigned (argv !!! 1%nat) ↦ₘ∗ source ∗
        bv_unsigned (argv !!! 0%nat) ↦ₘ∗ source ∗
        ziskExtraParamsAddress ↦ₘ∗ word64Bytes (bv_unsigned (argv !!! 2%nat)) ∗
        True)))%I.
Global Instance : LithiumUnfold (@memcpyCallSpec2) := I.
Global Typeclasses Opaque memcpyCallSpec2.

(* The reviewed runtime premise: the memcpy entry satisfies memcpyCallSpec2. *)
Definition memcpyCallPremise `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (□ instr_pre memcpyCsrPc memcpyCallSpec2)%I.
