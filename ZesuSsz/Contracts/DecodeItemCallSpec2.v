From Coq Require Import List ZArith.
From stdpp Require Import base list bitvector.definitions.
Require Import isla.riscv64.riscv64.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Automation2.Calls.
Require Import ZesuSsz.Automation2.GoalDomain.
Require Import ZesuSsz.Contracts.DecodeItemCompositional.
Require Export ZesuSsz.Contracts.DecodeItemCallData.
Import ListNotations.
Open Scope Z_scope.
Open Scope stdpp_scope.

(* decodeItemCallSpec with the Automation2 machine_call. A caller that
   imports this module loads no frozen-core module.
   Compliance/DecodeItemCallSpec2.v derives its correctness from
   decodeItemCallSpec_correct. *)
Definition decodeItemCallSpec2 `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (machine_call decodeItemCallMap decodeItemStackBytes
    (fun argv sp RET =>
      ∃ (input before : list byte) (inputEndBits : bv 64),
      "zisk_input_end" ↦ᵣ RVal_Bits inputEndBits ∗
      reg_col [(KindReg "zisk_free_input", BitsShape 64)] ∗
      bv_unsigned (argv !!! 1%nat) ↦ₘ∗ input ∗
      bv_unsigned (argv !!! 0%nat) ↦ₘ∗ before ∗
      ⌜decodeItemC1BDomain
          (decodeItemCallDataArgs argv sp (bv_unsigned inputEndBits) input before)⌝ ∗
      RET (fun _ =>
        ∃ after : DecodeItemOutcome,
        "zisk_input_end" ↦ᵣ RVal_Bits inputEndBits ∗
        reg_col [(KindReg "zisk_free_input", BitsShape 64)] ∗
        bv_unsigned (argv !!! 1%nat) ↦ₘ∗ input ∗
        bv_unsigned (argv !!! 0%nat) ↦ₘ∗ after ∗
        ⌜DecodeMeaningModuloKnownBugs
            (decodeItemCallDataArgs argv sp (bv_unsigned inputEndBits) input before) after⌝ ∗
        True)))%I.
Global Instance : LithiumUnfold (@decodeItemCallSpec2) := I.
Global Typeclasses Opaque decodeItemCallSpec2.

(* The call-site domain is address arithmetic over the call's arguments:
   a caller proves it with the registered-goal step of GoalDomain.v. *)
#[export] Hint Unfold decodeItemC1BDomain decodeItemArgsWellFormed decodeItemEntryLayout
  separateRanges decodeItemCallDataArgs : zesu_goal_domain.
