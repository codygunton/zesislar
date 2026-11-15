From Coq Require Import List ZArith.
From stdpp Require Import base list bitvector.definitions.
Require Import isla.riscv64.riscv64.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Automation2.Calls.
Require Import ZesuSsz.Contracts.DecodeItemCompositional.
Require Export ZesuSsz.Contracts.DecodeItemCallData.
Import ListNotations.
Open Scope Z_scope.
Open Scope stdpp_scope.

(* The template of decodeItem's public call spec, over the unsealed domain
   and meaning (decodeItemCallSpec with the Automation2 machine_call; it
   loads no frozen-core module). Callers never import this module: the
   public spec decodeItemCallSpec2 is rendered from this body over sealed
   names in ZesuSsz/Interfaces/DecodeItem.v (tools/block/render_interfaces.py,
   registry ZesuSsz/Contracts/proved_functions.json).
   Compliance/DecodeItemCallSpec2.v proves this template correct. *)
Definition decodeItemCallSpecDefinition `{!islaG Sigma} `{!threadG} : iProp Sigma :=
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

(* Inside the sealed interface the public spec is this template, so a proof
   of the template is a proof of the public spec. *)
Lemma decodeItemCallSpecCorrectFrom `{!islaG Sigma} `{!threadG} (code : iProp Sigma) (entry : Z) :
  (⊢ code -∗ instr_body entry decodeItemCallSpecDefinition) ->
  ⊢ code -∗ instr_body entry decodeItemCallSpecDefinition.
Proof. exact id. Qed.
