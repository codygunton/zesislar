From Coq Require Import List ZArith.
From stdpp Require Import base list bitvector.definitions.
Require Import isla.riscv64.riscv64.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.ParentHeaderRootFacts.
Require Import ZesuSsz.Contracts.NextUint64BlockEntries.
Require Import ZesuSsz.Automation2.Calls.
Require Export ZesuSsz.Contracts.DecodeItemCallData.
Require Export ZesuSsz.Contracts.NextUint64CallData.
Open Scope Z_scope.
Open Scope stdpp_scope.

(* The template of nextUint64's public call spec: nextUint64ContractCorrect
   (NextUint64Contract.v) in the machine_call shape, over the unsealed domain
   and result. Callers never import this module: the public spec
   nextUint64CallSpec2 is rendered from this body over sealed names in
   ZesuSsz/Interfaces/NextUint64.v (tools/block/render_interfaces.py,
   registry ZesuSsz/Contracts/proved_functions.json).
   Compliance/NextUint64CallSpec2.v derives this template from that theorem.
   The slice at a1 is two 64-bit words, so the caller binds the input
   pointer and length from the words it stored there. *)
Definition nextUint64CallSpecDefinition `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (machine_call decodeItemCallMap nextUint64CallStackBytes
    (fun argv sp RET =>
      ∃ (inputPointer inputLength inputEndBits : bv 64) (input : list byte),
      "zisk_input_end" ↦ᵣ RVal_Bits inputEndBits ∗
      reg_col [(KindReg "zisk_free_input", BitsShape 64)] ∗
      bv_unsigned (argv !!! 1%nat) ↦ₘ inputPointer ∗
      (bv_unsigned (argv !!! 1%nat) + 8) ↦ₘ inputLength ∗
      bv_unsigned inputPointer ↦ₘ∗ input ∗
      bv_unsigned (argv !!! 0%nat) ↦ₘ? 16 ∗
      ⌜Z.of_nat (length input) = bv_unsigned inputLength⌝ ∗
      ⌜nextUint64BoundaryDomain
          (nextUint64CallDataArgs argv sp inputPointer inputEndBits input)⌝ ∗
      RET (fun _ =>
        ∃ result : NextUint64Return,
        "zisk_input_end" ↦ᵣ RVal_Bits inputEndBits ∗
        reg_col [(KindReg "zisk_free_input", BitsShape 64)] ∗
        bv_unsigned (argv !!! 1%nat) ↦ₘ Z_to_bv 64 (nextRestPointer result) ∗
        (bv_unsigned (argv !!! 1%nat) + 8) ↦ₘ Z_to_bv 64 (nextRestLength result) ∗
        bv_unsigned inputPointer ↦ₘ∗ input ∗
        bv_unsigned (argv !!! 0%nat) ↦ₘ∗ nextResultBytes result ∗
        ⌜nextUint64RootResult
            (nextUint64Base
              (nextUint64CallDataArgs argv sp inputPointer inputEndBits input))
            result⌝ ∗
        True)))%I.

(* Inside the sealed interface the public spec is this template, so a proof
   of the template is a proof of the public spec. *)
Lemma nextUint64CallSpecCorrectFrom `{!islaG Sigma} `{!threadG} (code : iProp Sigma) (entry : Z) :
  (⊢ code -∗ instr_body entry nextUint64CallSpecDefinition) ->
  ⊢ code -∗ instr_body entry nextUint64CallSpecDefinition.
Proof. exact id. Qed.
