Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Proofs.WriteSuccess.Interfaces.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactSuffixHashesLoopSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactSuffixBytesPayloadSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputSemantic.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.

Import ListNotations.
Open Scope Z_scope.

Definition suffixTailFieldsCaller `{!islaG Sigma} `{!threadG}
    (sp data size : bv 64) (bytes : list (bv 8)) (P : iProp Sigma) :
    iProp Sigma :=
  ("x6" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
   reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
     ["x3"; "x4"; "x7"; "x17"; "x18"; "x19"; "x20"; "x21";
      "x22"; "x23"; "x24"; "x25"; "x26"; "x27"; "x28"; "x29";
      "x30"; "x31"]) ∗
   (bv_unsigned sp - 48) ↦ₘ? 48 ∗
   (bv_unsigned sp + 920) ↦ₘ data ∗
   (bv_unsigned sp + 928) ↦ₘ size ∗
   bv_unsigned data ↦ₘ∗ bytes ∗
   ⌜bv_unsigned size = length bytes⌝ ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜mapRamBase defaultMap <= bv_unsigned sp - 48⌝ ∗
   ⌜bv_unsigned sp < machineRamEnd defaultMap⌝ ∗
   ⌜bv_unsigned sp + 1896 < machineRamEnd defaultMap⌝ ∗
   P ∗ True)%I.
Global Instance : LithiumUnfold (@suffixTailFieldsCaller) := I.

Lemma write_success_exact_suffix_hashes_tail_connection
    `{!islaG Sigma} `{!threadG}
    (sp data size : bv 64) (hashBase : Z)
    (hashBytes bytes : list (bv 8)) (tail : spec) (P : iProp Sigma) :
  instr_body 0x158e0
    (writeSuccessExactTailFieldsEntryBoundary sp data size (BV 64 0)
      (Z_to_bv 64 (hashBase + Z.of_nat (length hashBytes)))
      bytes tail (hashBase ↦ₘ∗ hashBytes ∗ suffixLoopScratch sp ∗ P)) -∗
  instr_body 0x158e0
    (suffixLoopExit sp hashBase hashBytes
      (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
        (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned size)))
        (writeOutputEvents data size bytes tail))
      (suffixTailFieldsCaller sp data size bytes P)).
Proof. move => *. zesu_block. Qed.

Print Assumptions write_success_exact_suffix_hashes_tail_connection.
