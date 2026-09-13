Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.Calls.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputSemantic.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactBooleanSpec.

Definition zesuEncoderOptionalU64ExactSomeCallSpec
    `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (zesu_c_call 32 (fun args sp RET =>
    ∃ (value : bv 64) (tag : bv 8) (tail : spec),
    bv_unsigned (args !!! 0%nat) ↦ₘ value ∗
    (bv_unsigned (args !!! 0%nat) + 8) ↦ₘ tag ∗
    ⌜tag <> BV 8 0⌝ ∗
    ⌜bv_extract 0 3 (args !!! 0%nat) = BV 3 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned (args !!! 0%nat)⌝ ∗
    ⌜bv_unsigned (args !!! 0%nat) + 8 < 0x40000000⌝ ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace (writeOutputEvents (sp - BV 64 25)%bv (BV 64 1)
      (writeSuccessBooleanWordPayload (BV 64 1))
      (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
        (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned value))) tail)) ∗
    RET (fun _ =>
      bv_unsigned (args !!! 0%nat) ↦ₘ value ∗
      (bv_unsigned (args !!! 0%nat) + 8) ↦ₘ tag ∗
      mmio_range 0x2401a0c0 16 ∗ spec_trace tail ∗ True)))%I.

Definition zesuEncoderOptionalU64ExactNoneCallSpec
    `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (zesu_c_call 32 (fun args sp RET =>
    ∃ (value : bv 64) (tag : bv 8) (tail : spec),
    bv_unsigned (args !!! 0%nat) ↦ₘ value ∗
    (bv_unsigned (args !!! 0%nat) + 8) ↦ₘ tag ∗
    ⌜tag = BV 8 0⌝ ∗
    ⌜bv_extract 0 3 (args !!! 0%nat) = BV 3 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned (args !!! 0%nat)⌝ ∗
    ⌜bv_unsigned (args !!! 0%nat) + 8 < 0x40000000⌝ ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace (writeOutputEvents (sp - BV 64 9)%bv (BV 64 1)
      (writeSuccessBooleanWordPayload (BV 64 0)) tail) ∗
    RET (fun _ =>
      bv_unsigned (args !!! 0%nat) ↦ₘ value ∗
      (bv_unsigned (args !!! 0%nat) + 8) ↦ₘ tag ∗
      mmio_range 0x2401a0c0 16 ∗ spec_trace tail ∗ True)))%I.

Definition zesuEncoderOptionalU64ExactPayloadCallSpec
    `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (zesuEncoderOptionalU64ExactSomeCallSpec ∨ zesuEncoderOptionalU64ExactNoneCallSpec)%I.

Global Instance : LithiumUnfold (@zesuEncoderOptionalU64ExactSomeCallSpec) := I.
Global Instance : LithiumUnfold (@zesuEncoderOptionalU64ExactNoneCallSpec) := I.
Global Instance : LithiumUnfold (@zesuEncoderOptionalU64ExactPayloadCallSpec) := I.
