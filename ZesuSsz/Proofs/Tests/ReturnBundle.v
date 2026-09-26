Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Switches.ReturnBundle.
Require Import ZesuSsz.Proofs.WriteSuccess.Interfaces.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeContract.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessRepresentation.

Section tests.
Context `{!islaG Sigma} `{!threadG}.

Lemma return_bundle_bytes (data size sp ret : bv 64)
    (bytes : list (bv 8)) (old_x6 old_s0 old_s1 stack2 : bv 64)
    (tail : spec) :
  ⊢ ((encoderBytesExactReturn data size sp ret bytes
        old_x6 old_s0 old_s1 stack2 tail -∗
      "x2" ↦ᵣ RVal_Bits sp ∗ "x10" ↦ᵣ RVal_Bits data ∗
      spec_trace tail ∗ True) ∗ True)%I.
Proof.
  iStartProof. zesu_enter_return_bundle_if_enabled. iFrame.
Qed.

Lemma return_bundle_boolean (value sp ret : bv 64) (tail : spec) :
  ⊢ ((encoderBooleanClosedReturn value sp ret tail -∗
      "x2" ↦ᵣ RVal_Bits sp ∗ spec_trace tail ∗ True) ∗ True)%I.
Proof.
  iStartProof. zesu_enter_return_bundle_if_enabled. iFrame.
Qed.

Lemma return_bundle_keeps_caller_sealed {Decoded}
    `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded)
    (value sp ret : bv 64) (tail : spec) :
  writeSuccessExactPostWithdrawalsCallerFrame args witness -∗
  ((encoderBooleanClosedReturn value sp ret tail -∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    writeSuccessExactPostWithdrawalsCallerFrame args witness ∗ True) ∗ True)%I.
Proof.
  iIntros "Hcaller". zesu_enter_return_bundle_if_enabled.
  lazymatch iTypeOf "Hcaller" with
  | Some (_, writeSuccessExactPostWithdrawalsCallerFrame args witness) => idtac
  end.
  iFrame.
Qed.
End tests.

Print Assumptions return_bundle_bytes.
Print Assumptions return_bundle_boolean.
Print Assumptions return_bundle_keeps_caller_sealed.
