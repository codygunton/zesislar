Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCalls.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPayloadCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactBooleanCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactBooleanSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactOptionalU64Abi.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactOptionalU64AbiSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactByteLists.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactByteListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactEncoderBytes.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactEncoderIntCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactEncoderU128Call.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactEncoderU128.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactEncoderU256Call.

(** Exact payload contracts derived from the complete executable code bundle. *)
Definition writeSuccessExactCalleeProviders
    `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (□ instr_pre 0x10190 zesuWriteOutputPayloadCallSpec ∗
   □ instr_pre 0x101d4 zesuMemcpyCallSpec ∗
   (∀ P : iProp Sigma,
     □ instr_pre 0x15b9c (zesuEncoderBooleanExactPayloadCallSpec P)) ∗
   □ instr_pre 0x15bc8 zesuEncoderOptionalU64ExactPayloadCallSpec ∗
   □ instr_pre 0x15c10 encoderByteListsExactCallSpec ∗
   □ instr_pre 0x15c6c encoderBytesExactCallSpec ∗
   □ instr_pre 0x15cb0 zesuEncoderU256PayloadCallSpec ∗
   □ instr_pre 0x15ce4 zesuEncoderU128PayloadCallSpec ∗
   □ instr_pre 0x15d10 zesuEncoderIntPayloadCallSpec ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessExactCalleeProviders) := I.

Lemma write_success_exact_callee_providers
    `{!islaG Sigma} `{!threadG} :
  writeSuccessCompleteNativeCode -∗ writeSuccessExactCalleeProviders.
Proof.
  iStartProof. iIntros "#Hnative".
  iEval (rewrite /writeSuccessCompleteNativeCode) in "Hnative".
  iDestruct "Hnative" as
    "(#Hprologue & #Hlookup & #Hmain & #HoutputCode & #HmemcpyCode &
      #HbooleanCode & #HoptionalCode & #HlistsCode & #HbytesCode &
      #HintCode & #Hu256Code & #Hu128Code)".
  rewrite /writeSuccessExactCalleeProviders.
  iSplit; first iApply (zesu_write_output_payload_call_pre with "HoutputCode").
  iSplit; first iApply (zesu_memcpy_call_pre with "HmemcpyCode").
  iSplit.
  { iIntros (P).
    iApply (zesu_encoder_boolean_exact_payload_call_pre P with "HbooleanCode HoutputCode"). }
  iSplit; first iApply (optional_u64_exact_abi_pre with
    "HoptionalCode HbooleanCode HintCode HoutputCode").
  iSplit; first iApply (byte_lists_exact_native_pre with
    "HlistsCode HbytesCode HintCode HoutputCode").
  iSplit; first iApply (encoder_bytes_exact_call_pre with
    "HbytesCode HintCode HoutputCode").
  iSplit; first iApply (zesu_encoder_u256_payload_call_pre with "Hu256Code HoutputCode").
  iSplit; first iApply (zesu_encoder_u128_payload_call_pre with "Hu128Code HoutputCode").
  iSplit; last done.
  iApply (zesu_encoder_int_payload_call_pre with "HintCode HoutputCode").
Qed.
Print Assumptions write_success_exact_callee_providers.
