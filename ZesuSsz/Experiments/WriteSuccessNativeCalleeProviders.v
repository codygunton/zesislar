Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessByteLists.
Require Import ZesuSsz.Experiments.WriteSuccessCalls.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderBooleanCall.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderBytesCall.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderIntCall.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderInt1645Call.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderOptionalU64Call.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderU256.
Require Import ZesuSsz.Experiments.WriteSuccessNativeCode.

(** Boxed contracts for every raw callee block in the native code bundle. *)
Definition writeSuccessNativeCalleeProviders
    `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (□ instr_pre 0x10190 zesuWriteOutputCallSpec ∗
   □ instr_pre 0x101d4 zesuMemcpyCallSpec ∗
   □ instr_pre 0x15b9c zesuEncoderBooleanCallSpec ∗
   □ instr_pre 0x15bc8 zesuEncoderOptionalU64CallSpec ∗
   □ instr_pre 0x15c10 zesuEncoderByteListsCallSpec ∗
   □ instr_pre 0x15c6c zesuEncoderBytesCallSpec ∗
   □ instr_pre 0x15cb0 zesuEncoderU256CallSpec ∗
   □ instr_pre 0x15ce4 zesuEncoderInt1645CallSpec ∗
   □ instr_pre 0x15d10 zesuEncoderIntCallSpec ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessNativeCalleeProviders) := I.

Lemma write_success_native_callee_providers
    `{!islaG Sigma} `{!threadG} :
  writeSuccessCompleteNativeCode -∗ writeSuccessNativeCalleeProviders.
Proof.
  iStartProof.
  iIntros "#Hnative".
  rewrite /writeSuccessCompleteNativeCode.
  iDestruct "Hnative" as
    "(#Hprologue & #Hlookup & #Hmain & #HoutputCode & #HmemcpyCode &
      #HbooleanCode & #HoptionalCode & #HbyteListsCode & #HbytesCode &
      #HintCode & #Hu256Code & #Hint1645Code)".
  iPoseProof (zesu_write_output_call_pre with "HoutputCode") as "#Houtput".
  iPoseProof (zesu_memcpy_call_pre with "HmemcpyCode") as "#Hmemcpy".
  iPoseProof (zesu_encoder_boolean_call_pre with
    "HbooleanCode HoutputCode") as "#Hboolean".
  iPoseProof (zesu_encoder_int_call_pre with
    "HintCode HoutputCode") as "#Hint".
  iPoseProof (zesu_encoder_optional_u64_call_pre with
    "HoptionalCode Hboolean Hint") as "#Hoptional".
  iPoseProof (zesu_encoder_bytes_call_pre with
    "HbytesCode HintCode HoutputCode") as "#Hbytes".
  iPoseProof (zesu_encoder_u256_call_pre with
    "Hu256Code Houtput") as "#Hu256".
  iPoseProof (zesu_encoder_int1645_call_pre with
    "Hint1645Code HoutputCode") as "#Hint1645".
  iAssert (□ instr_pre 0x15c10 zesuEncoderByteListsCallSpec)%I
    as "#HbyteLists".
  { iModIntro. iApply instr_pre_to_body. iNext.
    iApply (write_success_byte_lists with "HbyteListsCode Hint Hbytes"). }
  rewrite /writeSuccessNativeCalleeProviders.
  iSplitL; first iExact "Houtput".
  iSplitL; first iExact "Hmemcpy".
  iSplitL; first iExact "Hboolean".
  iSplitL; first iExact "Hoptional".
  iSplitL; first iExact "HbyteLists".
  iSplitL; first iExact "Hbytes".
  iSplitL; first iExact "Hu256".
  iSplitL; first iExact "Hint1645".
  iSplitL; first iExact "Hint".
  done.
Qed.
