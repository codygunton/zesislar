Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import WriteSuccessNativeCode WriteSuccessCalls
 WriteSuccessPayloadCall WriteSuccessExactEncoderIntCall WriteSuccessExactEncoderBytes.
Definition exactPrefixCalls `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (□ instr_pre 0x101d4 zesuMemcpyCallSpec ∗
   □ instr_pre 0x10190 zesuWriteOutputPayloadCallSpec ∗
   □ instr_pre 0x15d10 zesuEncoderIntPayloadCallSpec ∗
   □ instr_pre 0x15c6c encoderBytesExactCallSpec)%I.
Lemma exact_prefix_calls `{!islaG Sigma} `{!threadG} :
  writeSuccessCompleteNativeCode -∗ exactPrefixCalls.
Proof.
  rewrite /writeSuccessCompleteNativeCode /exactPrefixCalls.
  iIntros "#(Hprologue & Hlookup & Hmain & Houtput & Hmemcpy & Hboolean & Hoptional & Hlists & Hbytes & Hint & Hu256 & Hu128)".
  iPoseProof (zesu_memcpy_call_pre with "Hmemcpy") as "#Hcopy".
  iPoseProof (zesu_write_output_payload_call_pre with "Houtput") as "#Hwrite".
  iPoseProof (zesu_encoder_int_payload_call_pre with "Hint Houtput") as "#Hinteger".
  iPoseProof (encoder_bytes_exact_call_pre with "Hbytes Hint Houtput") as "#Hpayload".
  iSplit; [iExact "Hcopy" |].
  iSplit; [iExact "Hwrite" |].
  iSplit; [iExact "Hinteger" | iExact "Hpayload"].
Qed.
Print Assumptions exact_prefix_calls.
