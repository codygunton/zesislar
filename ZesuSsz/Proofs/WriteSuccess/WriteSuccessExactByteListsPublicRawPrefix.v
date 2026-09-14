Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.Resources.
Require Import ZesuSsz.Automation.Alignment.
Require Import ZesuSsz.Automation.MemoryWords.
Require Import ZesuSsz.Automation.ByteListResources.
Require Import ZesuSsz.Automation.OutputPayloads.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessByteLists.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactByteListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactByteListsPublicSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactEncoderIntCall.
From IslaTraces.write_success_05 Require Import instrs.
Import ZesuSsz.Automation.Calls.FramedContinuations.

Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactByteListsPublicRawReturnSpec.

Lemma byte_lists_exact_public_raw_prefix_correct `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_05.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15d10 zesuEncoderIntPayloadCallSpec -∗
  instr_body 0x15c34 byteListsExactPublicRawCountReturnSpec -∗
  instr_body 0x15c10 encoderByteListsExactCallSpec.
Proof.
  iStartProof. iIntros "#Hcode #Hint Hnext".
  iEval (simpl) in "Hcode".
  zesu_open_resource_groups. zesu_run. Unshelve.
  all: try zesu_pack
    (byteListItemPayloadEvents (sp - BV 64 32)%bv items tail,
      0x15c34%Z, (sp - BV 64 32)%bv, b11, tt)ₗ.
  all: zesu_run. Unshelve. all: try zesu_alignment.
  all: try (zesu_normalize_output_payload; reflexivity).
  all: try (pose (saved :=
    [RVal_Bits b1; RVal_Bits b2; RVal_Bits b3; RVal_Bits b4;
     RVal_Bits b5; RVal_Bits b6; RVal_Bits b7; RVal_Bits b8;
     RVal_Bits b9; RVal_Bits b18]);
    iSplitL; [iIntros "Hreturned";
      rewrite /byteListsExactPublicRawCountReturnSpec;
      iExists sp, ret, b, b0, b10, b11, b12, b13, b14, b15, b16, b17,
        saved, items, tail;
      iSplit;
      [iPureIntro; repeat split; try assumption; try reflexivity |
       rewrite /byteListsExactPublicRawCountReturn;
       zesu_open_resource_groups; zesu_run] | done]).
  Unshelve. all: try zesu_alignment.
  all: zesu_finish.
Qed.
Print Assumptions byte_lists_exact_public_raw_prefix_correct.
