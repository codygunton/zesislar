From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index HintsAuthorizationsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccess.
Require Import ZesuSsz.Experiments.WriteSuccessCalls.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderCalls.
Require Import ZesuSsz.Experiments.WriteSuccessAuthorizationsSpec.
Require Import ZesuSsz.Experiments.WriteSuccessAuthorizationsMemcpy.
Require Import ZesuSsz.Experiments.WriteSuccessAuthorizationsRest.
Require Import ZesuSsz.Experiments.WriteSuccessAuthorizationsTail.

Lemma write_success_authorizations_loop `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x101d4 zesuMemcpyCallSpec -∗
  □ instr_pre 0x15cb0 zesuEncoderU256CallSpec -∗
  □ instr_pre 0x15d10 zesuEncoderIntCallSpec -∗
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  □ instr_pre 0x15590 (writeSuccessAuthorizationsLoopSpec P) -∗
  instr_body 0x15590 (writeSuccessAuthorizationsLoopSpec P).
Proof.
  iStartProof.
  iIntros "#Hlookup #Hcode #Hmemcpy #Hu256 #Hint #Houtput #Hloop".
  iApply (write_success_authorizations_memcpy P with
    "Hlookup Hcode Hmemcpy").
  iApply (write_success_authorizations_rest P with
    "Hlookup Hcode Hu256 Hint Houtput").
  iApply (write_success_authorizations_tail P with
    "Hlookup Hcode Hloop").
Qed.

Lemma write_success_authorizations_loop_pre `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x101d4 zesuMemcpyCallSpec -∗
  □ instr_pre 0x15cb0 zesuEncoderU256CallSpec -∗
  □ instr_pre 0x15d10 zesuEncoderIntCallSpec -∗
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  □ instr_pre 0x15590 (writeSuccessAuthorizationsLoopSpec P).
Proof.
  iStartProof.
  iIntros "#Hlookup #Hcode #Hmemcpy #Hu256 #Hint #Houtput".
  iLöb as "IH".
  iModIntro. iApply instr_pre_to_body. iNext.
  iApply (write_success_authorizations_loop P with
    "Hlookup Hcode Hmemcpy Hu256 Hint Houtput IH").
Qed.
