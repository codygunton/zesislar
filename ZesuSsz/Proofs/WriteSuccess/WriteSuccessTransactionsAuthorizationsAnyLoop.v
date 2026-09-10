Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCalls.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderIntCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderU256.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAuthorizationsLoop.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAuthorizationsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsAuthorizationsAdapter.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk1558cBranch.

Lemma write_success_transactions_authorizations_any_loop_pre
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x101d4 zesuMemcpyCallSpec -∗
  □ instr_pre 0x15cb0 zesuEncoderU256CallSpec -∗
  □ instr_pre 0x15d10 zesuEncoderIntCallSpec -∗
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  □ instr_pre 0x15590
    (writeSuccessTransactionsAuthorizationsAnyLoopSpec P).
Proof.
  iIntros "#Hlookup #Hcode #Hmemcpy #Hu256 #Hint #Houtput".
  iAssert (□ ∀ (authorizationSp : bv 64) (authorizationBase : Z)
      (authorizationTotal : nat) (authorizationBytes : list (bv 8))
      (authorizationTail : spec),
      instr_pre 0x15590
        (writeSuccessAuthorizationsLoopSpec
          (writeSuccessTransactionsAuthorizationsFrame authorizationSp
            authorizationBase authorizationTotal authorizationBytes
            authorizationTail P)))%I as "#HallLoops".
  { iModIntro. iIntros (authorizationSp authorizationBase authorizationTotal
      authorizationBytes authorizationTail).
    iApply (write_success_authorizations_loop_pre
      (writeSuccessTransactionsAuthorizationsFrame authorizationSp
        authorizationBase authorizationTotal authorizationBytes
        authorizationTail P) with
      "Hlookup Hcode Hmemcpy Hu256 Hint Houtput"). }
  rewrite instr_pre'_eq.
  iModIntro. iNext.
  iIntros "(%authorizationSp & %authorizationBase & %authorizationTotal &
    %authorizationBytes & %authorizationTail & HloopSpec)".
  iSpecialize ("HallLoops" $! authorizationSp authorizationBase
    authorizationTotal authorizationBytes authorizationTail).
  iPoseProof "HallLoops" as "#Hloop".
  iDestruct ("Hloop" with "HloopSpec") as (instruction) "(Hinstr & Hwp)".
  iExists instruction. iFrame.
Qed.
