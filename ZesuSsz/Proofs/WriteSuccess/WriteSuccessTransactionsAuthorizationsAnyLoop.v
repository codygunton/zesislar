Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccessCalls.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderIntCall.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderU256.
Require Import ZesuSsz.Experiments.WriteSuccessAuthorizationsLoop.
Require Import ZesuSsz.Experiments.WriteSuccessAuthorizationsSpec.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsAuthorizationsAdapter.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsChunk1558cBranch.

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
