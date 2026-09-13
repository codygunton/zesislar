Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessByteLists.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactByteListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactByteListsPublicSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactByteListsDispatchSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactByteListsLoop.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactByteListsDispatch.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactByteListsCountReturn.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactEncoderBytes.
From IslaTraces.write_success_05 Require Import instrs.

Lemma byte_lists_exact_public_count_return_correct `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_05.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15c6c encoderBytesExactCallSpec -∗
  instr_body 0x15c34 byteListsExactPublicCountReturnSpec.
Proof.
  iStartProof. iIntros "#Hcode #Hbytes". iEval (rewrite instr_pre'_eq).
  iIntros "Hentry". iDestruct "Hentry" as
    (callerSp ret savedS0 savedS1 pointer saved items tail)
    "(Hsys & Hx8 & Hframe & %Hlength & %Halign & %Hmin & %Hmax & %Hret1 & %Hret2 & _)".
  iPoseProof (byte_lists_exact_loop_pre
    (byteListsPublicFrame callerSp ret savedS0 savedS1 saved
      (bv_unsigned pointer) items tail) with "Hcode Hbytes") as "#Hloop".
  iPoseProof (byte_lists_exact_dispatch_correct with "Hcode Hloop") as "Hdispatch".
  iPoseProof (byte_lists_exact_count_return_correct with "Hcode Hdispatch") as "Hbody".
  iEval (rewrite instr_pre'_eq) in "Hbody".
  iApply ("Hbody" with "[Hsys Hx8 Hframe]").
  iEval (unfold byteListsExactCountReturnSpec).
  iExists (callerSp - BV 64 32)%bv, ret, savedS0, savedS1, pointer,
    (bv_unsigned pointer), [], items, tail.
  zesu_run. Unshelve. all: zesu_finish.
Qed.

Print Assumptions byte_lists_exact_public_count_return_correct.

Lemma byte_lists_exact_public_count_return_pre `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_05.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15c6c encoderBytesExactCallSpec -∗
  □ instr_pre 0x15c34 byteListsExactPublicCountReturnSpec.
Proof.
  iStartProof. iIntros "#Hcode #Hbytes". iModIntro.
  iApply instr_pre_to_body. iNext.
  iApply byte_lists_exact_public_count_return_correct; iAssumption.
Qed.

Print Assumptions byte_lists_exact_public_count_return_pre.
