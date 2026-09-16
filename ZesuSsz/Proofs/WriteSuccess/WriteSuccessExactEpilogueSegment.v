Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_126 Require Import instrs.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeContract.
Require Import ZesuSsz.Proofs.WriteSuccess.Interfaces.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactEpiloguePrefix.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactEpilogueReturnSegment.

Lemma write_success_exact_epilogue_segment
    `{!islaG Sigma} `{!threadG} {Decoded}
    (witness : writeSuccessNativeWitness Decoded) :
  ([∗ list] instruction ∈ IslaTraces.write_success_126.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x159d8
    (writeSuccessEpilogueSpec
      (writeSuccessExactEpilogueExit witness)).
Proof.
  iStartProof.
  zesu_expose_code_lists.
  iIntros "Hcode".
  zesu_reduce_introduced_code_lists.
  repeat iDestruct select (_ ∗ _)%I as "[? ?]".
  iRename select (instr 0x15a0c _)%I into "HaddSpCode".
  iRename select (instr 0x15a10 _)%I into "HreturnCode".
  iAssert (instr_body 0x15a0c
      (writeSuccessExactEpilogueAddSpSpec
        (writeSuccessExactEpilogueExit witness)))%I
    with "[HaddSpCode HreturnCode]" as "HreturnSegment".
  { iApply write_success_exact_epilogue_return_segment. iEval (cbn). iFrame. }
  iApply (write_success_exact_epilogue_prefix witness with "[-HreturnSegment] HreturnSegment").
  iEval (cbn). iFrame.
Qed.

Print Assumptions write_success_exact_epilogue_segment.
