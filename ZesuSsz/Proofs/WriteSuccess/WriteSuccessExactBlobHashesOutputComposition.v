Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Continuations.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessOutput WriteSuccessExactBlobHashesWide
  WriteSuccessExactBlobHashesEmit WriteSuccessExactBlobHashesEmitHandoff.

Lemma blob_output_composed_correct `{!islaG Sigma} `{!threadG}
    row count base bytes index sp a b c d tail (P : iProp Sigma) :
  ([∗ list] instruction ∈ drop 17 IslaTraces.write_success_69.instrs.instr_map ++
    IslaTraces.write_success_70.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x10190 (writeOutputTraceSpec (sp + BV 64 1680)%bv (BV 64 32)
    (BV 64 0x15558) (take 32 (drop index bytes)) tail
    (blobEmitFrame sp (take 32 (drop index bytes))
      (blobEmitCallerFrame row count base bytes index P))) -∗
  instr_body 0x15558 (blobEmitPost sp (take 32 (drop index bytes)) tail
    (blobEmitCallerFrame row count base bytes index P)) -∗
  instr_body 0x15538 (blobWidePost row count base bytes index
    (blobOutputResources sp a b c d (take 32 (drop index bytes)) tail P)).
Proof.
  iStartProof. iIntros "#Hemit #Houtput Hnext".
  iAssert (instr_body 0x15538 (∃ old_ra old5 old11 : bv 64,
    blobEmitEntry sp old_ra old5 old11 a b c d (take 32 (drop index bytes)) tail
      (blobEmitCallerFrame row count base bytes index P))) with "[Hnext]" as "Hcall".
  { iApply instr_body_exists. iIntros (old_ra).
    iApply instr_body_exists. iIntros (old5).
    iApply instr_body_exists. iIntros (old11).
    iApply (blob_emit_correct sp old_ra old5 old11 a b c d
      (take 32 (drop index bytes)) tail
      (blobEmitCallerFrame row count base bytes index P) with "Hemit Houtput Hnext"). }
  iApply (instr_pre_wand 0x15538 0x15538 false false with "Hcall"); [done | reflexivity |].
  iApply (blob_wide_to_emit row count base bytes index sp a b c d tail P).
Qed.
Print Assumptions blob_output_composed_correct.
