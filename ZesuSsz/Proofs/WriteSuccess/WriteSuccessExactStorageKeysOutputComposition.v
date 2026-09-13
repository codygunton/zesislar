Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Continuations.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessOutput WriteSuccessExactStorageKeysWide WriteSuccessExactStorageKeysWords
  WriteSuccessExactStorageKeysEmit WriteSuccessExactStorageKeysEmitHandoff.

Lemma storage_keys_output_composed_correct `{!islaG Sigma} `{!threadG}
    row base bytes index sp a b c d tail (P : iProp Sigma) :
  ([∗ list] instruction ∈ take 8 (drop 8 IslaTraces.write_success_61.instrs.instr_map),
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ take 8 (drop 16 IslaTraces.write_success_61.instrs.instr_map),
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x10190 (writeOutputTraceSpec (sp + BV 64 1712)%bv (BV 64 32)
    (BV 64 0x153a8) (take 32 (drop index bytes)) tail
    (storageKeysEmitFrame sp (take 32 (drop index bytes))
      (storageKeysEmitCallerFrame row base bytes index P))) -∗
  instr_body 0x153a8 (storageKeysEmitPost sp (take 32 (drop index bytes)) tail
    (storageKeysEmitCallerFrame row base bytes index P)) -∗
  instr_body 0x15368 (storageKeysWordsPost row base bytes index
    (storageKeysOutputResources sp a b c d (take 32 (drop index bytes)) tail P)).
Proof.
  iStartProof. iIntros "#Hwide #Hemit #Houtput Hnext".
  iAssert (instr_body 0x15388 (∃ old_ra old5 old11 : bv 64,
    storageKeysEmitEntry sp old_ra old5 old11 a b c d (take 32 (drop index bytes)) tail
      (storageKeysEmitCallerFrame row base bytes index P))) with "[Hnext]" as "Hcall".
  { iApply instr_body_exists. iIntros (old_ra).
    iApply instr_body_exists. iIntros (old5).
    iApply instr_body_exists. iIntros (old11).
    iApply (storage_keys_emit_correct sp old_ra old5 old11 a b c d
      (take 32 (drop index bytes)) tail
      (storageKeysEmitCallerFrame row base bytes index P) with "Hemit Houtput Hnext"). }
  iApply (storage_keys_wide_correct row base bytes index
    (storageKeysOutputResources sp a b c d (take 32 (drop index bytes)) tail P)
    with "Hwide").
  iApply (instr_pre_wand 0x15388 0x15388 false false with "Hcall");
    [done | reflexivity |].
  iApply (storage_keys_wide_to_emit row base bytes index sp a b c d tail P).
Qed.
Print Assumptions storage_keys_output_composed_correct.
