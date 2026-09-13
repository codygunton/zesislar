Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactStorageKeysSpec WriteSuccessExactStorageKeysBody
  WriteSuccessExactStorageKeysLoopEntry WriteSuccessExactStorageKeysLoopReturn
  WriteSuccessExactStorageKeysTailNative WriteSuccessExactStorageKeysTail
  WriteSuccessExactStorageKeysModel
  WriteSuccessExactStorageKeysEmit WriteSuccessExactStorageKeysEmitHandoff
  WriteSuccessOutput.

Lemma storage_keys_loop_body `{!islaG Sigma} `{!threadG}
    (x19 : bv 64) (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_58.instrs.instr_map, instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_59.instrs.instr_map, instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_60.instrs.instr_map, instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_61.instrs.instr_map, instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_62.instrs.instr_map, instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map, instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15228 (writeSuccessExactStorageKeysLoopSpec x19 P) -∗
  instr_body 0x15228 (writeSuccessExactStorageKeysLoopSpec x19 P).
Proof.
  iStartProof. iIntros "#H58 #H59 #H60 #H61 #H62 #Houtput #IH".
  iEval (rewrite instr_pre'_eq). iIntros "Hentry".
  iEval (unfold writeSuccessExactStorageKeysLoopSpec) in "Hentry".
  iDestruct "Hentry" as (sp pointer base total processed remaining bytes tail) "Hentry".
  iPoseProof (storage_keys_loop_entry_resources x19 sp pointer base total processed remaining bytes tail P
    with "Hentry") as "Hloads".
  iDestruct "Hloads" as (old21 a b c d) "Hloads".
  iPoseProof (storage_keys_tail_native x19 sp pointer base total processed remaining bytes tail P
    with "H62 IH") as "Htail".
  iPoseProof (instr_pre_wand 0x153a8 0x153a8 false false with "Htail []") as "Hnext".
  1: done. 1: reflexivity.
  { iIntros "Hpost". iApply (storage_keys_output_to_tail with "Hpost"). }
  iAssert (□ instr_pre 0x10190 (writeOutputTraceSpec (sp + BV 64 1712)%bv (BV 64 32)
    (BV 64 0x153a8) (take 32 (drop (32 * processed) bytes))
    (writeSuccessExactStorageKeysEvents sp (S processed) remaining bytes tail)
    (storageKeysEmitFrame sp (take 32 (drop (32 * processed) bytes))
      (storageKeysEmitCallerFrame pointer base bytes (32 * processed)
        (storageKeysLoopFrame x19 sp pointer base total processed remaining bytes tail P)))))%I as "#Hcallee".
  { iModIntro. iApply instr_pre_to_body. iNext.
    iApply (write_output_trace_correct with "Houtput"). }
  iPoseProof (storage_keys_body_correct pointer base bytes (32 * processed) old21 sp a b c d
    (writeSuccessExactStorageKeysEvents sp (S processed) remaining bytes tail)
    (storageKeysLoopFrame x19 sp pointer base total processed remaining bytes tail P)
    with "H58 H59 H60 H61 Hcallee Hnext") as "Hbody".
  iEval (rewrite instr_pre'_eq) in "Hbody". iApply ("Hbody" with "Hloads").
Qed.
Print Assumptions storage_keys_loop_body.
