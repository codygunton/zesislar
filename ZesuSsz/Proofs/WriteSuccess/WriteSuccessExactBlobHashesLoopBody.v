Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactBlobHashesSpec WriteSuccessExactBlobHashesBody
  WriteSuccessExactBlobHashesLoopEntry WriteSuccessExactBlobHashesLoopReturn
  WriteSuccessExactBlobHashesTailNative WriteSuccessExactBlobHashesTail
  WriteSuccessExactBlobHashesModel WriteSuccessExactBlobHashesEmit
  WriteSuccessExactBlobHashesEmitHandoff WriteSuccessOutput.

Lemma blob_loop_body `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (total : nat) (bytes : list (bv 8)) (tail : spec) (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_66.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_67.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_68.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_69.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_70.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_71.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x153d4 (writeSuccessExactBlobHashesLoopSpec sp base total bytes tail P) -∗
  instr_body 0x153d4 (writeSuccessExactBlobHashesLoopSpec sp base total bytes tail P).
Proof.
  iStartProof. iIntros "#H66 #H67 #H68 #H69 #H70 #H71 #Houtput #IH".
  iEval (rewrite instr_pre'_eq). iIntros "Hentry".
  iEval (unfold writeSuccessExactBlobHashesLoopSpec) in "Hentry".
  iDestruct "Hentry" as (pointer processed remaining) "Hentry".
  iPoseProof (blob_loop_entry_resources sp pointer base total processed remaining bytes tail P
    with "Hentry") as "Hloads".
  iDestruct "Hloads" as (old26 a b c d) "Hloads".
  iPoseProof (blob_tail_native sp pointer base total processed remaining bytes tail P
    with "H71 IH") as "Htail".
  iPoseProof (instr_pre_wand 0x15558 0x15558 false false with "Htail []") as "Hnext".
  1: done. 1: reflexivity.
  { iIntros "Hpost". iApply (blob_output_to_tail with "Hpost"). }
  iPoseProof (blob_body_correct pointer (Z_to_bv 64 (Z.of_nat (S remaining))) base bytes (32 * processed) old26 sp a b c d
    (writeSuccessExactBlobHashesEvents sp (S processed) remaining bytes tail) (blobLoopFrame sp pointer base total processed remaining bytes tail P)
    with "H66 H67 H68 H69 H70 Houtput Hnext") as "Hbody".
  iEval (rewrite instr_pre'_eq) in "Hbody". iApply ("Hbody" with "Hloads").
Qed.
Print Assumptions blob_loop_body.
