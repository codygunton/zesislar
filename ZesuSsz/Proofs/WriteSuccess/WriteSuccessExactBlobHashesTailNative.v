Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.CounterShapes.
Require Import ZesuSsz.Automation.CounterZero.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessBlobHashesSpec WriteSuccessLoopCommon WriteSuccessExactBlobHashesModel
  WriteSuccessExactBlobHashesLoopReturn WriteSuccessExactBlobHashesTail
  WriteSuccessExactBlobHashesSpec WriteSuccessExactBlobHashesTailZero WriteSuccessExactBlobHashesTailGuard.

Lemma blob_tail_native `{!islaG Sigma} `{!threadG}
    (sp pointer : bv 64) base total processed remaining bytes tail (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_71.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x153d4 (writeSuccessExactBlobHashesLoopSpec sp base total bytes tail P) -∗
  instr_body 0x15558 (∃ value22 : bv 64,
    blobTailState pointer (Z_to_bv 64 (Z.of_nat (S remaining))) value22 (blobTailFrame sp pointer base total processed remaining bytes tail P)).
Proof.
  zesu_block.
  liInst (fun x => x.1ₗ = S processed).
  zesu_run.
Qed.
Print Assumptions blob_tail_native.
