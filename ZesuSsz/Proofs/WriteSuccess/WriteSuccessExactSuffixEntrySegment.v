Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Proofs.WriteSuccess.Interfaces.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessHashesLoop.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactEncoderIntCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessSuffixHashesEntryResources.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessSuffixHashesSourceWords.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessSuffixHashes15750Branch.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessSuffixHashesCallContinuations.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessSuffixHashesBranchAdapters.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessSuffixHashes15750EntryHandoff.
Require Import IslaTraces.write_success_102.a15750.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.

Lemma write_success_exact_suffix_entry_segment
    `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma)
    (sp pointer : bv 64) (base : Z)
    (total processed remaining : nat) (bytes : list (bv 8))
    (tail : spec) (HremainingBound : (S remaining < 2 ^ 64)%nat) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15d10 zesuEncoderIntExactCallSpec -∗
  □ instr_pre 0x15754
    (writeSuccessHashesLoopSpec ((bv_unsigned sp - 16) ↦ₘ? 16 ∗ P)) -∗
  instr_body 0x15744
    (writeSuccessSuffixHashesEntryPostSpec sp
      (Z_to_bv 64 (Z.of_nat (S remaining))) remaining tail
      (writeSuccessSuffixHashesEntryFrame
        sp pointer base total processed remaining bytes tail P)).
Proof.
  move => *.
  have HcountNonzero :
      Z_to_bv 64 (Z.of_nat (S remaining)) <> BV 64 0 :=
    zesu_nat_successor_bv64_nonzero remaining HremainingBound.
  iStartProof. iIntros "_ #Hlookup #Hcode #Hencoder #Hloop".
  zesu_expose_code_lists; zesu_reduce_introduced_code_lists.
  repeat iDestruct select (_ ∗ _)%I as "[? ?]".
  zesu_run.
  iExists (WriteSuccessEvents.writeOutputEventsAny
    (sp + BV 64 1744)%bv (BV 64 32)
    (writeSuccessHashesEvents sp remaining tail), tt)ₗ.
  zesu_run.
  1: (unfold subseteq, spec_subseteq, scons, scons_snap; naive_solver).
  have Hret :
      (Z_to_bv 64 0x1574c + BV 64 4)%bv = BV 64 0x15750 by bv_solve.
  rewrite Hret bv_unsigned_BV; cbn.
  zesu_run.
  iSplit; last done. iIntros "Hreturn HPC".
  zesu_run.
  iEval (unfold encoderIntExactReturn) in "Hreturn".
  iDestruct "Hreturn" as
    "(Hsys & H1r & H2r & H5r & H10r & H11r & Hstack & Hmmio & Htrace & _)".
  zesu_run.
  zesu_run.
  iRename select
    (writeSuccessSuffixHashesCallerBundle
      sp pointer base total processed remaining bytes tail P)
    into "Hcaller".
  iEval (rewrite writeSuccessSuffixHashesCallerBundle_unfold) in "Hcaller".
  iDestruct "Hcaller" as "(Hother & Hbytes & HP & Hinvariant & Hexit)".
  zesu_run.
  iExists (tail, bytes, processed, total, base, tt)ₗ.
  iFrame.
Qed.

Print Assumptions write_success_exact_suffix_entry_segment.
