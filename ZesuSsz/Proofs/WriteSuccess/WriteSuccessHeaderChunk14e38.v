Require Import ZesuSsz.Automation.AllLegacy.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCallAbi.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCalls.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessHeaderSpec.

Local Remove Hints
  InstrSpecs.Lookup.find_in_context_instr_body_lookup_resources_inst
  : typeclass_instances.

Ltac run_header_output :=
  lazymatch goal with
  | |- instr_body 0x14e48 _ => idtac
  | _ =>
      first
        [ progress iEval (unfold zesuWriteOutputCallSpec, zesu_c_call)
        | liAStep
        | progress prepare_sidecond
        | reflexivity
        | vm_compute
        | bv_solve
        | lia ];
      run_header_output
  end.

Lemma write_success_header_chunk_14e38 `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (bytes : list (bv 8)) (tail : spec) (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  instr_body 0x14e48
    (writeSuccessHeaderAfterCopySpec sp bytes
      (writeSuccessHeaderEventsAfter1216 sp tail) tail P) -∗
  instr_body 0x14e38
    (writeSuccessHeaderAfterCopySpec sp bytes
      (writeSuccessHeaderEventsAfter1184 sp tail) tail P).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode #Houtput Hnext".
  run_header_output.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
Qed.
