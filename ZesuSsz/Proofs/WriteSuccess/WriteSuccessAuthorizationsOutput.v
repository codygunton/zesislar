Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index HintsAuthorizationsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Experiments.WriteSuccessCalls.
Require Import ZesuSsz.Experiments.WriteSuccessAuthorizationsSpec.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Lemma write_success_authorizations_output `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  instr_body 0x155cc
    (writeSuccessAuthorizationsCopiedSpec AuthorizationsFirstInt P) -∗
  instr_body 0x155bc
    (writeSuccessAuthorizationsCopiedSpec AuthorizationsOutput P).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode #Houtput Hnext".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  run_write_success_authorizations_chunk 0x155cc.
  Unshelve. all: try run_write_success_authorizations_return 0x155cc.
  all: try prepare_sidecond.
  all: try assumption.
  all: try iFrame.
  all: try bv_solve.
  all: try lia.
  Unshelve.
  iExists
    (tail, suffix, prefix, prefix ++ suffix, processed,
     (processed + S remaining)%nat, base, tt)ₗ.
  liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
Qed.
