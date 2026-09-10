Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import
  Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCalls.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsBoundary15200.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsBoundary15210.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Remove Hints writeSuccessAccessEntryStorageOwn_unfold :
  typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.
#[local] Hint Extern 7
  (FindInContext (FindInstrKind ?address ?later) FICSyntactic) =>
  let reduced := eval vm_compute in address in
  first [ constr_eq address reduced; fail 1
        | change (FindInContext (FindInstrKind reduced later) FICSyntactic);
          typeclasses eauto ] : typeclass_instances.

Lemma write_success_access_lists_chunk_15200
    `{!islaG Sigma} `{!threadG} (x19 : bv 64) (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  instr_body 0x15210 (writeSuccessAccessListsAt15210Spec x19 P) -∗
  instr_body 0x15200 (writeSuccessAccessListsAt15200Spec x19 P).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode #Houtput Hnext".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  run_write_success_access_lists_chunk 0x15210.
  Unshelve. all: try run_write_success_access_lists_return 0x15210.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve. all: try liARun.
  Unshelve.
  iExists
    (tail, savedX22,
     (writeSuccessAccessEntryBytes entry ++
      writeSuccessAccessEntriesBytes remaining),
     writeSuccessAccessEntriesBytes processed,
     writeSuccessAccessEntriesBytes (processed ++ entry :: remaining),
     remaining, processed, (processed ++ entry :: remaining), entry,
     base, tt)ₗ.
  liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
Qed.
