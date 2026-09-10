From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import
  Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsBoundary151dc.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsLoopExitBytes.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsLoopContinuation.

Lemma write_success_access_lists_loop_entry
    `{!islaG Sigma} `{!threadG} (x19 : bv 64) (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ writeSuccessAccessListsAt151dcBody x19 P -∗
  instr_body 0x151d4 (writeSuccessAccessListsLoopSpec x19 P).
Proof.
  iStartProof.
  iIntros "#Hlookup #Hcode #Hnext".
  liARun.
  Unshelve.
  all: destruct remaining as [|entry remaining].
  all: try prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  all: try (iExists (storedIndex, tt)ₗ; cbn; iFrame).
  all: try (iExists
    (tail, savedX22, storedIndex,
      writeSuccessAccessEntriesBytes (entry :: remaining),
      writeSuccessAccessEntriesBytes processed,
      writeSuccessAccessEntriesBytes (processed ++ entry :: remaining),
      remaining, entry, base, tt)ₗ;
    cbn; iFrame).
  all: try (eapply write_success_access_lists_exit_bytes;
    [exact H4 | exact H11]).
  Unshelve.
  - iExists (storedIndex, tt)ₗ. cbn. iFrame.
    rewrite app_nil_r. iFrame. iFrame "#".
  - exfalso.
    have Hnil := write_success_access_lists_exit_remaining_nil
      processed (entry :: remaining) H4 H11.
    discriminate Hnil.
  - exfalso. apply H11. rewrite app_nil_r. reflexivity.
  - iExists
      (tail, savedX22, storedIndex,
        writeSuccessAccessEntriesBytes (entry :: remaining),
        writeSuccessAccessEntriesBytes processed,
        writeSuccessAccessEntriesBytes (processed ++ entry :: remaining),
        remaining, entry, base, tt)ₗ.
    cbn. iFrame. iFrame "#".
    rewrite /writeSuccessAccessListsInvariant.
    repeat iSplit; iPureIntro; try reflexivity; try assumption.
Qed.
