Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Machine.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Experiments.WriteSuccessTactics.

Definition writeSuccessSuffixHashes15750NonzeroState
    `{!islaG Sigma} `{!threadG} (value : bv 64) (Q : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x8" ↦ᵣ RVal_Bits value ∗ Q)%I.

Global Instance : LithiumUnfold
  (@writeSuccessSuffixHashes15750NonzeroState) := I.

Lemma write_success_suffix_hashes_15750_nonzero_state
    `{!islaG Sigma} `{!threadG} (value : bv 64) (Q : iProp Sigma)
    (Hvalue : value <> BV 64 0) :
  instr 0x15750 (Some IslaTraces.write_success_102.a15750.a15750) -∗
  instr_pre 0x15754
    (writeSuccessSuffixHashes15750NonzeroState value Q) -∗
  instr_body 0x15750
    (writeSuccessSuffixHashes15750NonzeroState value Q).
Proof.
  iStartProof. iIntros "Hinstr Hnext".
  rewrite instr_pre'_eq. iIntros "Hentry".
  iEval (unfold writeSuccessSuffixHashes15750NonzeroState) in "Hentry".
  iDestruct "Hentry" as "(Hsys & H8 & HQ)".
  iExists (Some IslaTraces.write_success_102.a15750.a15750).
  iSplitL "Hinstr"; first iExact "Hinstr".
  iEval (rewrite -instr_pre'_eq) in "Hnext".
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try close_infeasible_bv_branches.
  all: try (exfalso; apply Hvalue; bv_solve).
  all: try bv_solve.
  all: try iFrame.
  Unshelve. all: try (exfalso; apply Hvalue; bv_solve).
  all: try iFrame.
  all: lazymatch goal with |- ?G => fail "state branch residual" G end.
Qed.
