Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPost15668DataStates.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPost15674Boundary.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Lemma write_success_transactions_post_15670_data
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  instr_body 0x15674 (writeSuccessTransactionsPost15674DataSpec P) -∗
  instr_body 0x15670 (writeSuccessTransactionsPost15670DataSpec P).
Proof.
  move => *. iStartProof. iIntros "#Hlookup Hnext".
  liARun.
  all: destruct H0 as
    (HsecondLength & HitemsLength & HfirstAlign & HfirstLower & HfirstUpper &
     HspExtract & HspCallLower & HspMax).
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve.
  all: try exact inhabitant.
  all: try bv_solve.
  Unshelve.
  all: iExists (items, count, tail, bytes, transactions, base, pointer, tt)ₗ.
  all: iRename select (mmio_range 0x2401a0c0 16)%I into "Hmmio".
  all: iFrame.
  all: repeat iSplit; try iPureIntro; try assumption; try lia.
  all: try iExact "Hmmio".
Qed.
