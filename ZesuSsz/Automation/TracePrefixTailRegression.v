Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.Sets.call.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.

(* The root pointer event must remain beside the root length event. *)
Lemma zesu_bytes_root_tail_regression `{!islaG Sigma} `{!threadG}
    (data size root : bv 64) (bytes : list (bv 8)) (tail : spec) :
  instr_pre 0x1572c
    (spec_trace (scons (SWriteMem (BV 64 604086464) (bv_to_bvn root))
      (scons (SWriteMem (BV 64 604086472) (BV 64 32)) tail)) ∗ True) -∗
  ∃ x : spec *ₗ unit,
    ⌜writeOutputEvents data size bytes x.1ₗ ⊆
      writeOutputEvents data size bytes
        (scons (SWriteMem (BV 64 604086464) (bv_to_bvn root))
      (scons (SWriteMem (BV 64 604086472) (BV 64 32)) tail))⌝ ∗
    instr_pre 0x1572c (spec_trace x.1ₗ ∗ True).
Proof.
  iIntros "Hreturn". zesu_run.
Qed.
Print Assumptions zesu_bytes_root_tail_regression.
