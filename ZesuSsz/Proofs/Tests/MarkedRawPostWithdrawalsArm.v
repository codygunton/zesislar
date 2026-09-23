(* Benchmark-only marker for the post-withdrawals entry load. *)
Require Import ZesuSsz.Automation.All.
Require Export ZesuSsz.Automation.Sets.v2.
Require Export ZesuSsz.Automation.MarkedRawInstruction.
Require Export ZesuSsz.Automation.Switches.MarkedRawInstruction.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.

Global Instance marked_raw_post_withdrawals_entry :
    ZesuRawInstructionAt Index.lookup 0x156e8.
Proof. unfold ZesuRawInstructionAt. rewrite Index.lookup_a156e8. eexists. reflexivity. Qed.

Print Assumptions marked_raw_post_withdrawals_entry.
