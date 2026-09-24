Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_101.a15740_spec.

Lemma write_success_suffix_hashes_a15740_raw
    `{!islaG Sigma} `{!threadG} :
  instr 0x15740 (Some IslaTraces.write_success_101.a15740.a15740) -∗
  instr_body 0x15740
    (InstrSpecs.Specs.zesu_ld_spec 0x15740 "x8" "x2" 912).
Proof. move => *. zesu_block. Qed.
