Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_113.a15930_spec.
Require Import IslaTraces.write_success_113.a15934_spec.

Lemma write_success_post_15930_load_pointer
    `{!islaG Sigma} `{!threadG} :
  instr 0x15930 (Some IslaTraces.write_success_113.a15930.a15930) -∗
  instr_body 0x15930
    (InstrSpecs.Specs.zesu_ld_spec 0x15930 "x10" "x2" 24).
Proof.
  iIntros "Hinstr".
  iApply (IslaTraces.write_success_113.a15930_spec.a15930_spec
    0x15930 with "Hinstr").
Qed.

Lemma write_success_post_15934_load_count
    `{!islaG Sigma} `{!threadG} :
  instr 0x15934 (Some IslaTraces.write_success_113.a15934.a15934) -∗
  instr_body 0x15934
    (InstrSpecs.Specs.zesu_ld_spec 0x15934 "x11" "x2" 16).
Proof.
  iIntros "Hinstr".
  iApply (IslaTraces.write_success_113.a15934_spec.a15934_spec
    0x15934 with "Hinstr").
Qed.

