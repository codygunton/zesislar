(* The marker remains local to this segment test. *)

Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.SpecTable.
Require Import ZesuSsz.Automation.MarkedRawLookup.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.

Local Instance pw_raw_at_156e8 :
    ZesuRawTraceAt Index.lookup 0x156e8.
Proof.
  unfold ZesuRawTraceAt, is_Some.
  eexists. exact Index.lookup_a156e8.
Qed.

Lemma test_pw_raw_at_87784 `{!islaG Sigma} `{!threadG} :
  instr_lookup_resources Index.lookup -∗
  Index.spec_instr_resources -∗
  find_in_context (FindInstrKind 87784 false)
    (fun kind => ⌜kind = IKInstr (Index.lookup 87784)⌝).
Proof.
  iIntros "#Hcode #Htable".
  zesu_run.
Qed.
Print Assumptions test_pw_raw_at_87784.

Lemma test_pw_table_at_87792 `{!islaG Sigma} `{!threadG} :
  instr_lookup_resources Index.lookup -∗
  Index.spec_instr_resources -∗
  find_in_context (FindInstrKind 87792 false)
    (fun kind => ⌜kind = IKPre false
      (zesu_jalr_same_spec 87792 "x1" (BV 64 1572))⌝).
Proof.
  iIntros "#Hcode #Htable".
  zesu_run.
Qed.
Print Assumptions test_pw_table_at_87792.
