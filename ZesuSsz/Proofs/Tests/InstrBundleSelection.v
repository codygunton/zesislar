Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_69 Require Import instrs.
From IslaTraces.write_success_70 Require Import instrs.
From IslaTraces.write_success_59 Require Import instrs.
From IslaTraces.write_success_60 Require Import instrs.

Lemma instr_bundle_select_blob `{!islaG Sigma} `{!threadG} :
  (instr 87352 (Some a15538) ∗ instr 87356 (Some a1553c) ∗
   instr 87360 (Some a15540) ∗ instr 87364 (Some a15544) ∗
   instr 87368 (Some a15548) ∗ instr 87372 (Some a1554c) ∗
   instr 87376 (Some a15550) ∗ instr 87380 (Some a15554) ∗ emp)%I -∗
  find_in_context (FindInstrKind 87352 false)
    (fun kind => match kind with IKInstr (Some _) => True%I | _ => False%I end).
Proof.
  iStartProof. iIntros "Hbundle". zesu_run.
Qed.
Print Assumptions instr_bundle_select_blob.

Lemma instr_bundle_select_storage `{!islaG Sigma} `{!threadG} :
  (instr 86748 (Some a152dc) ∗ instr 86752 (Some a152e0) ∗
   instr 86756 (Some a152e4) ∗ instr 86760 (Some a152e8) ∗ emp)%I -∗
  find_in_context (FindInstrKind 86748 false)
    (fun kind => match kind with IKInstr (Some _) => True%I | _ => False%I end).
Proof.
  iStartProof. iIntros "Hbundle". zesu_run.
Qed.
Print Assumptions instr_bundle_select_storage.
