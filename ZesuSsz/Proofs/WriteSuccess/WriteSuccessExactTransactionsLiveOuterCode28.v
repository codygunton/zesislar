Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.CodeLookup.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_28 Require Import instrs.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeCode.

Lemma transactions_live_outer_code28 `{!islaG Sigma} `{!threadG} :
  writeSuccessCompleteNativeCode -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_28.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I.
Proof.
  iStartProof. iIntros "#Hcode".
  iEval (unfold writeSuccessCompleteNativeCode) in "Hcode".
  iDestruct "Hcode" as
    "#(Hprologue & Hlookup & Hmain & Houtput & Hmemcpy & Hboolean &
       Hoptional & HbyteLists & Hbytes & Hint & Hu256 & Hu128)".
  iApply instr_lookup_collect; last iExact "Hlookup".
  repeat constructor; reflexivity.
Qed.
Print Assumptions transactions_live_outer_code28.
