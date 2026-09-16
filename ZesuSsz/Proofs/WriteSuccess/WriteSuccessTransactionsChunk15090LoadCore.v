Require Import ZesuSsz.Automation.AllLegacy.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Specs.
Require Import IslaTraces.write_success_33.a15090_spec.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary14f1c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk15090LoadState.

Local Remove Hints a15090_spec_inst : typeclass_instances.
Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Lemma write_success_transactions_chunk_15090_load_core
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
  instr 0x15090 (Some IslaTraces.write_success_33.a15090.a15090) -∗
  instr_body 0x15094
    (writeSuccessTransactions15090LoadResult P sp base transaction
      transactions processed remaining bytes prefix suffix tail) -∗
  instr_body 0x15090
    (writeSuccessTransactions15090LoadState P sp base transaction
      transactions processed remaining bytes prefix suffix tail).
Proof.
  iIntros "#Hinstr Hnext".
  iPoseProof (IslaTraces.write_success_33.a15090_spec.a15090_spec 0x15090
    with "Hinstr") as "Hload".
  rewrite instr_pre'_eq. iIntros "Hstate".
  rewrite /writeSuccessTransactions15090LoadState.
  iDestruct "Hstate" as
    "(Hsys & Hx15 & Hx10 & Hprefix & Hword & Hsuffix & HmachineFrame &
      Hphase & Hfacts & %Hcurrent & _)".
  iEval (unfold writeSuccessTransactionsLoadFacts) in "Hfacts".
  iDestruct "Hfacts" as
    "(%Hlength & %Halign & %Hlower & %Hupper & %HspAlign & %HspLower &
      %HspUpper & _)".
  iAssert (("x15" ↦ᵣ: fun _ => True))%I with "[Hx15]" as "Hx15Any".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists _. iSplit; first iExact "Hx15". done. }
  iApply "Hload".
  rewrite /InstrSpecs.Specs.zesu_ld_byte_array_at_spec.
  iExists
    (Z_to_bv 64 (base + 288 * Z.of_nat (length processed))),
    (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
      transaction 128),
    (WriteSuccessTransactionsSpec.writeSuccessTransactionBytes transaction).
  rewrite Hcurrent !Z.add_0_r.
  iFrame "Hsys Hx15Any Hx10 Hword Hprefix Hsuffix".
  iSplit; first by iPureIntro; reflexivity.
  iSplit; first by iPureIntro; rewrite Hlength; lia.
  iSplit; first by iPureIntro; reflexivity.
  iSplit; first by iPureIntro; exact Halign.
  iSplit; first by iPureIntro; lia.
  iEval (rewrite -instr_pre'_eq) in "Hnext".
  iApply (instr_pre_wand with "Hnext").
  { done. }
  { reflexivity. }
  iIntros "Hpost".
  iDestruct "Hpost" as
      "(Hsys & Hx15 & Hx10 & Hword & Hprefix & Hsuffix & _)".
  iSpecialize ("HmachineFrame" $!
      (RVal_Bits
        (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
          transaction 128)) with "Hsys Hx15 Hx10").
  rewrite /writeSuccessTransactions15090LoadResult.
  iFrame "HmachineFrame Hprefix Hword Hsuffix Hphase".
  rewrite /writeSuccessTransactionsLoadFacts.
  repeat iSplit; try iPureIntro; try assumption; try done.
Qed.
