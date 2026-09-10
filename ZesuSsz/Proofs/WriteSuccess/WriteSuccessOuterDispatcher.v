From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import InstrSpecs.Lookup.
Require Import InstrSpecs.Specs.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOuterBranch.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessValueBlock.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsValueAdapter.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Lemma write_success_outer_dispatcher_pre
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (values : list (bv 64)) (payload : list (bv 8))
    (tail : spec) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  □ writeSuccessTransactionsValueAdapter P -∗
  □ instr_pre 0x14f04 (writeSuccessTransactionsLoopSpec P) -∗
  □ instr_pre 0x15668 (writeSuccessValuePost sp values payload tail P) -∗
  □ instr_pre 0x14f04 (writeSuccessValuePost sp values payload tail P).
Proof.
  iStartProof. iIntros "#Hlookup #Hadapter #Hloop #Hexit".
  destruct (decide
    (default (BV 64 0) (values !! 8%nat) = BV 64 0)) as [Hzero | Hnonzero].
  - iModIntro. iApply instr_pre_to_body. iNext.
    iPoseProof (write_success_outer_empty_branch P with "Hlookup") as "Hempty".
    iApply (instr_pre_wand 0x14f04 0x14f04 false false with "Hempty");
      [done | reflexivity |].
    iIntros "Hpost".
    iEval (rewrite /writeSuccessOuterEmptySpec).
    iExists sp, values, payload, tail.
    iFrame "Hpost Hexit". iPureIntro. exact Hzero.
  - iPoseProof (write_success_outer_nonempty_transactions_pre P with
      "Hadapter Hloop") as "#HnonemptyPre".
    iModIntro.
    iApply (instr_pre_wand 0x14f04 0x14f04 true true with "HnonemptyPre");
      [done | reflexivity |].
    iIntros "Hpost".
    iEval (rewrite /writeSuccessOuterNonemptyValueSpec).
    iExists sp, values, payload, tail.
    iFrame "Hpost". iSplit; last done.
    iPureIntro. exact Hnonzero.
Qed.
