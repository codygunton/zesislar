Require Import ZesuSsz.Automation.AllLegacy.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsTailBoundaries.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsTailState.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsChunk153b4Load.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsChunk153b8.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsChunk153bc.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Lemma write_success_access_lists_tail
    `{!islaG Sigma} `{!threadG} (x19 : bv 64) (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x151d4 (writeSuccessAccessListsLoopSpec x19 P) -∗
  instr_body 0x153b4 (writeSuccessAccessListsTailSpec x19 P).
Proof.
  iStartProof.
  iIntros "#Hlookup #Hcode #Hloop".
  iAssert (□ instr_pre 0x151d4
      (writeSuccessAccessListsAt153bcSpec x19 P))%I with "[]" as
      "#Hloop153bc".
  { iModIntro.
    iApply (instr_pre_wand 0x151d4 0x151d4 true true with "Hloop");
      [done | reflexivity |].
    iIntros "Hentry".
    iApply (write_success_access_lists_153bc_to_loop x19 P with "Hentry"). }
  iAssert (instr_body 0x153b4
      (writeSuccessAccessListsAt153b4SplitSpec x19 P))%I with "[]" as
      "Hsplit".
  { iApply (write_success_access_lists_chunk_153b4_load x19 P with
      "Hlookup Hcode").
    iApply (write_success_access_lists_chunk_153b8 x19 P with
      "Hlookup Hcode").
    iApply (write_success_access_lists_chunk_153bc x19 P with
      "Hlookup Hcode Hloop153bc"). }
  iApply (instr_pre_wand 0x153b4 0x153b4 false false with "Hsplit");
    [done | reflexivity |].
  iIntros "Htail".
  iApply (write_success_access_lists_tail_to_153b4 x19 P with "Htail").
Qed.
