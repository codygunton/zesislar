Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.MemoryWords.
Require Import ZesuSsz.Automation.Alignment.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactByteListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessByteLists.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactEncoderBytes.
From IslaTraces.write_success_05 Require Import instrs.
Import ZesuSsz.Automation.Calls.FramedContinuations.

Lemma byte_lists_exact_call_correct `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_05.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15c6c encoderBytesExactCallSpec -∗
  □ instr_pre 0x15c3c (byteListsExactLoopSpec P) -∗
  instr_body 0x15c4c (byteListsExactAfterCallSpec P) -∗
  instr_body 0x15c3c (byteListsExactLoopSpec P).
Proof.
  iStartProof. iIntros "#Hcode #Hencoder #Hloop Hnext".
  iEval (simpl) in "Hcode".
  repeat iDestruct select (instr _ _ ∗ _)%I as "(? & ?)".
  zesu_run.
  Unshelve.
  all: try zesu_finish.
  Unshelve.
  all: try zesu_pack (byteListsExactEncoderFrame P sp savedRa savedS0 savedS1
    pointer itemBase done item rest tail,
    byteListItemPayloadEvents sp rest tail, byteListBytes item,
    BV 64 0x15c4c, sp, byteListSize item, byteListData item, tt)ₗ.
  all: zesu_run.
  Unshelve. all: try zesu_alignment.
  all: try zesu_pack
    (tail, rest, item, done, itemBase, pointer, savedS1, savedS0, savedRa, sp, tt)ₗ.
  all: zesu_run.
  Unshelve. all: try zesu_alignment.
  all: try zesu_pack (tail, done, itemBase, tt)ₗ.
  all: zesu_run.
  Unshelve. all: try zesu_alignment.
  all: try zesu_pack
    (tail0, item0, done0, itemBase0, pointer0, savedS3, savedS2, savedRa0, sp0, tt)ₗ.
  all: zesu_run.
  Unshelve. all: try zesu_alignment.
Qed.
Print Assumptions byte_lists_exact_call_correct.

