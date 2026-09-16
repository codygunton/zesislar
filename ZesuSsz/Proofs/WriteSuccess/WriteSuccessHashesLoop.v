Require Import ZesuSsz.Automation.AllLegacy.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import
  Index HintsHashesLoop HintsBlobHashesLoop HintsStorageKeysLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccess.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCalls.

Import ListNotations.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessLoopCommon.
#[local] Hint Extern 7
  (FindInContext (FindInstrKind ?address ?later) FICSyntactic) =>
  let reduced := eval vm_compute in address in
  first [ constr_eq address reduced; fail 1
        | change (FindInContext (FindInstrKind reduced later) FICSyntactic);
          typeclasses eauto ] : typeclass_instances.

From ZesuSsz.Proofs.WriteSuccess Require Export
  WriteSuccessHashesLoopSpec
  WriteSuccessHashesLoopWord3
  WriteSuccessHashesLoopWord2
  WriteSuccessHashesLoopWord1
  WriteSuccessHashesLoopWord0
  WriteSuccessHashesLoopTail.

Lemma write_success_hashes_loop `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  □ instr_pre 0x15754 (writeSuccessHashesLoopSpec P) -∗
  instr_body 0x15754 (writeSuccessHashesLoopSpec P).
Proof.
  iStartProof. iIntros "#Hlookup #Hcode #Houtput #Hloop".
  iApply (write_success_hashes_word3 P with "Hlookup Hcode").
  iApply (write_success_hashes_word2 P with "Hlookup Hcode").
  iApply (write_success_hashes_word1 P with "Hlookup Hcode").
  iApply (write_success_hashes_word0 P with "Hlookup Hcode").
  iApply (write_success_hashes_tail P with
    "Hlookup Hcode Houtput Hloop").
Qed.

Lemma write_success_hashes_loop_pre `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  □ instr_pre 0x15754 (writeSuccessHashesLoopSpec P).
Proof.
  iStartProof. iIntros "#Hlookup #Hcode #Houtput".
  iLöb as "IH".
  iModIntro. iApply instr_pre_to_body. iNext.
  iApply (write_success_hashes_loop P with "Hlookup Hcode Houtput IH").
Qed.

Print Assumptions write_success_hashes_loop.
Print Assumptions write_success_hashes_loop_pre.
