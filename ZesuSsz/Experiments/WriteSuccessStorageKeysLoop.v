From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import
  Index HintsHashesLoop HintsBlobHashesLoop HintsStorageKeysLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccess.
Require Import ZesuSsz.Experiments.WriteSuccessCalls.

Import ListNotations.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.
Require Import ZesuSsz.Experiments.WriteSuccessStorageKeysSpec.
Require Import ZesuSsz.Experiments.WriteSuccessStorageKeysSegment01.
Require Import ZesuSsz.Experiments.WriteSuccessStorageKeysSegment02.
Require Import ZesuSsz.Experiments.WriteSuccessStorageKeysSegment03.
Require Import ZesuSsz.Experiments.WriteSuccessStorageKeysSegment04.
Require Import ZesuSsz.Experiments.WriteSuccessStorageKeysSegment05.
Require Import ZesuSsz.Experiments.WriteSuccessStorageKeysSegment06.
Require Import ZesuSsz.Experiments.WriteSuccessStorageKeysSegment07.
Require Import ZesuSsz.Experiments.WriteSuccessStorageKeysSegment08.
Require Import ZesuSsz.Experiments.WriteSuccessStorageKeysSegment09.
Require Import ZesuSsz.Experiments.WriteSuccessStorageKeysSegment10.
Require Import ZesuSsz.Experiments.WriteSuccessStorageKeysSegment11.
Require Import ZesuSsz.Experiments.WriteSuccessStorageKeysSegment12.
Require Import ZesuSsz.Experiments.WriteSuccessStorageKeysSegment13.
Require Import ZesuSsz.Experiments.WriteSuccessStorageKeysSegment14.
Require Import ZesuSsz.Experiments.WriteSuccessStorageKeysSegment15.
Require Import ZesuSsz.Experiments.WriteSuccessStorageKeysSegment16.
Require Import ZesuSsz.Experiments.WriteSuccessStorageKeysSegment17.
Require Import ZesuSsz.Experiments.WriteSuccessStorageKeysSegment18.
Require Import ZesuSsz.Experiments.WriteSuccessStorageKeysSegment19.
Require Import ZesuSsz.Experiments.WriteSuccessStorageKeysSegment20.
Require Import ZesuSsz.Experiments.WriteSuccessStorageKeysOutput.
Require Import ZesuSsz.Experiments.WriteSuccessStorageKeysTail.
#[local] Hint Extern 7
  (FindInContext (FindInstrKind ?address ?later) FICSyntactic) =>
  let reduced := eval vm_compute in address in
  first [ constr_eq address reduced; fail 1
        | change (FindInContext (FindInstrKind reduced later) FICSyntactic);
          typeclasses eauto ] : typeclass_instances.

Lemma write_success_storage_keys_loop `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  □ instr_pre 0x15228 (writeSuccessStorageKeysLoopSpec P) -∗
  instr_body 0x15228 (writeSuccessStorageKeysLoopSpec P).
Proof.
  iStartProof. iIntros "#Hlookup #Hcode #Houtput #Hloop".
  iApply (write_success_storage_keys_a P with "Hlookup Hcode").
  iApply (write_success_storage_keys_b P with "Hlookup Hcode").
  iApply (write_success_storage_keys_c P with "Hlookup Hcode").
  iApply (write_success_storage_keys_d P with "Hlookup Hcode").
  iApply (write_success_storage_keys_e P with "Hlookup Hcode").
  iApply (write_success_storage_keys_f P with "Hlookup Hcode").
  iApply (write_success_storage_keys_g P with "Hlookup Hcode").
  iApply (write_success_storage_keys_h P with "Hlookup Hcode").
  iApply (write_success_storage_keys_i P with "Hlookup Hcode").
  iApply (write_success_storage_keys_j P with "Hlookup Hcode").
  iApply (write_success_storage_keys_k P with "Hlookup Hcode").
  iApply (write_success_storage_keys_l P with "Hlookup Hcode").
  iApply (write_success_storage_keys_m P with "Hlookup Hcode").
  iApply (write_success_storage_keys_n P with "Hlookup Hcode").
  iApply (write_success_storage_keys_o P with "Hlookup Hcode").
  iApply (write_success_storage_keys_p P with "Hlookup Hcode").
  iApply (write_success_storage_keys_q P with "Hlookup Hcode").
  iApply (write_success_storage_keys_r P with "Hlookup Hcode").
  iApply (write_success_storage_keys_s P with "Hlookup Hcode").
  iApply (write_success_storage_keys_t P with "Hlookup Hcode").
  iApply (write_success_storage_keys_output P with
    "Hlookup Hcode Houtput").
  iApply (write_success_storage_keys_tail P with
    "Hlookup Hcode Houtput Hloop").
Qed.
Lemma write_success_storage_keys_loop_pre `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  □ instr_pre 0x15228 (writeSuccessStorageKeysLoopSpec P).
Proof.
  iStartProof. iIntros "#Hlookup #Hcode #Houtput".
  iLöb as "IH".
  iModIntro. iApply instr_pre_to_body. iNext.
  iApply (write_success_storage_keys_loop P with
    "Hlookup Hcode Houtput IH").
Qed.
