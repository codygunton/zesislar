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
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessStorageKeysSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessStorageKeysSegment01.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessStorageKeysSegment02.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessStorageKeysSegment03.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessStorageKeysSegment04.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessStorageKeysSegment05.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessStorageKeysSegment06.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessStorageKeysSegment07.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessStorageKeysSegment08.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessStorageKeysSegment09.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessStorageKeysSegment10.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessStorageKeysSegment11.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessStorageKeysSegment12.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessStorageKeysSegment13.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessStorageKeysSegment14.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessStorageKeysSegment15.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessStorageKeysSegment16.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessStorageKeysSegment17.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessStorageKeysSegment18.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessStorageKeysSegment19.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessStorageKeysSegment20.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessStorageKeysOutput.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessStorageKeysTail.
#[local] Hint Extern 7
  (FindInContext (FindInstrKind ?address ?later) FICSyntactic) =>
  let reduced := eval vm_compute in address in
  first [ constr_eq address reduced; fail 1
        | change (FindInContext (FindInstrKind reduced later) FICSyntactic);
          typeclasses eauto ] : typeclass_instances.

Lemma write_success_storage_keys_loop `{!islaG Sigma} `{!threadG}
    (x19 : bv 64) (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  □ instr_pre 0x15228 (writeSuccessStorageKeysLoopSpec x19 P) -∗
  instr_body 0x15228 (writeSuccessStorageKeysLoopSpec x19 P).
Proof.
  iStartProof. iIntros "#Hlookup #Hcode #Houtput #Hloop".
  iApply (write_success_storage_keys_a x19 P with "Hlookup Hcode").
  iApply (write_success_storage_keys_b x19 P with "Hlookup Hcode").
  iApply (write_success_storage_keys_c x19 P with "Hlookup Hcode").
  iApply (write_success_storage_keys_d x19 P with "Hlookup Hcode").
  iApply (write_success_storage_keys_e x19 P with "Hlookup Hcode").
  iApply (write_success_storage_keys_f x19 P with "Hlookup Hcode").
  iApply (write_success_storage_keys_g x19 P with "Hlookup Hcode").
  iApply (write_success_storage_keys_h x19 P with "Hlookup Hcode").
  iApply (write_success_storage_keys_i x19 P with "Hlookup Hcode").
  iApply (write_success_storage_keys_j x19 P with "Hlookup Hcode").
  iApply (write_success_storage_keys_k x19 P with "Hlookup Hcode").
  iApply (write_success_storage_keys_l x19 P with "Hlookup Hcode").
  iApply (write_success_storage_keys_m x19 P with "Hlookup Hcode").
  iApply (write_success_storage_keys_n x19 P with "Hlookup Hcode").
  iApply (write_success_storage_keys_o x19 P with "Hlookup Hcode").
  iApply (write_success_storage_keys_p x19 P with "Hlookup Hcode").
  iApply (write_success_storage_keys_q x19 P with "Hlookup Hcode").
  iApply (write_success_storage_keys_r x19 P with "Hlookup Hcode").
  iApply (write_success_storage_keys_s x19 P with "Hlookup Hcode").
  iApply (write_success_storage_keys_t x19 P with "Hlookup Hcode").
  iApply (write_success_storage_keys_output x19 P with
    "Hlookup Hcode Houtput").
  iApply (write_success_storage_keys_tail x19 P with
    "Hlookup Hcode Houtput Hloop").
Qed.
Lemma write_success_storage_keys_loop_pre `{!islaG Sigma} `{!threadG}
    (x19 : bv 64) (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  □ instr_pre 0x15228 (writeSuccessStorageKeysLoopSpec x19 P).
Proof.
  iStartProof. iIntros "#Hlookup #Hcode #Houtput".
  iLöb as "IH".
  iModIntro. iApply instr_pre_to_body. iNext.
  iApply (write_success_storage_keys_loop x19 P with
    "Hlookup Hcode Houtput IH").
Qed.
