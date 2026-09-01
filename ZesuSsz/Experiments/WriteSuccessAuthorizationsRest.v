From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index HintsAuthorizationsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Experiments.WriteSuccess.
Require Import ZesuSsz.Experiments.WriteSuccessCalls.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderCalls.
Require Import ZesuSsz.Experiments.WriteSuccessAuthorizationsSpec.
Require Import ZesuSsz.Experiments.WriteSuccessAuthorizationsFirstU256.
Require Import ZesuSsz.Experiments.WriteSuccessAuthorizationsOutput.
Require Import ZesuSsz.Experiments.WriteSuccessAuthorizationsFirstInt.
Require Import ZesuSsz.Experiments.WriteSuccessAuthorizationsSecondInt.
Require Import ZesuSsz.Experiments.WriteSuccessAuthorizationsSecondU256.
Require Import ZesuSsz.Experiments.WriteSuccessAuthorizationsThirdU256.

Import ListNotations.
Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.
#[local] Hint Extern 7
  (FindInContext (FindInstrKind ?address ?later) FICSyntactic) =>
  let reduced := eval vm_compute in address in
  first [ constr_eq address reduced; fail 1
        | change (FindInContext (FindInstrKind reduced later) FICSyntactic);
          typeclasses eauto ] : typeclass_instances.

Lemma write_success_authorizations_rest `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15cb0 zesuEncoderU256CallSpec -∗
  □ instr_pre 0x15d10 zesuEncoderIntCallSpec -∗
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  instr_body 0x15614 (writeSuccessAuthorizationsTailSpec P) -∗
  instr_body 0x155a4
    (writeSuccessAuthorizationsCopiedSpec AuthorizationsFirstU256 P).
Proof.
  iStartProof.
  iIntros "#Hlookup #Hcode #Hu256 #Hint #Houtput Hnext".
  iApply (write_success_authorizations_first_u256 P with
    "Hlookup Hcode Hu256").
  iApply (write_success_authorizations_output P with
    "Hlookup Hcode Houtput").
  iApply (write_success_authorizations_first_int P with
    "Hlookup Hcode Hint").
  iApply (write_success_authorizations_second_int P with
    "Hlookup Hcode Hint").
  iApply (write_success_authorizations_second_u256 P with
    "Hlookup Hcode Hu256").
  iApply (write_success_authorizations_third_u256 P with
    "Hlookup Hcode Hu256 Hnext").
Qed.
