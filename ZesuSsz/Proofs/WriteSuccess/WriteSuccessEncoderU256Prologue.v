From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_08 Require Import
  a15cb0 a15cb4 a15cb8 a15cbc a15cc0 a15cc4.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderU256Spec.

Import ListNotations.

#[local] Hint Extern 7
  (FindInContext (FindInstrKind ?address ?later) FICSyntactic) =>
  let reduced := eval vm_compute in address in
  first [ constr_eq address reduced; fail 1
        | change (FindInContext (FindInstrKind reduced later) FICSyntactic);
          typeclasses eauto ] : typeclass_instances.

Lemma zesu_encoder_u256_prologue `{!islaG Sigma} `{!threadG} :
  instr 0x15cb0 (Some IslaTraces.write_success_08.a15cb0.a15cb0) -∗
  instr 0x15cb4 (Some IslaTraces.write_success_08.a15cb4.a15cb4) -∗
  instr 0x15cb8 (Some IslaTraces.write_success_08.a15cb8.a15cb8) -∗
  instr 0x15cbc (Some IslaTraces.write_success_08.a15cbc.a15cbc) -∗
  instr 0x15cc0 (Some IslaTraces.write_success_08.a15cc0.a15cc0) -∗
  instr 0x15cc4 (Some IslaTraces.write_success_08.a15cc4.a15cc4) -∗
  instr_body 0x15cc8 zesuEncoderU256AtOutputCallSpec -∗
  instr_body 0x15cb0 zesuEncoderU256CallSpec.
Proof.
  iStartProof.
  iIntros "#H00 #H04 #H08 #H0c #H10 #H14 Hnext".
  liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try iFrame.
  all: try bv_solve.
  all: try lia.
  Unshelve. all: try liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try iFrame.
  all: try bv_solve.
  all: try lia.
  Unshelve.
  iExists
    (tail,
     [RVal_Bits b; RVal_Bits b0; RVal_Bits b1; RVal_Bits b2;
      RVal_Bits b3; RVal_Bits b4; RVal_Bits b5; RVal_Bits b6;
      RVal_Bits b7; RVal_Bits b8; RVal_Bits b9; RVal_Bits b18],
     ret, sp, tt)ₗ.
  liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try iFrame.
  all: try reflexivity.
  all: try bv_solve.
  all: try lia.
  all: simpl.
Qed.
