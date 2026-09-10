Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_04 Require Import instrs.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBitvector.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderBooleanCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderOptionalSomeBoundaries.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderOptionalU64SomeFrame.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderOptionalU64SomePublicResume.

Lemma zesu_encoder_optional_u64_some_boolean_call
    `{!islaG Sigma} `{!threadG}
    (data value sp ret : bv 64) (tag : bv 8) (tail : spec)
    (r9 r12 r13 r14 r15 r16 r17
     r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 : bv 64) :
  ([∗ list] instruction ∈ IslaTraces.write_success_04.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_pre 0x15b9c zesuEncoderBooleanCallSpec -∗
  instr_body 0x15bec
    (encoderOptionalSomeAtPublicResume data value sp ret tag tail
      (optionalU64SomePublicFrame r9 r12 r13 r14 r15 r16 r17
        r18 r19 r20 r21 r22 r23 r24 r25 r26 r27)) -∗
  instr_body 0x15bd0
    (encoderOptionalSomeAtSomeBody data value sp ret tag tail
      (optionalU64SomePublicFrame r9 r12 r13 r14 r15 r16 r17
        r18 r19 r20 r21 r22 r23 r24 r25 r26 r27)).
Proof.
  move => * /=.
  iStartProof.
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try iFrame.
  all: try (bv_simplify_arith select (bv_extract 0 4 sp = _)).
  all: try (bv_simplify_arith select (bv_extract 0 3 sp = _)).
  all: try rewrite bv_sign_extend_idemp.
  all: try match goal with
    | H : bv_extract 0 3 ?currentData = _ |- _ =>
        bv_simplify_arith H; bv_solve
    end.
  all: try bv_solve.
  all: try lia.
  Unshelve. all: try exact inhabitant.
  all: lazymatch goal with |- ?G => fail "side condition" G end.
Qed.
