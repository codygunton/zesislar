Require Import ZesuSsz.Automation.AllLegacy.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_04 Require Import instrs.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBitvector.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTactics.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderOptionalNoneBoundaries.

Lemma encoder_optional_none_tail `{!islaG Sigma} `{!threadG}
    (data value sp ret : bv 64) (tail : spec) (P : iProp Sigma) :
  instr 0x15c04 (Some a15c04) -∗
  instr 0x15c08 (Some a15c08) -∗
  instr 0x15c0c (Some a15c0c) -∗
  instr_pre 0x15b9c (encoderOptionalNoneAtBoolean data value sp ret tail P) -∗
  instr_body 0x15c04 (encoderOptionalNoneAtTail data value sp ret tail P).
Proof.
  move => * /=.
  iStartProof.
  repeat (liAStep; close_infeasible_bv_branches).
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try (bv_simplify_arith select (bv_extract 0 3 _ = _)).
  all: try rewrite bv_sign_extend_idemp.
  all: try bv_solve.
  all: try lia.
  all: try (change (bv_extract 0 2 ret = BV 2 0); assumption).
  Unshelve. all: try exact inhabitant.
Qed.
