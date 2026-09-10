From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_04 Require Import instrs.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Experiments.WriteSuccessBitvector.
Require Import ZesuSsz.Experiments.WriteSuccessTactics.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderOptionalSomeBoundaries.

Lemma encoder_optional_some_branch `{!islaG Sigma} `{!threadG}
    (data value sp ret : bv 64) (tag : bv 8)
    (tail : spec) (P : iProp Sigma) :
  instr 0x15bcc (Some a15bcc) -∗
  instr_body 0x15bd0
    (encoderOptionalSomeAtSomeBody data value sp ret tag tail P) -∗
  instr_body 0x15bcc
    (encoderOptionalSomeAtBranch data value sp ret tag tail P).
Proof.
  move => * /=.
  iStartProof.
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try (intros Hzero; contradiction).
  all: try bv_solve.
  all: try lia.
  Unshelve. all: try exact inhabitant.
  all: iExFalso; iPureIntro; contradiction.
  all: lazymatch goal with |- ?G => fail "side condition" G end.
Qed.
