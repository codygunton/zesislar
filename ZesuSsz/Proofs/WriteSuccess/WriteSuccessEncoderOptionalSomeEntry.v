Require Import ZesuSsz.Automation.AllLegacy.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_04 Require Import instrs.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBitvector.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderOptionalSomeBoundaries.

Lemma encoder_optional_some_entry `{!islaG Sigma} `{!threadG}
    (data value sp ret : bv 64) (tag : bv 8)
    (tail : spec) (P : iProp Sigma) :
  instr 0x15bc8 (Some a15bc8) -∗
  instr_body 0x15bcc
    (encoderOptionalSomeAtBranch data value sp ret tag tail P) -∗
  instr_body 0x15bc8
    (encoderOptionalSomeSpec data value sp ret tag tail P).
Proof.
  move => * /=.
  iStartProof.
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try (intros Hzero;
    apply bv_zero_extend_64_zero_8 in Hzero;
    contradiction).
  all: try (bv_simplify_arith select (bv_extract 0 3 data = _)).
  all: try bv_solve.
  all: try lia.
  all: try match goal with
           | Hneq : ?tag ≠ (BV 8 0) |- _ =>
               match goal with
               | Hzero : bv_zero_extend 64 tag = (BV 64 0) |- _ =>
                   exfalso; apply Hneq;
                   exact (bv_zero_extend_64_zero_8 tag Hzero)
               end
           end.
  Unshelve. all: try exact inhabitant.
  all: lazymatch goal with |- ?G => fail "side condition" G end.
Qed.
