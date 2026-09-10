From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_04 Require Import instrs.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Experiments.WriteSuccessBitvector.
Require Import ZesuSsz.Experiments.WriteSuccessTactics.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderOptionalU64Spec.

Lemma zesu_encoder_optional_u64_none_entry_raw
    `{!islaG Sigma} `{!threadG} :
  instr 0x15bc8 (Some a15bc8) -∗
  instr 0x15bcc (Some a15bcc) -∗
  instr_body 0x15c04 zesuEncoderOptionalU64NoneCallSpec -∗
  instr_body 0x15bc8 zesuEncoderOptionalU64NoneCallSpec.
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
  Unshelve. all: try exact inhabitant.
  all: lazymatch goal with |- ?G => fail "side condition" G end.
Qed.
