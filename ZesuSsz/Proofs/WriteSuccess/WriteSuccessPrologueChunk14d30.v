Require Import ZesuSsz.Automation.AllLegacy.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_00 Require Import instrs.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBitvector.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPrologueSpec.

#[local] Hint Rewrite bv_sign_extend_64_idemp : isla_coq_rewrite.

Lemma write_success_prologue_chunk_14d30 `{!islaG Sigma} `{!threadG}
    (sp decoded ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : bv 64)
    (P Q : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_00.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x14d48
    (writeSuccessPrologueAt14d48 sp decoded ra s0 s1 s2 s3 s4 s5 s6 s7
       s8 s9 s10 s11 (P ∗ Q)) -∗
  instr_body 0x14d30
    (write_success_prologue_entry sp decoded ra s0 s1 s2 s3 s4 s5 s6 s7
       s8 s9 s10 s11 P ∗ Q).
Proof.
  move => * /=.
  iStartProof.
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try (bv_simplify_arith H1).
  all: try bv_solve.
  all: try lia.
  Unshelve. all: try exact inhabitant.
  all: lazymatch goal with |- ?G => fail "side condition" G end.
Qed.
