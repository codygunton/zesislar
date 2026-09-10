Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_08 Require Import a15cd8 a15cdc a15ce0.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderU256Spec.

#[local] Hint Rewrite (@bv_sign_extend_idemp 64) :
  lithium_rewrite isla_coq_rewrite.

#[local] Hint Extern 7
  (FindInContext (FindInstrKind ?address ?later) FICSyntactic) =>
  let reduced := eval vm_compute in address in
  first [ constr_eq address reduced; fail 1
        | change (FindInContext (FindInstrKind reduced later) FICSyntactic);
          typeclasses eauto ] : typeclass_instances.

Lemma zesu_encoder_u256_epilogue `{!islaG Sigma} `{!threadG} :
  instr 0x15cd8 (Some IslaTraces.write_success_08.a15cd8.a15cd8) -∗
  instr 0x15cdc (Some IslaTraces.write_success_08.a15cdc.a15cdc) -∗
  instr 0x15ce0 (Some IslaTraces.write_success_08.a15ce0.a15ce0) -∗
  instr_body 0x15cd8 zesuEncoderU256AfterOutputSpec.
Proof.
  iStartProof.
  iIntros "#H28 #H2c #H30".
  liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try iFrame.
  all: try rewrite bv_sign_extend_idemp.
  all: try bv_solve.
  all: try lia.
  Unshelve. all: try liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try iFrame.
  all: try rewrite bv_sign_extend_idemp.
  all: try bv_solve.
  all: try lia.
  all: simpl.
Qed.
