From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_04 Require Import instrs.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Experiments.WriteSuccessCallAbi.
Require Import ZesuSsz.Experiments.WriteSuccessBitvector.
Require Import ZesuSsz.Experiments.WriteSuccessTactics.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderBooleanCall.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderIntCall.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderOptionalU64Spec.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderOptionalU64SomeCore.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderOptionalU64SomeFrame.

#[local] Hint Rewrite (@bv_sign_extend_idemp 64) :
  lithium_rewrite isla_coq_rewrite.

#[local] Hint Extern 7
  (FindInContext (FindInstrKind ?address ?later) FICSyntactic) =>
  let reduced := eval vm_compute in address in
  first [ constr_eq address reduced; fail 1
        | change (FindInContext (FindInstrKind reduced later) FICSyntactic);
          typeclasses eauto ] : typeclass_instances.

Lemma zesu_encoder_optional_u64_some_call_correct
    `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_04.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15b9c zesuEncoderBooleanCallSpec -∗
  □ instr_pre 0x15d10 zesuEncoderIntCallSpec -∗
  instr_body 0x15bc8 zesuEncoderOptionalU64SomeCallSpec.
Proof.
  iStartProof. iIntros "#Hcode Hboolean Hint".
  iPoseProof (zesu_encoder_optional_u64_some_core_family with
    "Hcode Hboolean Hint") as "Hfamily".
  rewrite instr_pre'_eq. iIntros "Hspec".
  unpack_zesu_encoder_optional_u64_call_spec
    zesuEncoderOptionalU64SomeCallSpec.
  subst r10; subst r11; subst r12; subst r13; subst r14; subst r15;
    subst r16; subst r17.
  apply valu_has_bits_shape in Hr8 as (b8 & ->).
  apply valu_has_bits_shape in Hr9 as (b9 & ->).
  apply valu_has_bits_shape in Hr18 as (b18 & ->).
  apply valu_has_bits_shape in Hr19 as (b19 & ->).
  apply valu_has_bits_shape in Hr20 as (b20 & ->).
  apply valu_has_bits_shape in Hr21 as (b21 & ->).
  apply valu_has_bits_shape in Hr22 as (b22 & ->).
  apply valu_has_bits_shape in Hr23 as (b23 & ->).
  apply valu_has_bits_shape in Hr24 as (b24 & ->).
  apply valu_has_bits_shape in Hr25 as (b25 & ->).
  apply valu_has_bits_shape in Hr26 as (b26 & ->).
  apply valu_has_bits_shape in Hr27 as (b27 & ->).
  iPoseProof (optional_u64_some_public_return
    b10 value sp ret tag tail b8 b9 b12 b13 b14 b15 b16 b17
    b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 with "Hret")
    as "HgenericRet".
  iRename "HgenericRet" into "Hret".
  iSpecialize ("Hfamily" $! b10 value sp ret tag tail
    b9 b12 b13 b14 b15 b16 b17
    b18 b19 b20 b21 b22 b23 b24 b25 b26 b27).
  iRename "Hfamily" into "Hbody".
  iApply "Hbody".
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try iFrame.
  all: try (bv_simplify_arith select (bv_extract 0 4 sp = _)).
  all: try (bv_simplify_arith select (bv_extract 0 3 sp = _)).
  all: try bv_solve.
  all: try lia.
  Unshelve. all: try exact inhabitant.
  all: lazymatch goal with |- ?G => fail "side condition" G end.
Qed.
