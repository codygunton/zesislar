From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_04 Require Import instrs.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Experiments.WriteSuccessCallAbi.
Require Import ZesuSsz.Experiments.WriteSuccessBitvector.
Require Import ZesuSsz.Experiments.WriteSuccessTactics.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderBooleanCall.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderOptionalU64Spec.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderOptionalU64NoneEntry.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderOptionalU64NoneTail.

#[local] Hint Rewrite (@bv_sign_extend_idemp 64) :
  lithium_rewrite isla_coq_rewrite.

#[local] Hint Extern 7
  (FindInContext (FindInstrKind ?address ?later) FICSyntactic) =>
  let reduced := eval vm_compute in address in
  first [ constr_eq address reduced; fail 1
        | change (FindInContext (FindInstrKind reduced later) FICSyntactic);
          typeclasses eauto ] : typeclass_instances.

Lemma zesu_encoder_optional_u64_none_call_correct
    `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_04.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15b9c zesuEncoderBooleanCallSpec -∗
  instr_body 0x15bc8 zesuEncoderOptionalU64NoneCallSpec.
Proof.
  iStartProof.
  iIntros "#Hcode #Hboolean".
  iEval (simpl) in "Hcode".
  iDestruct "Hcode" as
    "(#Hc8 & #Hcc & #H08 & #H0c & #H10 & #H14 & #H18 & #H1c &
      #H20 & #H24 & #H28 & #H2c & #H30 & #H34 & #H38 & #Hc04 &
      #Hc08 & #Hc0c & _)".
  iApply (zesu_encoder_optional_u64_none_entry with "Hc8 Hcc").
  iApply (zesu_encoder_optional_u64_none_tail with
    "Hc04 Hc08 Hc0c Hboolean").
Qed.
