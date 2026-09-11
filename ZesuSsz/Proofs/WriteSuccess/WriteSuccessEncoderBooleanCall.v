Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_08 Require Import instrs.
From IslaTraces.write_success_03 Require Import instrs.
From IslaTraces.write_success_01 Require Import instrs.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCallAbi.

#[local] Hint Rewrite (@bv_sign_extend_idemp 64) :
  lithium_rewrite isla_coq_rewrite.

#[local] Hint Extern 7
  (FindInContext (FindInstrKind ?address ?later) FICSyntactic) =>
  let reduced := eval vm_compute in address in
  first [ constr_eq address reduced; fail 1
        | change (FindInContext (FindInstrKind reduced later) FICSyntactic);
          typeclasses eauto ] : typeclass_instances.

Definition zesuEncoderBooleanCallSpec `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (zesu_call 16
    (fun _ sp RET =>
      ∃ tail : spec,
      mmio_range 0x2401a0c0 16 ∗
      spec_trace
        (writeOutputEventsAny (sp - BV 64 9)%bv (BV 64 1) tail) ∗
      RET (fun _ =>
        mmio_range 0x2401a0c0 16 ∗ spec_trace tail ∗ True)))%I.

Global Instance : LithiumUnfold (@zesuEncoderBooleanCallSpec) := I.

Lemma zesu_encoder_boolean_call_correct `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_03.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15b9c zesuEncoderBooleanCallSpec.
Proof.
  move => * /=.
  zesu_block.
  all: lazymatch goal with |- ?G => fail "side condition" G end.
Qed.

Lemma zesu_encoder_boolean_call_pre `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_03.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15b9c zesuEncoderBooleanCallSpec.
Proof.
  iStartProof. iIntros "#HbooleanCode #HoutputCode". iModIntro.
  iApply instr_pre_to_body. iNext.
  iApply zesu_encoder_boolean_call_correct; iAssumption.
Qed.
