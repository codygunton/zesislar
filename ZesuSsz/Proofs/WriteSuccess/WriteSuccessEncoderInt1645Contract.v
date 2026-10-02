Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Sets.call.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_127 Require Import instrs.
From IslaTraces.write_success_01 Require Import instrs.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCalls.

Definition encoderInt1645Contract `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (zesu_call 32 (fun args sp RET => ∃ tail : spec,
    mmio_range (machineOutputAddress defaultMap) 16 ∗
    spec_trace (writeOutputEventsAny (sp - BV 64 32)%bv (BV 64 16) tail) ∗
    RET (fun _ => mmio_range (machineOutputAddress defaultMap) 16 ∗
      spec_trace tail ∗ True)))%I.
#[local] Instance : LithiumUnfold (@encoderInt1645Contract) := I.
#[local] Typeclasses Opaque encoderInt1645Contract.

Lemma encoder_int1645_contract_correct `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_127.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15ce4 encoderInt1645Contract.
Proof. zesu_block. Qed.

Print Assumptions encoder_int1645_contract_correct.
