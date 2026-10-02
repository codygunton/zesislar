Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Sets.call.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_127 Require Import instrs.
From IslaTraces.write_success_01 Require Import instrs.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCalls.
Require Import ZesuSsz.Export.Snapshots.

Definition encoderInt1645Contract `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (zesu_call 32 (fun args sp RET => ∃ tail : spec,
    mmio_range (machineOutputAddress defaultMap) 16 ∗
    spec_trace (writeOutputEvents (sp - BV 64 32)%bv (BV 64 16)
      (bv_to_little_endian 8 8 (bv_unsigned (args !!! 0%nat)) ++
       bv_to_little_endian 8 8 (bv_unsigned (args !!! 1%nat))) tail) ∗
    RET (fun _ => mmio_range (machineOutputAddress defaultMap) 16 ∗
      spec_trace tail ∗ True)))%I.
#[local] Instance : LithiumUnfold (@encoderInt1645Contract) := I.
#[local] Typeclasses Opaque encoderInt1645Contract.

Require Import ZesuSsz.Proofs.WriteSuccess.WriteOutputContract.
Require Import ZesuSsz.Automation.WordArrays.
Import WordMatching.
#[local] Instance : LithiumUnfold (@writeOutputContract) := I.
#[local] Typeclasses Opaque writeOutputContract.

Lemma encoder_int1645_contract_correct `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_127.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15ce4 encoderInt1645Contract.
Proof.
  iStartProof. iIntros "#Hcode #Houtput".
  iAssert ((□ instr_pre 0x10190 writeOutputContract)%I) as "#Hcallee".
  { iModIntro. iApply instr_pre_to_body. iNext.
    iApply (write_output_contract_correct with "Houtput"). }
  iEval (rewrite /IslaTraces.write_success_127.instrs.instr_map
    /IslaTraces.write_success_01.instrs.instr_map /=) in "Hcode Houtput".
  repeat iDestruct select (_ ∗ _)%I as "[? ?]".
  repeat liAStep. liShow.
  iMatchHyp ltac:(fun H P =>
    lazymatch P with
    | spec_trace (writeOutputEvents ?data ?size ?bytes ?tail) =>
        iExists (tail, bytes, tt)ₗ
    end).
  repeat liAStep. Unshelve. all: prepare_sidecond.
  all: try bv_solve.
  assert (Haddr : (sp + 18446744073709551584 + 0 = sp - 32)%bv) by bv_solve.
  rewrite Haddr. reflexivity.
Qed.

Print Assumptions encoder_int1645_contract_correct.
