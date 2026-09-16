Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsLoopNative.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsReturnLoopNative.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsReturnLoopEntry.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsReturnCount.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputSemantic.
Require Import ZesuSsz.Export.Snapshots.
Require Import isla.riscv64.riscv64.

Lemma access_exact_loop_with_count `{!islaG Sigma} `{!threadG}
    sp base entries processed remaining bytes storedIndex x19 savedX22 data x22 x27 tail
    (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_53.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_54.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_55.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_56.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_57.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_58.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_59.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_60.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_61.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_62.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_63.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_64.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_02.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_body 0x153d0 (accessReturnCountPost sp savedX22 tail
    (accessReturnLoopFrame sp base entries bytes x19 P)) -∗
  instr_body 0x151d4 (writeSuccessExactAccessListsState sp base entries processed remaining bytes storedIndex
    x19 savedX22 data x22 x27
    (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
      (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned savedX22))) tail)
    (accessReturnRuntimeBounds sp P)).
Proof.
  iStartProof. iIntros "#H53 #H54 #H55 #H56 #H57 #H58 #H59 #H60 #H61 #H62 #H63 #H64 #Hcopy #Hencoder #Houtput #Hnext".
  iApply (access_exact_loop_native_correct with
    "H53 H54 H55 H56 H57 H58 H59 H60 H61 H62 H63 Hcopy Hencoder Houtput []").
  iModIntro. iApply (access_return_loop_native_correct with "H64 Hencoder Houtput Hnext").
Qed.
Print Assumptions access_exact_loop_with_count.
