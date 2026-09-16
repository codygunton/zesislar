Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsWithCount.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsBlobEntry.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactBlobHashesNativeEntry.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactBlobHashesModel.
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

Lemma access_blob_native_correct `{!islaG Sigma} `{!threadG}
    sp base entries processed remaining bytes storedIndex x19 savedX22 data x22 x27 blobBase blobTotal blobBytes tail
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
  ([∗ list] instruction ∈ IslaTraces.write_success_65.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_66.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_67.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_68.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_69.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_70.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_71.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x151d4 (writeSuccessExactAccessListsState sp base entries processed remaining bytes storedIndex
    x19 savedX22 data x22 x27
    (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
      (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned savedX22))) (writeSuccessExactBlobHashesEvents sp 0 blobTotal blobBytes tail))
    (accessReturnRuntimeBounds sp (accessBlobSourceResources sp x19 savedX22 blobBase blobTotal blobBytes tail
      (accessBlobReturnedMemory sp savedX22 base entries bytes P) ∗ P ∗ True))).
Proof.
  iStartProof. iIntros "#H53 #H54 #H55 #H56 #H57 #H58 #H59 #H60 #H61 #H62 #H63 #H64 #Hcopy #Hencoder #Houtput #H65 #H66 #H67 #H68 #H69 #H70 #H71".
  iApply (access_exact_loop_with_count with
    "H53 H54 H55 H56 H57 H58 H59 H60 H61 H62 H63 H64 Hcopy Hencoder Houtput []").
  iModIntro.
  iPoseProof (blob_native_entry_correct sp x19 blobBase blobTotal blobBytes tail
    (accessBlobReturnedMemory sp savedX22 base entries bytes P) with "H65 H66 H67 H68 H69 H70 H71 Houtput") as "Hblob".
  iApply (instr_pre_wand 0x153d0 0x153d0 false false with "Hblob");
    [done | done |].
  iIntros "Hpost". iApply (access_return_to_blob_entry with "Hpost").
Qed.
Print Assumptions access_blob_native_correct.
