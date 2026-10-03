Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.ExactResources.
Require Import ZesuSsz.Generated.WriteSuccess.States.NativeRoot_14d30.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeContract.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessRepresentation.
Require Import ZesuSsz.Contracts.Endpoints.

Lemma native_root_from_level1 `{!islaG Sigma} `{!threadG}
    {Decoded : Type} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded) :
  writeSuccessNativeEntry args ⊢
    (∃ witness, NativeRootState_14d30 args witness)%I.
Proof.
rewrite /writeSuccessNativeEntry. iIntros "Hentry".
iDestruct "Hentry" as (witness) "[%Hwell Hentry]".
iExists witness. rewrite /NativeRootState_14d30.
iEval (rewrite /WriteSuccessPrologueSpec.write_success_prologue_entry
  /writeSuccessProloguePayload /WriteSuccessPrologueSpec.writeSuccessScratch
  /WriteSuccessPrologueSpec.writeSuccessPrologueFacts /writeSuccessNativeDataResources
  /WriteSuccessToLoadWithFrame.writeSuccessLoadHeaderHeapResources) in "Hentry".
zesu_open_resource_groups.
iRename select ("x11" ↦ᵣ: _)%I into "Hunknown".
iEval (rewrite !reg_mapsto_pred_eq /reg_mapsto_pred_def) in "Hunknown".
iDestruct "Hunknown" as (rv11) "[Hx11 Hrest]".
iDestruct "Hrest" as (rv12) "[Hx12 Hrest]".
iDestruct "Hrest" as "[Hscratch Hrest]".
iDestruct "Hscratch" as (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12) "Hscratch".
iExists rv11, rv12, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12.
iRename select (reg_col WriteSuccessPrologueSpec.writeSuccessOtherRegShapes) into "Hother".
iEval (rewrite /WriteSuccessPrologueSpec.writeSuccessOtherRegShapes /reg_col /=) in "Hother".
repeat (iDestruct "Hother" as "[Hex Hother]";
  let value := fresh "other" in iDestruct "Hex" as (value) "[? ?]"; iExists value).
unfold writeSuccessWitnessWellFormed in Hwell.
repeat match goal with Hfact : _ /\ _ |- _ => destruct Hfact end.
zesu_open_resource_groups.
iRename select (reg_col zesu_ram_sys_regs) into "Hsys". iFrame "Hsys".
zesu_frame_exact_resources.
Qed.

Print Assumptions native_root_from_level1.
