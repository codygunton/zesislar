Require Import ZesuSsz.Automation.All.
From iris.proofmode Require Import environments.
Require Import ZesuSsz.Automation.CallReturnFrames.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith Lia.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
From IslaTraces.write_success_125 Require Import a159d4_spec.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessByteLists.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCallAbi.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEpilogueBlock.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeContract.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderIntCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderBytesCall.

Import ListNotations.

From ZesuSsz.Proofs.WriteSuccess Require Import WriteSuccessExactFinalByteListCall
  WriteSuccessExactByteLists WriteSuccessExactByteListsSpec WriteSuccessRepresentation
  WriteSuccessExactEncoderIntCall WriteSuccessExactEncoderBytes WriteSuccessObservation
  WriteSuccessOutputSemantic.
Require Import ZesuSsz.Export.Snapshots.
Definition writeSuccessExactFinalPayloadCallEntryFrame `{!islaG Sigma} `{!threadG}
    (sp pointer count : bv 64) (items : list ByteListItem) (tail : spec)
    (savedReturn : bv 64) (P : iProp Sigma) : iProp Sigma :=
  writeSuccessExactFinalCallFrameForTrace sp pointer count items tail savedReturn P
    (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
      (writeSuccessPrivateBytes (writeSuccessEncodeU64 (Z.of_nat (length items))))
      (byteListItemPayloadEvents (sp - BV 64 32)%bv items tail)).
Global Instance : LithiumUnfold (@writeSuccessExactFinalPayloadCallEntryFrame) := I.

Definition writeSuccessExactPost159d4PayloadCallEntrySpec
    `{!islaG Sigma} `{!threadG} (savedReturn : bv 64) (Q : iProp Sigma) : iProp Sigma :=
  (∃ (sp pointer count : bv 64) (items : list ByteListItem) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits (BV 64 0x159d0) ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x8" ↦ᵣ RVal_Bits pointer ∗
    "x10" ↦ᵣ RVal_Bits pointer ∗
    "x11" ↦ᵣ RVal_Bits count ∗
    writeSuccessExactFinalPayloadCallEntryFrame sp pointer count items tail savedReturn Q)%I.

Global Instance : LithiumUnfold (@writeSuccessExactPost159d4PayloadCallEntrySpec) := I.

Lemma write_success_exact_post_159d4_payload_byte_lists_call
    `{!islaG Sigma} `{!threadG} (savedReturn : bv 64) (Q : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  byteListsCode -∗
  □ instr_pre 0x15d10 zesuEncoderIntPayloadCallSpec -∗
  □ instr_pre 0x15c6c encoderBytesExactCallSpec -∗
  (∀ sp pointer items tail, instr_body 0x159d8
    (writeSuccessEpilogueSpec (writeSuccessExactFinalReturnedFrame sp pointer items tail Q))) -∗
  instr_body 0x159d4 (writeSuccessExactPost159d4PayloadCallEntrySpec savedReturn Q).
Proof.
  iStartProof. iIntros "#Hlookup #Hcode HbyteLists #Hint #Hbytes Hnext".
  iPoseProof (byte_lists_exact_correct with "HbyteLists Hint Hbytes") as "HcalleeBody".
  iAssert (instr_pre 0x15c10 encoderByteListsExactCallSpec)%I with "[HcalleeBody]" as "Hcallee".
  { iApply instr_pre_to_body. iNext. iExact "HcalleeBody". }
  repeat first [progress iIntros (?) | progress iIntros "#?" | progress iIntros "?"];
  repeat iDestruct select (_ ∗ _)%I as "[? ?]".
  zesu_run_until ltac:(fun _ =>
    lazymatch goal with |- envs_entails _ (∃ _ : unit, _)%I => idtac end).
  liShow; zesu_instantiate_tuple; liFromSyntaxGoal.
  zesu_run_until ltac:(fun _ =>
    lazymatch goal with |- envs_entails _ encoderByteListsExactCallSpec => idtac end).
  iEval (unfold encoderByteListsExactCallSpec, zesu_c_call).
  zesu_run_until ltac:(fun _ =>
    lazymatch goal with |- envs_entails _ (@bi_exist _ (list ByteListItem) _) => idtac end).
  iExists items, tail.
  zesu_run_until ltac:(fun _ =>
    lazymatch goal with |- envs_entails _ (instr_pre _ _) => idtac end).
  iSpecialize ("Hnext" $! sp pointer items tail).
  iApply (instr_pre_wand 0x159d8 (bv_unsigned LET) false true with "Hnext");
    [done | subst LET; bv_solve |].
  iIntros "Hpost".
  iRename select (reg_col [(KindReg "x3", BitsShape 64); (KindReg "x4", BitsShape 64)]) into "Hother".
  iRename select Q into "HQ".
  iRename select (instr_pre (bv_unsigned savedReturn) _) into "Hreturn".
  iAssert (writeSuccessEpilogueSavedSlots sp savedReturn s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)%I
    with "[-Hother HQ Hreturn Hpost]" as "Hslots".
  { rewrite /writeSuccessEpilogueSavedSlots. iFrame. }
  iApply (zesu_call_ret_to_epilogue with "Hother Hpost Hslots HQ Hreturn"); try assumption.
  rewrite /writeSuccessExactFinalReturnedFrame !bi.sep_assoc bi.sep_True. done.
  Unshelve. all: unfold SHELVED_SIDECOND; bv_simplify_arith H5; try subst LET; try subst LET0; try subst LET1; try bv_solve.
  f_equal. apply bool_decide_eq_true_2. bv_solve.
Qed.
Print Assumptions write_success_exact_post_159d4_payload_byte_lists_call.
