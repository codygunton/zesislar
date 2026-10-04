Require Import ZesuSsz.Automation.All.
From iris.proofmode Require Import environments.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCallReturnFrames.
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

Definition writeSuccessFinalSavedRegisters : list string :=
  ["x9"; "x18"; "x19"; "x20"; "x21"; "x22";
   "x23"; "x24"; "x25"; "x26"; "x27"].

Definition writeSuccessFinalCallArgRegisters : list string :=
  ["x13"; "x14"; "x15"; "x16"; "x17"].

Definition writeSuccessFinalOtherRegisters : list string := ["x3"; "x4"].

Definition writeSuccessExactFinalReturnedFrame `{!islaG Sigma} `{!threadG}
    (sp pointer : bv 64) (items : list ByteListItem) (tail : spec)
    (Q : iProp Sigma) : iProp Sigma :=
  (writeSuccessReturnedCallerRegisters ∗ (bv_unsigned sp - 80) ↦ₘ? 80 ∗
   byteListItemResources (bv_unsigned pointer) items ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗ spec_trace tail ∗ Q)%I.

Definition writeSuccessExactFinalCallFrameForTrace
    `{!islaG Sigma} `{!threadG}
    (sp pointer count : bv 64) (items : list ByteListItem) (tail : spec)
  (savedReturn : bv 64) (P : iProp Sigma) (callTrace : spec) : iProp Sigma :=
  (∃ (b12 b13 b14 b15 b16 b17 : bv 64)
      (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : bv 64),
    reg_col ((fun r => (KindReg r, BitsShape 64)) <$> tmp_registers) ∗
    reg_col ((fun r => (KindReg r, BitsShape 64)) <$>
      writeSuccessFinalOtherRegisters) ∗
    reg_col ((fun r => (KindReg r, BitsShape 64)) <$>
      writeSuccessFinalSavedRegisters) ∗
    "x12" ↦ᵣ RVal_Bits b12 ∗ "x13" ↦ᵣ RVal_Bits b13 ∗
    "x14" ↦ᵣ RVal_Bits b14 ∗ "x15" ↦ᵣ RVal_Bits b15 ∗
    "x16" ↦ᵣ RVal_Bits b16 ∗ "x17" ↦ᵣ RVal_Bits b17 ∗
    (bv_unsigned sp - 80) ↦ₘ? 80 ∗
    byteListItemResources (bv_unsigned pointer) items ∗
    mmio_range (machineOutputAddress defaultMap) 16 ∗
    spec_trace callTrace ∗
    ⌜bv_unsigned count = length items⌝ ∗
    ⌜length items < 2 ^ 64⌝ ∗
    ⌜bv_extract 0 3 pointer = BV 3 0⌝ ∗
    ⌜(mapRamBase defaultMap) <= bv_unsigned pointer⌝ ∗
    ⌜bv_unsigned pointer + 16 * Z.of_nat (length items) < (machineRamEnd defaultMap)⌝ ∗
    ⌜bv_extract 0 4 sp = BV 4 0⌝ ∗
    ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 80⌝ ∗
    ⌜bv_unsigned sp < (machineRamEnd defaultMap)⌝ ∗
    (writeSuccessEpilogueSavedSlots sp savedReturn
      s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ∗
    ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
    ⌜(mapRamBase defaultMap) <= bv_unsigned sp + 1896⌝ ∗
    ⌜bv_unsigned sp + 2000 < (machineRamEnd defaultMap)⌝ ∗
    ⌜bv_extract 0 1 savedReturn = BV 1 0⌝ ∗
    ⌜bv_extract 1 1 savedReturn = BV 1 0⌝ ∗
    ⌜bv_extract 0 2 savedReturn = BV 2 0⌝ ∗
    P ∗
    instr_pre (bv_unsigned savedReturn)
      (writeSuccessEpiloguePost sp savedReturn
        s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
        (writeSuccessExactFinalReturnedFrame sp pointer items tail P)))%I.

Global Instance : LithiumUnfold (@writeSuccessExactFinalCallFrameForTrace) := I.
Definition writeSuccessExactFinalCallEntryFrame `{!islaG Sigma} `{!threadG}
    (sp pointer count : bv 64) (items : list ByteListItem) (tail : spec)
    (savedReturn : bv 64) (P : iProp Sigma) : iProp Sigma :=
  writeSuccessExactFinalCallFrameForTrace sp pointer count items tail savedReturn P
    (writeOutputEventsAny (sp - BV 64 48)%bv (BV 64 8)
      (byteListItemEvents (sp - BV 64 32)%bv items tail)).

Global Instance : LithiumUnfold (@writeSuccessExactFinalCallEntryFrame) := I.

Definition writeSuccessExactPost159d4CallEntrySpec
    `{!islaG Sigma} `{!threadG} (savedReturn : bv 64) (Q : iProp Sigma) : iProp Sigma :=
  (∃ (sp pointer count : bv 64) (items : list ByteListItem) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits (BV 64 0x159d0) ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x8" ↦ᵣ RVal_Bits pointer ∗
    "x10" ↦ᵣ RVal_Bits pointer ∗
    "x11" ↦ᵣ RVal_Bits count ∗
    writeSuccessExactFinalCallEntryFrame sp pointer count items tail savedReturn Q)%I.

Global Instance : LithiumUnfold (@writeSuccessExactPost159d4CallEntrySpec) := I.

Lemma write_success_exact_post_159d4_byte_lists_call
    `{!islaG Sigma} `{!threadG} (savedReturn : bv 64) (Q : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  byteListsCode -∗
  □ instr_pre 0x15d10 zesuEncoderIntCallSpec -∗
  □ instr_pre 0x15c6c zesuEncoderBytesCallSpec -∗
  (∀ sp pointer items tail, instr_body 0x159d8
    (writeSuccessEpilogueSpec (writeSuccessExactFinalReturnedFrame sp pointer items tail Q))) -∗
  instr_body 0x159d4 (writeSuccessExactPost159d4CallEntrySpec savedReturn Q).
Proof.
  iStartProof. iIntros "#Hlookup #Hcode HbyteLists #Hint #Hbytes Hnext".
  iPoseProof (write_success_byte_lists with "HbyteLists Hint Hbytes") as "HcalleeBody".
  iAssert (instr_pre 0x15c10 zesuEncoderByteListsCallSpec)%I with "[HcalleeBody]" as "Hcallee".
  { iApply instr_pre_to_body. iNext. iExact "HcalleeBody". }
  repeat first [progress iIntros (?) | progress iIntros "#?" | progress iIntros "?"];
  repeat iDestruct select (_ ∗ _)%I as "[? ?]".
  zesu_run_until ltac:(fun _ =>
    lazymatch goal with |- envs_entails _ (∃ _ : unit, _)%I => idtac end).
  liShow; zesu_instantiate_tuple; liFromSyntaxGoal.
  zesu_run_until ltac:(fun _ =>
    lazymatch goal with |- envs_entails _ zesuEncoderByteListsCallSpec => idtac end).
  iEval (unfold zesuEncoderByteListsCallSpec, zesu_c_call).
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
Print Assumptions write_success_exact_post_159d4_byte_lists_call.
