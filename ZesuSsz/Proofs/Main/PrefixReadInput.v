Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Contracts.DecodeHeap.
Require Import ZesuSsz.Contracts.DecodeMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPrologueSpec.
Require Import ZesuSsz.Proofs.Main.Resources.
Require Import ZesuSsz.Proofs.Main.DecodeEntry.
Require Import ZesuSsz.Proofs.Main.AllocatorAdapter.
Require Import ZesuSsz.Proofs.Main.PrefixResources.
Require Import ZesuSsz.Proofs.ReadInput.ReadInput.
Require Import ZesuSsz.Proofs.Main.PrefixArithmetic.
Require Import ZesuSsz.Proofs.Main.PrefixAllocator.
Require Import ZesuSsz.Proofs.Main.ReadInputFrame.
Lemma main_read_exit_allocator_entry `{!islaG Sigma} `{!threadG}
    (decodeTail successExitTail : DecodeBoundaryArgs -> spec)
    (args : DecodeBoundaryArgs) (x12 x13 : bv 64) (outcome : ReadInputOutcome) :
  islarisExit _ _ (mainReadInputFramedResources
    (mainPrefixReadFrame decodeTail args x12 x13)) (mainPrefixReadArgs args) outcome ⊢
  islarisEntry _ _ (mainAllocatorPrefixResources decodeTail successExitTail) args.
Proof.
  rewrite /mainReadInputFramedResources /read_input_resources /mainPrefixReadArgs /=.
  iIntros "(Hread&Hframe&_)".
  iDestruct "Hread" as (bufferSlot sizeSlot sizeWord savedWord)
    "(%Hbuffer&%Hsize&%Houtcome&%HsizeWord&%HsavedWord&Hsys&H1&H5&H6&H10&H11&HinputSlot&HsizeSlot&HsizeIo&Hinput&HsavedRa&_)".
  iDestruct "Hframe" as "(Hcommon&H2&H12&H13&HstateSlot&HtableSlot)".
  iEval (rewrite /mainPrefixCommonFrame /mainPrefixGlobals /=) in "Hcommon".
  iDestruct "Hcommon" as
    "(%Hreturn&%Hsaved&%Halign&%Hlow&%Hhigh&Hother&Hsaves&%Hpad&Hpadding&Hobject&Hstatus&Hscratch&Hprivate&Houtput&Hspec&Hheap&(%HinputAddr&%HstateAddr&%HvtableAddr&%Hbound&Hvtable&Hfailure&Hexit)&_)".
  have Hsp : bv_unsigned (Z_to_bv 64 (decodeStackPointer args)) = decodeStackPointer args.
  { pose proof (main_prefix_stack_offset _ 0 Hlow Hhigh ltac:(lia)). bv_solve. }
  have HbufferAddr : bv_unsigned (bufferSlot + BV 64 0) = decodeStackPointer args by bv_solve.
  have HsizeAddr : bv_unsigned (sizeSlot + BV 64 0) = decodeStackPointer args + 8 by bv_solve.
  have HsizeValue : sizeWord = Z_to_bv 64 (Z.of_nat (length (decodeInput args))).
  { apply bv_eq. rewrite HsizeWord. symmetry. apply main_prefix_input_size. exact Hbound. }
  have HsavedValue : savedWord = Z_to_bv 64 (decodeSavedReturnAddress args).
  { apply bv_eq. exact HsavedWord. }
  have HioAddr : bv_unsigned (readInputIoPointer + BV 64 0) = mapIoContextAddress defaultMap.
  { rewrite read_input_io_pointer_eq. bv_solve. }
  have HinputValue : BV 64 (mapInputBufferAddress defaultMap) = Z_to_bv 64 (decodeInputAddress args).
  { rewrite HinputAddr. bv_solve. }
  destruct (main_prefix_stack_alignment _ Halign Hlow Hhigh) as [Halign8 _].
  iEval (rewrite HbufferAddr HinputValue) in "HinputSlot".
  iEval (rewrite HsizeAddr HsizeValue) in "HsizeSlot".
  iEval (rewrite HioAddr HsizeValue) in "HsizeIo".
  iEval (rewrite HsavedValue) in "HsavedRa".
  iEval (rewrite HsizeValue) in "H6".
  rewrite /mainAllocatorPrefixResources /mainAllocatorEntry
    /mainPrefixAllocatorFrame /mainPrefixCommonFrame /mainPrefixGlobals /= Hsp.
  iSplitL "Hsys H2 H10 H11 H12 H13 HinputSlot HsizeSlot HstateSlot HtableSlot".
  - iExists bufferSlot, sizeSlot, x12, x13. iFrame.
    zesu_normalize_machine_map.
    repeat iSplit; iPureIntro; zesu_normalize_machine_map; lia.
  - iFrame. repeat iSplit; done.
Qed.
Print Assumptions main_read_exit_allocator_entry.

Definition mainReadInputPrefixResources `{!islaG Sigma} `{!threadG}
    (decodeTail successExitTail : DecodeBoundaryArgs -> spec) (x12 x13 : bv 64) :
    IslarisContractResources DecodeBoundaryArgs unit := {|
  islarisCode := islarisCode _ _ read_input_resources;
  islarisEntry := fun args => islarisEntry _ _
    (mainReadInputFramedResources (mainPrefixReadFrame decodeTail args x12 x13))
    (mainPrefixReadArgs args);
  islarisExit := fun args _ => islarisExit _ _
    (mainAllocatorPrefixResources decodeTail successExitTail) args tt
|}.
Theorem main_read_input_prefix_state_correct `{!islaG Sigma} `{!threadG}
    (decodeTail successExitTail : DecodeBoundaryArgs -> spec) (x12 x13 : bv 64) :
  islarisCode _ _ (mainAllocatorPrefixResources decodeTail successExitTail) -∗
  IslarisContractSpec 0x10140 0x14cec (fun _ _ => True%type)
    (mainReadInputPrefixResources decodeTail successExitTail x12 x13).
Proof.
  rewrite /IslarisContractSpec /mainReadInputPrefixResources /=.
  iIntros "HallocCode HreadCode" (args).
  iPoseProof (main_read_input_framed_state_correct
    (mainPrefixReadFrame decodeTail args x12 x13) with "HreadCode") as "Hread".
  iSpecialize ("Hread" $! (mainPrefixReadArgs args)).
  iEval (rewrite instr_pre'_eq /instr_pre'_def /=) in "Hread".
  rewrite instr_pre'_eq /instr_pre'_def /=.
  iIntros "[Hentry Hreturn]". iApply "Hread". iFrame "Hentry".
  iNext. iIntros "Hexit". iDestruct "Hexit" as (outcome) "[_ Hexit]".
  iPoseProof (main_read_exit_allocator_entry decodeTail successExitTail args x12 x13 outcome with "Hexit") as "HallocEntry".
  iPoseProof (main_allocator_prefix_state_correct decodeTail successExitTail with "HallocCode") as "Halloc".
  iSpecialize ("Halloc" $! args).
  iEval (rewrite instr_pre'_eq /instr_pre'_def /=) in "Halloc".
  iApply "Halloc". iFrame "HallocEntry Hreturn".
Qed.
Print Assumptions main_read_input_prefix_state_correct.
