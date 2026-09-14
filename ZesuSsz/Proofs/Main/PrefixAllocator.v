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

Lemma main_prefix_other_registers_correct `{!islaG Sigma} `{!threadG} (x5 x6 : bv 64) :
  mainPrefixOtherRegisters ∗ "x5" ↦ᵣ RVal_Bits x5 ∗ "x6" ↦ᵣ RVal_Bits x6 ⊢
  reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
    List.filter (fun register => negb (String.eqb register "x13")) writeSuccessOtherRegisters).
Proof.
  rewrite /mainPrefixOtherRegisters /writeSuccessOtherRegisters /= !reg_col_cons /=.
  iIntros "[((H3&H4&_)&Hrest) (H5&H6)]".
  iSplitL "H3"; first iExact "H3".
  iSplitL "H4"; first iExact "H4".
  iSplitL "H5"; first (iExists (RVal_Bits x5); iFrame; done).
  iSplitL "H6"; first (iExists (RVal_Bits x6); iFrame; done).
  iExact "Hrest".
Qed.
Print Assumptions main_prefix_other_registers_correct.

Require Import ZesuSsz.Proofs.Main.PrefixArithmetic.
Lemma main_allocator_exit_decode_entry `{!islaG Sigma} `{!threadG}
    (decodeTail successExitTail : DecodeBoundaryArgs -> spec) (args : DecodeBoundaryArgs) :
  mainAllocatorExit (Z_to_bv 64 (decodeStackPointer args))
      (Z_to_bv 64 (decodeInputAddress args))
      (Z_to_bv 64 (Z.of_nat (length (decodeInput args)))) ∗
    mainPrefixAllocatorFrame decodeTail args ∗ True ⊢
  islarisExit _ _ (mainAllocatorPrefixResources decodeTail successExitTail) args tt.
Proof.
  iIntros "(Halloc&Hframe&_)".
  iDestruct "Hframe" as "(Hcommon&H1&H5&H6&HsavedRa&Hinput&HsizeWord)".
  iEval (rewrite /mainPrefixCommonFrame /mainPrefixGlobals /=) in "Hcommon".
  iDestruct "Hcommon" as
    "(%Hreturn&%Hsaved&%Halign&%Hlow&%Hhigh&Hother&Hsaves&%Hpad&Hpadding&Hobject&Hstatus&Hscratch&Hprivate&Houtput&Hspec&Hheap&(%HinputAddr&%HstateAddr&%HvtableAddr&%Hbound&Hvtable&Hfailure&Hexit)&_)".
  have Hsp : bv_unsigned (Z_to_bv 64 (decodeStackPointer args)) = decodeStackPointer args.
  { pose proof (main_prefix_stack_offset _ 0 Hlow Hhigh ltac:(lia)). bv_solve. }
  have HstatePtr : Z_to_bv 64 mainAllocatorStateAddress = BV 64 (mapIoContextAddress defaultMap - 8) by (rewrite /mainAllocatorStateAddress; bv_solve).
  have HvtablePtr : Z_to_bv 64 mainAllocatorVtableAddress = BV 64 0x177a8 by (rewrite /mainAllocatorVtableAddress /mapRodataBase /defaultMap /=; bv_solve).
  iEval (rewrite /mainAllocatorExit /= Hsp) in "Halloc".
  iDestruct "Halloc" as
    "(Hsys&H2&H10&H11&H12&H13&HinputSlot&HsizeSlot&HstateSlot&HtableSlot&_)".
  iPoseProof (main_prefix_other_registers_correct with "[$Hother $H5 $H6]") as "Hother".
  rewrite /mainAllocatorPrefixResources /mainBeforeDecodeCallResources
    /mainBeforeDecodeCallFrame /mainCallRegisters /mainDecoderCallerFrame
    /mainDecoderPreservedFrame /= HinputAddr HstateAddr HvtableAddr
    HstatePtr HvtablePtr /mainAllocatorStateAddress /mainAllocatorVtableAddress /= Hsp.
  iFrame. repeat iSplit; done.
Qed.
Print Assumptions main_allocator_exit_decode_entry.

Require Import ZesuSsz.Proofs.Main.AllocatorGuarded.
Theorem main_allocator_prefix_state_correct `{!islaG Sigma} `{!threadG}
    (decodeTail successExitTail : DecodeBoundaryArgs -> spec) :
  ⊢ IslarisContractSpec 0x14ccc 0x14cec (fun _ _ => True%type)
    (mainAllocatorPrefixResources decodeTail successExitTail).
Proof.
  rewrite /IslarisContractSpec /mainAllocatorPrefixResources /=.
  iIntros "Hcode" (args).
  iPoseProof (main_allocator_guarded_state_correct
    (Z_to_bv 64 (decodeStackPointer args)) (Z_to_bv 64 (decodeInputAddress args))
    (Z_to_bv 64 (Z.of_nat (length (decodeInput args))))
    (mainPrefixAllocatorFrame decodeTail args) with "Hcode") as "Halloc".
  iSpecialize ("Halloc" $! tt).
  iApply (instr_pre_wand 0x14ccc 0x14ccc false false with "Halloc"); [done | reflexivity |].
  iIntros "[Hentry Hreturn]". iFrame "Hentry".
  iApply (instr_pre_wand 0x14cec 0x14cec true true with "Hreturn"); [done | reflexivity |].
  iIntros "Hexit". iDestruct "Hexit" as (outcome) "[_ Hexit]".
  iExists tt. iSplit; first done.
  iApply (main_allocator_exit_decode_entry decodeTail successExitTail args with "Hexit").
Qed.
Print Assumptions main_allocator_prefix_state_correct.
