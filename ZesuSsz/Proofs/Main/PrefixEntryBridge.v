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
Require Import ZesuSsz.Proofs.Main.ReadInputFrame.
Lemma main_prologue_exit_read_entry `{!islaG Sigma} `{!threadG}
    (decodeTail : DecodeBoundaryArgs -> spec) (args : DecodeBoundaryArgs)
    (oldInput x5 x6 x12 x13 : bv 64) :
  mainReadInputCall (mainPrefixInitialSp args)
    (Z_to_bv 64 (decodeSavedReturnAddress args)) ∗
  mainPrefixFrame decodeTail args oldInput x5 x6 x12 x13 ∗ True ⊢
  islarisEntry _ _ (mainReadInputFramedResources
    (mainPrefixReadFrame decodeTail args x12 x13)) (mainPrefixReadArgs args).
Proof.
  have Hframe : mainFrameSp (mainPrefixInitialSp args) = Z_to_bv 64 (decodeStackPointer args).
  { rewrite /mainFrameSp /mainPrefixInitialSp. bv_solve. }
  rewrite /mainReadInputCall Hframe.
  iIntros "((%HinitialAlign&%HinitialLow&%HinitialHigh&Hsys&H1&H2&H10&H11&HsavedRa&HsizeSlot&_)&Hframe&_)".
  iDestruct "Hframe" as "(Hcommon&H5&H6&H12&H13&HinputSlot&HstateSlot&HtableSlot&Hinput&HsizeIo)".
  iEval (rewrite /mainPrefixCommonFrame /mainPrefixGlobals /=) in "Hcommon".
  iDestruct "Hcommon" as
    "(%Hreturn&%Hsaved&%Halign&%Hlow&%Hhigh&Hother&Hsaves&%Hpad&Hpadding&Hobject&Hstatus&Hscratch&Hprivate&Houtput&Hspec&Hheap&(%HinputAddr&%HstateAddr&%HvtableAddr&%Hbound&Hvtable&Hfailure&Hexit)&_)".
  have Hsp := main_prefix_stack_offset _ 0 Hlow Hhigh ltac:(lia).
  have Hsp8 := main_prefix_stack_offset _ 8 Hlow Hhigh ltac:(lia).
  have Hsp888 := main_prefix_stack_offset _ 888 Hlow Hhigh ltac:(lia).
  have Hsp0 : bv_unsigned (Z_to_bv 64 (decodeStackPointer args)) = decodeStackPointer args by bv_solve.
  have HsizeValue := main_prefix_input_size (decodeInput args) Hbound.
  destruct (main_prefix_stack_alignment _ Halign Hlow Hhigh) as [Halign8 [Hbits Hbits8]].
  have HioAddr : bv_unsigned (readInputIoPointer + BV 64 0) = mapIoContextAddress defaultMap.
  { rewrite read_input_io_pointer_eq. bv_solve. }
  have HsizeAddr : bv_unsigned (Z_to_bv 64 (decodeStackPointer args) + BV 64 8 + BV 64 0) = decodeStackPointer args + 8 by bv_solve.
  iEval (rewrite Hsp888) in "HsavedRa".
  iEval (rewrite Hsp8) in "HsizeSlot".
  rewrite /mainReadInputFramedResources /read_input_resources /mainPrefixReadArgs /=.
  iSplitL "Hsys H1 H5 H6 H10 H11 HsavedRa HsizeSlot HinputSlot HsizeIo Hinput".
  - iExists (Z_to_bv 64 (decodeStackPointer args)),
      (Z_to_bv 64 (decodeStackPointer args) + BV 64 8)%bv,
      (Z_to_bv 64 (Z.of_nat (length (decodeInput args)))), x5, x6,
      oldInput, (BV 64 0), (Z_to_bv 64 (decodeSavedReturnAddress args)).
    rewrite Hsp HsizeAddr HioAddr Z.add_0_r Hsp8 Hsp0. iFrame.
    zesu_normalize_machine_map.
    repeat iSplit; iPureIntro; try done;
      zesu_normalize_machine_map; lia.
  - rewrite /mainPrefixReadFrame /mainPrefixCommonFrame /mainPrefixGlobals /=.
    iFrame. repeat iSplit; done.
Qed.
Print Assumptions main_prologue_exit_read_entry.
