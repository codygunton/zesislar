Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Contracts.DecodeMachine.
Require Import ZesuSsz.Contracts.DecodeHeap.
Require Import ZesuSsz.Proofs.Main.DecodeTail.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeContract.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.
Require Import ZesuSsz.Proofs.Main.SuccessResources.
Require Import ZesuSsz.Proofs.Main.Resources.
Require Import ZesuSsz.Proofs.Main.PrefixArithmetic.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPrologueSpec.

Definition mainSuccessWitnessFrame `{!islaG Sigma} `{!threadG}
    (args : DecodeBoundaryArgs) (witness : writeSuccessNativeWitness WriteSuccessObservation)
    (a2 allocatorPointer allocatorSize : bv 64) : iProp Sigma :=
  let sp := Z_to_bv 64 (decodeStackPointer args) in
  (reg_col writeSuccessOtherRegShapes ∗
   ([∗ list] register; value ∈
     ["x8"; "x9"; "x18"; "x19"; "x20"; "x21";
      "x22"; "x23"; "x24"; "x25"; "x26"; "x27"]; decodeSavedRegisters args,
     register ↦ᵣ RVal_Bits (value : bv 64)) ∗
   "x12" ↦ᵣ RVal_Bits a2 ∗ writeSuccessScratch sp ∗
   writeSuccessProloguePayload witness ∗
   mainDecoderCallerFrame sp (Z_to_bv 64 (decodeInputAddress args))
     (Z_to_bv 64 (Z.of_nat (length (decodeInput args)))) allocatorPointer allocatorSize
     (Z_to_bv 64 (decodeSavedReturnAddress args)) (decodeFramePadding args) ∗
   mainDecoderPreservedFrame args ∗ True)%I.

Lemma main_success_witness_fixed_tail_entry `{!islaG Sigma} `{!threadG}
    (args : DecodeBoundaryArgs) (observation : WriteSuccessObservation)
    (witness : writeSuccessNativeWitness WriteSuccessObservation)
    (fixedTail : spec) (a1 a2 allocatorPointer allocatorSize : bv 64) :
  writeSuccessWitnessWellFormed (mainWriterArgs args observation) witness ->
  writeSuccessTraceTail witness = fixedTail ->
  decodeSavedRegisters args =
    [writeSuccessSavedS0 witness; writeSuccessSavedS1 witness;
     writeSuccessSavedS2 witness; writeSuccessSavedS3 witness;
     writeSuccessSavedS4 witness; writeSuccessSavedS5 witness;
     writeSuccessSavedS6 witness; writeSuccessSavedS7 witness;
     writeSuccessSavedS8 witness; writeSuccessSavedS9 witness;
     writeSuccessSavedS10 witness; writeSuccessSavedS11 witness] ->
  decodeStackPointer args `mod` 16 = 0 ->
  mapRamBase defaultMap + 0x880 <= decodeStackPointer args ->
  decodeStackPointer args + 0x7d0 < machineRamEnd defaultMap ->
  bv_unsigned (Z_to_bv 64 (decodeStackPointer args)) = decodeStackPointer args ->
  bv_unsigned (Z_to_bv 64 (decodeStackPointer args) + BV 64 32)%bv = decodeStackPointer args + 32 ->
  mainCallRegisters (Z_to_bv 64 (decodeStackPointer args)) (BV 64 0x14d10)
    (Z_to_bv 64 (decodeStackPointer args) + BV 64 32)%bv a1 ∗
  mainDispatchMemory (Z_to_bv 64 (decodeStackPointer args)) (BV 16 0) ∗
  mainSuccessWitnessFrame args witness a2 allocatorPointer allocatorSize ∗ True ⊢
  writeSuccessFixedTailEntry fixedTail (mainWriterArgs args observation) ∗
  mainSuccessCallerFrame args allocatorPointer allocatorSize ∗ True.
Proof.
  intros Hwell Htail Hsaved Halign Hlow Hhigh Hsp Hsp32.
  pose proof Hwell as Hfacts.
  destruct Hfacts as [HentrySp [HdecodedPtr [Hreturn [HreturnValue Hfacts]]]].
  cbn [mainWriterArgs successStackPointer successDecodedAddress successReturnAddress] in HentrySp, HdecodedPtr, HreturnValue.
  have HentryValue : writeSuccessEntrySp witness = Z_to_bv 64 (decodeStackPointer args).
  { apply bv_eq. rewrite Hsp. symmetry. exact HentrySp. }
  have HdecodedValue : writeSuccessDecodedPointer witness =
      (Z_to_bv 64 (decodeStackPointer args) + BV 64 32)%bv.
  { apply bv_eq. rewrite Hsp32. symmetry. exact HdecodedPtr. }
  change (writeSuccessReturnValue witness = Z_to_bv 64 0x14d10) in HreturnValue.
  have HreturnBits : writeSuccessReturnValue witness = BV 64 0x14d10.
  { rewrite HreturnValue. apply bv_eq. vm_compute. reflexivity. }
  have Hbits : bv_extract 0 4 (Z_to_bv 64 (decodeStackPointer args)) = BV 4 0.
  { apply bv_eq. rewrite bv_extract_0_unsigned Hsp. exact Halign. }
  rewrite /mainCallRegisters /mainDispatchMemory /mainSuccessWitnessFrame /= Hsp.
  iIntros "((Hsys&H1&H2&H10&H11&_)&(%Halign8&%HramLow&%HramHigh&Hstatus&_)&(Hother&Hsaved&H12&Hscratch&Hpayload&Hcaller&Hpreserved&_)&_)".
  iEval (rewrite Hsaved /=) in "Hsaved".
  iDestruct "Hsaved" as "(H8&H9&H18&H19&H20&H21&H22&H23&H24&H25&H26&H27&_)".
  rewrite /mainSuccessCallerFrame /=.
  iSplitL "Hsys H1 H2 H10 H11 Hother H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H12 Hscratch Hpayload".
  - rewrite /writeSuccessFixedTailEntry. iExists witness. iSplit; first done.
    iSplit; first done.
    rewrite /write_success_prologue_entry HentryValue HdecodedValue HreturnBits.
    iFrame. rewrite !reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists (RVal_Bits a1). iFrame.
    rewrite /writeSuccessPrologueFacts Hsp Hsp32. iFrame. repeat iSplit; done.
  - have Hsp880 : bv_unsigned (Z_to_bv 64 (decodeStackPointer args) + BV 64 880)%bv = decodeStackPointer args + 880.
    { pose proof (main_prefix_stack_offset _ 880 Hlow Hhigh ltac:(lia)). bv_solve. }
    iEval (rewrite Hsp880) in "Hstatus". iFrame.
Qed.
Print Assumptions main_success_witness_fixed_tail_entry.
