Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuMachineMap.Machine.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  Interfaces WriteSuccessNativeContract WriteSuccessRepresentation
  WriteSuccessPostTransactionResources
  WriteSuccessOutputSemantic WriteSuccessObservation WriteSuccessExactBooleanSpec
  WriteSuccessExactBooleanClosedCall WriteSuccessExactTailBooleanTracePrefix
  WriteSuccessExactPrefixStackFacts WriteSuccessExactTailStackCallBounds.

Lemma exact_tail_present_boolean_witness_caller
    `{!islaG Sigma} `{!threadG} {Decoded}
    `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded) (witness : writeSuccessNativeWitness Decoded)
    (P : iProp Sigma) :
  writeSuccessPostWord (writeSuccessPostTailWords (writeSuccessDecodedBytes witness)) 7 <> BV 64 0 ->
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  □ instr_pre 0x15b9c zesuEncoderBooleanExactCallSpec -∗
  (∀ payload : list (bv 8), instr_pre 0x15980
    (encoderBooleanClosedReturn (BV 64 1) (writeSuccessFrameSp witness)
       (BV 64 0x15980) (writeOutputEvents (writeSuccessFrameSp witness - BV 64 48)%bv (BV 64 8)
        (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned
          (writeSuccessPostWord (writeSuccessPostTailWords (writeSuccessDecodedBytes witness)) 8))))
        (writeOutputEvents
          (writeSuccessPostWord (writeSuccessPostTailWords (writeSuccessDecodedBytes witness)) 7)
          (writeSuccessPostWord (writeSuccessPostTailWords (writeSuccessDecodedBytes witness)) 8)
          payload (writeSuccessExactTailAfterConditionalEvents witness))) ∗
     writeSuccessExactPostWithdrawalsCallerFrameRest args witness ∗ P)) -∗
  instr_body 0x15974
    (reg_col zesu_ram_sys_regs ∗
     "x1" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
     "x2" ↦ᵣ RVal_Bits (writeSuccessFrameSp witness) ∗
     "x5" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
     "x10" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
     "x11" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
     (bv_unsigned (writeSuccessFrameSp witness) - 16) ↦ₘ? 16 ∗
     mmio_range (machineOutputAddress defaultMap) 16 ∗
     spec_trace (writeSuccessExactTailFirstBranchEvents witness) ∗
     writeSuccessExactPostWithdrawalsCallerFrameRest args witness ∗ P ∗ True).
Proof.
  zesu_block.
  have Hzero : writeSuccessPostWord (writeSuccessPostTailWords
    (writeSuccessDecodedBytes witness)) 7 <> BV 64 0 by assumption.
  iRename select (writeSuccessExactPostWithdrawalsCallerFrameRest args witness) into "Hframe".
  iDestruct (tail_boolean_one_trace_from_frame args witness Hzero with "Hframe")
    as "[%Hprefix Hframe]".
  destruct Hprefix as (payload & Hprefix).
  iAssert (⌜writeSuccessWitnessWellFormed args witness⌝)%I as %Hwf.
  { iEval (rewrite writeSuccessExactPostWithdrawalsCallerFrameRest_unfold
      /writeSuccessExactPostWithdrawalsCallerFrameRestRaw
      /writeSuccessExactPostWithdrawalsMemoryFrame) in "Hframe".
    iDestruct "Hframe" as "[_ [%Hwf _]]". done. }
  have [Hsp [Halign Hupper]] := exact_prefix_stack_facts args witness Hwf.
  have [Hlower Hend] := exact_tail_stack_call_bounds args witness Hwf.
  iRename select (∀ payload : list (bv 8), instr_pre 0x15980 _)%I into "Hnext".
  iSpecialize ("Hnext" $! payload).
  match type of Hprefix with _ = writeOutputEvents _ _ _ ?tail =>
    pose (callTail := tail) end.
  have HscratchAddress : (writeSuccessEntrySp witness - (BV 64 2000 + BV 64 48))%bv =
    (writeSuccessFrameSp witness - BV 64 48)%bv by (unfold writeSuccessFrameSp; bv_solve).
  iAssert (instr_pre 0x15980
    (encoderBooleanClosedReturn (BV 64 1) (writeSuccessFrameSp witness)
      (BV 64 0x15980) callTail))%I
    with "[-]" as "Hreturn".
  { iApply (instr_pre_wand 0x15980 0x15980 true true with "Hnext"); [done | done |].
    iIntros "Hpost". subst callTail. iFrame.
    rewrite HscratchAddress. iExact "Hpost". }
  iRename select (instr_lookup_resources _) into "Hlookup".
  iClear "Hlookup".
  liInst (λ x, x.1ₗ = callTail); unLET; liARun.
  rewrite HscratchAddress.
  iApply zesu_instr_pre_match_identity; [f_equal; bv_solve | done].
  Unshelve. all: prepare_sidecond.
  all: try (rewrite Hprefix; reflexivity).
  all: try assumption; try bv_solve.
  rewrite Hprefix.
  have -> : (writeSuccessEntrySp witness - (BV 64 2000 + BV 64 9))%bv =
    (writeSuccessFrameSp witness - BV 64 9)%bv by (unfold writeSuccessFrameSp; bv_solve).
  rewrite HscratchAddress. reflexivity.
Qed.
Print Assumptions exact_tail_present_boolean_witness_caller.
