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
  WriteSuccessOutputSemantic WriteSuccessExactBooleanSpec
  WriteSuccessExactBooleanClosedCall WriteSuccessExactTailBooleanTracePrefix
  WriteSuccessExactPrefixStackFacts WriteSuccessExactTailStackCallBounds.

Lemma exact_tail_absent_boolean_witness_caller
    `{!islaG Sigma} `{!threadG} {Decoded}
    `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded) (witness : writeSuccessNativeWitness Decoded)
    (P : iProp Sigma) :
  writeSuccessPostWord (writeSuccessPostTailWords (writeSuccessDecodedBytes witness)) 7 = BV 64 0 ->
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  □ instr_pre 0x15b9c zesuEncoderBooleanExactCallSpec -∗
  instr_pre 0x159a0
    (encoderBooleanClosedReturn (BV 64 0) (writeSuccessFrameSp witness)
       (BV 64 0x159a0) (writeSuccessExactTailAfterConditionalEvents witness) ∗
     writeSuccessExactPostWithdrawalsCallerFrameRest args witness ∗ P) -∗
  instr_body 0x15994
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
    (writeSuccessDecodedBytes witness)) 7 = BV 64 0 by assumption.
  iRename select (writeSuccessExactPostWithdrawalsCallerFrameRest args witness) into "Hframe".
  iDestruct (tail_boolean_zero_trace_from_frame args witness Hzero with "Hframe")
    as "[%Hprefix Hframe]".
  iAssert (⌜writeSuccessWitnessWellFormed args witness⌝)%I as %Hwf.
  { iEval (rewrite writeSuccessExactPostWithdrawalsCallerFrameRest_unfold
      /writeSuccessExactPostWithdrawalsCallerFrameRestRaw
      /writeSuccessExactPostWithdrawalsMemoryFrame) in "Hframe".
    iDestruct "Hframe" as "[_ [%Hwf _]]". done. }
  have [Hsp [Halign Hupper]] := exact_prefix_stack_facts args witness Hwf.
  have [Hlower Hend] := exact_tail_stack_call_bounds args witness Hwf.
  iRename select (instr_pre 0x159a0 _) into "Hnext".
  iAssert (instr_pre 0x159a0
    (encoderBooleanClosedReturn (BV 64 0) (writeSuccessFrameSp witness)
      (BV 64 0x159a0) (writeSuccessExactTailAfterConditionalEvents witness)))%I
    with "[-]" as "Hreturn".
  { iApply (instr_pre_wand 0x159a0 0x159a0 true true with "Hnext"); [done | done |].
    iIntros "Hpost". iFrame. }
  iRename select (instr_lookup_resources _) into "Hlookup".
  iClear "Hlookup".
  liInst (λ x, x.1ₗ = writeSuccessExactTailAfterConditionalEvents witness); unLET; liARun.
  iApply zesu_instr_pre_match_identity; [f_equal; bv_solve | done].
  Unshelve. all: prepare_sidecond.
  all: try (rewrite Hprefix; reflexivity).
  all: try assumption; try bv_solve.
  rewrite Hprefix.
  have -> : (writeSuccessEntrySp witness - (BV 64 2000 + BV 64 9))%bv =
    (writeSuccessFrameSp witness - BV 64 9)%bv by (unfold writeSuccessFrameSp; bv_solve).
  reflexivity.
Qed.
Print Assumptions exact_tail_absent_boolean_witness_caller.
