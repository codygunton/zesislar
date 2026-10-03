Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTailFieldsSourceJunction.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTailFieldsCallerJunction.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTailFieldsTraceJunction.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTailFieldsPayloadJunction.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactSuffixBytesPayloadSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactSuffixBytesPayload158e0.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeContract.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessRepresentation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactEncoderBytes.
Require Import ZesuSsz.Proofs.WriteSuccess.Interfaces.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Automation.ArrayLoadPriority.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPostTransactionDescriptors.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPostTransactionResources.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Open Scope Z_scope.

Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTailFieldsFirstResources.
Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTailFieldsFifthBlock.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderBytesContract.
Require Import ZesuSsz.Automation.Sets.call.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Generated.WriteSuccess.States.NativeBytesSuccessor_15920_15930.
Lemma actual_bytes_15920_handoff `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded) (witness : writeSuccessNativeWitness Decoded)
    (oldS1 : bv 64) :
  instr_pre 0x15930 (NativeBytesSuccessor_15920_15930 args witness oldS1 (tailFieldsCallerRest args witness)) -∗
  instr_lookup_resources lookup -∗ spec_instr_resources -∗
  □ instr_pre 0x15c6c encoderBytesContract -∗
  instr_body 0x15920
    (tailFieldsCallerReturn args witness oldS1 (BV 64 0x15920)
      (writeSuccessPostBytes15910 (writeSuccessPostData witness))
      (tailFieldsAfterFourthCallEvents witness)).
Proof.
 zesu_block.
 all: try (unfold array_region_start; replace (bv_unsigned (writeSuccessFrameSp witness) + 984 - (bv_unsigned (writeSuccessFrameSp witness) + 936)) with 48 by lia; simpl; lia).
 have Hindex : array_region_start 64 (bv_unsigned (writeSuccessFrameSp witness) + 936) (bv_unsigned (writeSuccessFrameSp witness) + 984) = 6%nat by (unfold array_region_start; replace (bv_unsigned (writeSuccessFrameSp witness) + 984 - (bv_unsigned (writeSuccessFrameSp witness) + 936)) with 48 by lia; reflexivity).
 rewrite Hindex.
 iEval (rewrite /tailFieldsDescriptorWords /=).
 zesu_run.
 all: try (unfold array_region_start; replace (bv_unsigned (writeSuccessFrameSp witness) + 992 - (bv_unsigned (writeSuccessFrameSp witness) + 936 + 8 * 7%nat)) with 0 by lia; simpl; lia).
 have Hindex2 : array_region_start 64 (bv_unsigned (writeSuccessFrameSp witness) + 936 + 8 * 7%nat) (bv_unsigned (writeSuccessFrameSp witness) + 992) = 0%nat by (unfold array_region_start; replace (bv_unsigned (writeSuccessFrameSp witness) + 992 - (bv_unsigned (writeSuccessFrameSp witness) + 936 + 8 * 7%nat)) with 0 by lia; reflexivity).
 rewrite Hindex2. iEval (simpl).
 zesu_run.
 have Hscratch : (writeSuccessEntrySp witness - (BV 64 2000 + BV 64 48))%bv = (writeSuccessFrameSp witness - BV 64 48)%bv by (unfold writeSuccessFrameSp; bv_solve).
 rewrite Hscratch.
 have Haddress : bv_unsigned (writeSuccessFrameSp witness - BV 64 48)%bv = bv_unsigned (writeSuccessFrameSp witness) - 48 by bv_solve.
 iDestruct (encoder_bytes_contract_stack (writeSuccessFrameSp witness) (BV 64 0x15920) (BV 64 0) oldS1 stack2 (writeSuccessPostBytes15910 (writeSuccessPostData witness)).2 Haddress with "[$]") as "Hscratch".
 iEval (unfold encoderBytesContract).
 zesu_run.
 iRename select (tailFieldsActivePayloads _ _) into "Hactive".
 iEval (rewrite tailFieldsActivePayloads_unfold /writeSuccessDescriptorResources) in "Hactive".
 iRename select (spec_trace _) into "Htrace".
 iEval (unfold tailFieldsAfterFourthCallEvents, tailFieldsBytesCallEvents) in "Htrace".
 rewrite Hscratch.
 repeat iDestruct select (_ ∗ _)%I as "[? ?]".
 repeat iDestruct select ⌜_⌝%I as %?.
 iExists (tailFieldsAfterFifthCallEvents witness, writeSuccessPostBytes15920Payload (writeSuccessPostData witness), tt)ₗ.
 zesu_run.
Qed.
Print Assumptions actual_bytes_15920_handoff.
