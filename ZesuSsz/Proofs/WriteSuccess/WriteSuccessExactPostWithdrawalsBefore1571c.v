Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Endpoints.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessNativeContract WriteSuccessRepresentation WriteSuccessValueSpec
  WriteSuccessOutputSemantic WriteSuccessPostTransactionDescriptors.
Require Import ZesuSsz.Automation.Sets.v2.
Require Import ZesuSsz.Automation.Switches.ReturnBundle.
Require Import ZesuSsz.Automation.Switches.ArrayLoadPriority.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactPrefixStackFacts.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactPostWithdrawalsChainEnd.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactPostWithdrawalsSplit.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactPostWithdrawalsPrefixJunction.
Require Import ZesuSsz.Proofs.WriteSuccess.Interfaces.
From IslaTraces.write_success_blocks Require Import Index.

Require Import ZesuSsz.Automation.ArrayForget.
Require Import ZesuSsz.Automation.Switches.LoadedTrace.
Require Import ZesuSsz.Proofs.WriteSuccess.InterfacesCoverage.
Require Import ZesuSsz.Automation.Switches.ConjunctMatch.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactPostWithdrawalsOptionalJunction.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactPostWithdrawalsBytesFacts.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactPostWithdrawalsBytesJunction.
Lemma write_success_exact_post_withdrawals_before1571c
    `{!islaG Sigma} `{!threadG} {Decoded}
    `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded) (P : iProp Sigma)
    (Hwf : writeSuccessWitnessWellFormed args witness) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15bc8 encoderOptionalEntryBoundary -∗
  instr_body 0x1571c (writeSuccessExactPostWithdrawalsAt1571c args witness P) -∗
  instr_body 0x15718 (writeSuccessExactPostWithdrawalsAt15718 args witness P).
Proof.
have HvaluesLength : length (writeSuccessValues witness) = 74%nat by (unfold writeSuccessWitnessWellFormed in Hwf; tauto).
have HtakeLength : length (take 69 (writeSuccessValues witness)) = 69%nat by (rewrite length_take HvaluesLength; lia).
have HsourceLength : length (writeSuccessSourceBytes witness) = 720%nat by (unfold writeSuccessWitnessWellFormed in Hwf; tauto).
have HsourceBytes : IslarisMemory.bytes_of_u64s (writeSuccessValues witness) = take 592 (writeSuccessSourceBytes witness) by (unfold writeSuccessWitnessWellFormed in Hwf; tauto).
have HoptionalLength : length (bv_to_little_endian 8 8 (bv_unsigned (writeSuccessValueWord (writeSuccessValues witness) 15)) ++ bv_to_little_endian 8 8 (bv_unsigned (writeSuccessValueWord (writeSuccessValues witness) 16))) = 16%nat by (rewrite length_app !length_bv_to_little_endian; lia).
time "Before1571c_block" zesu_block.
iEval (replace (bv_unsigned (writeSuccessFrameSp witness) + 1632)%Z with
    (bv_unsigned (writeSuccessFrameSp witness) + 1624 + 8)%Z by lia) in "∗".
iPoseProof (mem_mapsto_u64_pair_to_byte_array
    (bv_unsigned (writeSuccessFrameSp witness) + 1624)
    (writeSuccessValueWord (writeSuccessValues witness) 15)
    (writeSuccessValueWord (writeSuccessValues witness) 16) with "[$] [$]") as "HoptionalBytes".
time "From15718_pair" zesu_run.
1: unfold encoderOptionalU64Valid; cbn [bv_to_little_endian]; rewrite !lookup_cons; case_decide; [done | split; [cbn [length]; lia | zesu_witness_facts; bv_solve]].
have Houtcome := write_success_post_withdrawals_optional_outcome witness HvaluesLength HsourceLength HsourceBytes H0.
iExists (pw_binding_declared witness, tt)ₗ.
time "From15718_tail" zesu_run.
1: rewrite Houtcome -write_success_post_withdrawals_optional_tail; reflexivity.
rewrite Houtcome /encoderOptionalU64ExactReturn.
destruct (writeSuccessPostOptional15700 (writeSuccessPostData witness)) as [value |] eqn:Hoptional.
all: iIntros "Hreturn".
all: iEval (unfold WriteSuccessExactOptionalU64SomeBooleanResume.optionalU64SomeExactPost,
  WriteSuccessExactOptionalU64SomeJumpHandoff.optionalU64SomeExactSourceFrame,
  WriteSuccessExactOptionalU64NoneCallSpec.optionalU64NoneExactCallPost,
  WriteSuccessExactOptionalU64NoneEntry.optionalU64NoneObjectFrame) in "∗".
all: repeat iDestruct select (_ ∗ _)%I as "[? ?]".
all: iPoseProof (byte_array_forget (bv_unsigned (writeSuccessFrameSp witness + 1624))
  (bv_to_little_endian 8 8 (bv_unsigned (writeSuccessValueWord (writeSuccessValues witness) 15)) ++
   bv_to_little_endian 8 8 (bv_unsigned (writeSuccessValueWord (writeSuccessValues witness) 16)))
  with "[$]") as "Hoptional".
all: iEval (replace (bv_unsigned (writeSuccessFrameSp witness + 1624)) with
  (bv_unsigned (writeSuccessFrameSp witness) + 1624)%Z by (zesu_witness_facts; bv_solve);
  rewrite HoptionalLength) in "Hoptional".
all: iDestruct select (_ -∗ writeSuccessExactPostWithdrawalsMemoryFrame args witness)%I as "Hrestore".
all: iPoseProof (write_success_post_withdrawals_optional_memory_restore args witness with "Hrestore [$] [$] Hoptional") as "[Hmemory Hsmall]".
all: time "Before1571c_frame" zesu_run.
Time Qed.

