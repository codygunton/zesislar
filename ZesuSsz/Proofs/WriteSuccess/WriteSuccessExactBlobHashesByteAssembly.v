Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactBlobHashesLoads16 WriteSuccessExactBlobHashesLoadHandoff
  WriteSuccessExactBlobHashesInitialLoads WriteSuccessExactBlobHashesLoads8
  WriteSuccessExactBlobHashesPairsLoad8Resources WriteSuccessExactBlobHashesPairs8Handoff
  WriteSuccessExactBlobHashesWide WriteSuccessExactBlobHashesPrefix
  WriteSuccessExactBlobHashesPairAssembly.

Lemma blob_byte_assembly_correct `{!islaG Sigma} `{!threadG}
    row count base bytes index (old26 : bv 64) (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_66.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_67.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_68.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ take 17 IslaTraces.write_success_69.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15538 (blobWidePost row count base bytes index P) -∗
  instr_body 0x153d4 (blobLoads16Entry row base bytes index
    (blobLoad20Frame bytes index (blobUpperLoadFrame count bytes index
      (⌜(index + 32 <= length bytes)%nat⌝ ∗
       reg_col [(KindReg "x25", BitsShape 64)] ∗
       ("x26" ↦ᵣ RVal_Bits old26 ∗ P ∗ True) ∗ True)%I))).
Proof.
  iStartProof. iIntros "#H66 #H67 #H68 #H69 Hnext".
  iPoseProof (blob_pair_assembly_correct row count base bytes index P
    with "[] H68 H69 Hnext") as "Hpairs".
  { iApply (big_sepL_submseteq with "H67"). apply sublist_submseteq, sublist_drop. }
  iAssert (instr_body 0x15464 (blobLoads8Post row base bytes index
    (blobPairs16Carry count bytes index P))) with "[Hpairs]" as "Hhandoff".
  { iApply (instr_pre_wand 0x15464 0x15464 false false with "Hpairs"); [done | reflexivity |].
    iApply blob_load8_to_pairs8. }
  iApply (blob_prefix_correct row count base bytes index old26 P with "H66 [] Hhandoff").
  iApply (big_sepL_submseteq with "H67"). apply sublist_submseteq, sublist_take.
Qed.
Print Assumptions blob_byte_assembly_correct.
