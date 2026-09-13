Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Resources.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactBlobHashesLoads16 WriteSuccessExactBlobHashesSaveLoads12
  WriteSuccessExactBlobHashesLoadHandoff WriteSuccessExactBlobHashesUpperLoadHandoff
  WriteSuccessExactBlobHashesLowerLoadHandoff WriteSuccessExactBlobHashesInitialLoads
  WriteSuccessExactBlobHashesPairsLoad16 WriteSuccessExactBlobHashesPairHandoff
  WriteSuccessExactBlobHashesLoads8 WriteSuccessExactBlobHashesPairsLoad8Resources
  WriteSuccessExactBlobHashesPairsLoad8.

Lemma blob_prefix_correct `{!islaG Sigma} `{!threadG}
    row count base bytes index (old26 : bv 64) (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_66.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ take 12 IslaTraces.write_success_67.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15464 (blobLoads8Post row base bytes index
    (blobPairs16Carry count bytes index P)) -∗
  instr_body 0x153d4 (blobLoads16Entry row base bytes index
    (blobLoad20Frame bytes index (blobUpperLoadFrame count bytes index
      (⌜(index + 32 <= length bytes)%nat⌝ ∗
       reg_col [(KindReg "x25", BitsShape 64)] ∗
       ("x26" ↦ᵣ RVal_Bits old26 ∗ P ∗ True) ∗ True)%I))).
Proof.
  iStartProof. iIntros "#H66 #H67 Hnext".
  iPoseProof (blob_pairs16_load8_correct row count base bytes index old26 P
    with "H67 Hnext") as "Hmiddle".
  iApply (blob_initial_loads_correct row count base bytes index
    (⌜(index + 32 <= length bytes)%nat⌝ ∗
     reg_col [(KindReg "x25", BitsShape 64)] ∗
     ("x26" ↦ᵣ RVal_Bits old26 ∗ P ∗ True) ∗ True)%I
    with "[] [] [] [] [] []").
  1-6: iApply (big_sepL_submseteq with "H66");
    first [apply sublist_submseteq, sublist_take |
      etransitivity; apply sublist_submseteq; [apply sublist_take | apply sublist_drop]].
  iApply (instr_pre_wand 0x15434 0x15434 false false with "Hmiddle"); [done | reflexivity |].
  iIntros "Hinitial".
  iPoseProof (blob_initial_loads_to_pairs16 row count base bytes index
    ("x26" ↦ᵣ RVal_Bits old26 ∗ P ∗ True)%I with "Hinitial") as "Hpost".
  iEval (unfold blobPairs16Entry, blobByte15EntryFrame, blobPairs16RemainingFrame,
    blobLoaded28Frame, blobLoaded24Frame, blobLoaded4Frame) in "Hpost".
  iEval (unfold blobPairs16Entry, blobByte15EntryFrame, blobPairs16RemainingFrame,
    blobLoaded28Frame, blobLoaded24Frame, blobLoaded4Frame).
  zesu_open_resource_groups. iFrame. iPureIntro. naive_solver.
Qed.
Print Assumptions blob_prefix_correct.
