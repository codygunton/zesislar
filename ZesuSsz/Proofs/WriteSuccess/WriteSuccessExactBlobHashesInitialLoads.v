Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsFlagLoads.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactBlobHashesLoads16 WriteSuccessExactBlobHashesLoads20
  WriteSuccessExactBlobHashesLoads28 WriteSuccessExactBlobHashesLoads24
  WriteSuccessExactBlobHashesLoads4 WriteSuccessExactBlobHashesSaveLoads12.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactBlobHashesLoadHandoff.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactBlobHashesUpperLoadHandoff.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactBlobHashesLowerLoadHandoff.
From IslaTraces.write_success_66 Require Import instrs.

Definition blobLoaded20Frame `{!islaG Sigma} `{!threadG}
    (bytes : list (bv 8)) (index : nat) (P : iProp Sigma) : iProp Sigma :=
  ("x9" ↦ᵣ RVal_Bits (transactionRowByte bytes index 20) ∗
   "x18" ↦ᵣ RVal_Bits (transactionRowByte bytes index 21) ∗
   "x20" ↦ᵣ RVal_Bits (transactionRowByte bytes index 22) ∗
   "x21" ↦ᵣ RVal_Bits (transactionRowByte bytes index 23) ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@blobLoaded20Frame) := I.

Definition blobLoaded24Frame `{!islaG Sigma} `{!threadG}
    (bytes : list (bv 8)) (index : nat) (P : iProp Sigma) : iProp Sigma :=
  ("x11" ↦ᵣ RVal_Bits (transactionRowByte bytes index 24) ∗
   "x5" ↦ᵣ RVal_Bits (transactionRowByte bytes index 25) ∗
   "x17" ↦ᵣ RVal_Bits (transactionRowByte bytes index 26) ∗
   "x16" ↦ᵣ RVal_Bits (transactionRowByte bytes index 27) ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@blobLoaded24Frame) := I.

Definition blobLowerLoadFrame `{!islaG Sigma} `{!threadG}
    (count : bv 64) (bytes : list (bv 8)) (index : nat) (P : iProp Sigma) : iProp Sigma :=
  (reg_col [(KindReg "x15", BitsShape 64); (KindReg "x31", BitsShape 64);
    (KindReg "x30", BitsShape 64); (KindReg "x29", BitsShape 64)] ∗
   blobLoad12Frame count bytes index P ∗ True)%I.
Global Instance : LithiumUnfold (@blobLowerLoadFrame) := I.

Definition blobUpperLoadFrame `{!islaG Sigma} `{!threadG}
    (count : bv 64) (bytes : list (bv 8)) (index : nat) (P : iProp Sigma) : iProp Sigma :=
  (reg_col [(KindReg "x10", BitsShape 64); (KindReg "x14", BitsShape 64);
    (KindReg "x13", BitsShape 64); (KindReg "x12", BitsShape 64)] ∗
   ⌜(index + 32 <= length bytes)%nat⌝ ∗
   blobLoad24Frame bytes index (blobLowerLoadFrame count bytes index P) ∗ True)%I.
Global Instance : LithiumUnfold (@blobUpperLoadFrame) := I.

Lemma blob_load20_to_load28 `{!islaG Sigma} `{!threadG}
    row count base bytes index (P : iProp Sigma) :
  blobLoads20Post row base bytes index (blobLoaded16Frame bytes index
    (blobUpperLoadFrame count bytes index P)) -∗
  blobLoads28Entry row base bytes index (blobLoad24Frame bytes index
    (blobLoaded20Frame bytes index (blobLoaded16Frame bytes index
      (blobLowerLoadFrame count bytes index P)))).
Proof.
  iIntros "Hfirst".
  iEval (unfold blobLoads20Post, blobLoaded16Frame,
    blobUpperLoadFrame, blobLoad24Frame) in "Hfirst".
  iDestruct "Hfirst" as
    "(Hsys & H8 & H26 & H9 & H25 & Hrow & Harray & %Hcursor & %Hbound24 & %Hlow & %Hhigh & (H6 & H7 & H28 & H1 & (Hregs & %Hbound32 & (Hregs24 & %Hbound28 & Hlower & _) & _) & _) & _)".
  iEval (unfold blobLoads28Entry, blobLoad24Frame,
    blobLoaded20Frame, blobLoaded16Frame).
  iFrame. done.
Qed.
Print Assumptions blob_load20_to_load28.

Lemma blob_load24_to_load4 `{!islaG Sigma} `{!threadG}
    row count base bytes index (P : iProp Sigma) :
  blobLoads24Post row base bytes index (blobLoaded28Frame bytes index
    (blobLoaded20Frame bytes index (blobLoaded16Frame bytes index
      (blobLowerLoadFrame count bytes index P)))) -∗
  blobLoads4Entry row base bytes index (blobLoad12Frame count bytes index
    (blobLoaded24Frame bytes index (blobLoaded28Frame bytes index
      (blobLoaded20Frame bytes index (blobLoaded16Frame bytes index P))))).
Proof.
  iIntros "Hfirst".
  iEval (unfold blobLoads24Post, blobLoaded28Frame,
    blobLoaded20Frame, blobLoaded16Frame, blobLowerLoadFrame) in "Hfirst".
  iDestruct "Hfirst" as
    "(Hsys & H11 & H5 & H17 & H16 & Hrow & Harray & %Hcursor & %Hbound28 & %Hlow & %Hhigh & (H10 & H14 & H13 & H12 & (H8 & H26 & H9 & H25 & (H6 & H7 & H28 & H1 & (Hregs & Hlower & _) & _) & _) & _) & _)".
  iEval (unfold blobLoads4Entry, blobLoad12Frame,
    blobLoaded24Frame, blobLoaded28Frame,
    blobLoaded20Frame, blobLoaded16Frame).
  iEval (unfold blobLoad12Frame) in "Hlower".
  iDestruct "Hlower" as "(Hregs12 & Hcount & %Hbound15 & HP & _)".
  iFrame. iPureIntro. lia.
Qed.
Print Assumptions blob_load24_to_load4.

Lemma blob_initial_loads_correct `{!islaG Sigma} `{!threadG}
    row count base bytes index (P : iProp Sigma) :
  ([∗ list] instruction ∈ take 4 IslaTraces.write_success_66.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ take 4 (drop 4 IslaTraces.write_success_66.instrs.instr_map),
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ take 4 (drop 8 IslaTraces.write_success_66.instrs.instr_map),
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ take 4 (drop 12 IslaTraces.write_success_66.instrs.instr_map),
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ take 4 (drop 16 IslaTraces.write_success_66.instrs.instr_map),
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ take 4 (drop 20 IslaTraces.write_success_66.instrs.instr_map),
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15434 (blobSaveLoads12Post row count base bytes index
    (blobLoaded4Frame bytes index (blobLoaded24Frame bytes index
      (blobLoaded28Frame bytes index (blobLoaded20Frame bytes index
        (blobLoaded16Frame bytes index P)))))) -∗
  instr_body 0x153d4 (blobLoads16Entry row base bytes index
    (blobLoad20Frame bytes index (blobUpperLoadFrame count bytes index P))).
Proof.
  iStartProof. iIntros "#H16 #H20 #H28 #H24 #H4 #H12 Hnext".
  iPoseProof (blob_loads4_save12_correct row count base bytes index
    (blobLoaded24Frame bytes index (blobLoaded28Frame bytes index
      (blobLoaded20Frame bytes index (blobLoaded16Frame bytes index P))))
    with "H4 H12 Hnext") as "Hlower".
  iAssert (instr_body 0x15414 (blobLoads24Post row base bytes index
    (blobLoaded28Frame bytes index (blobLoaded20Frame bytes index
      (blobLoaded16Frame bytes index (blobLowerLoadFrame count bytes index P))))))
    with "[Hlower]" as "Hhandoff".
  { iApply (instr_pre_wand 0x15414 0x15414 false false with "Hlower");
      [done | reflexivity |]. iApply blob_load24_to_load4. }
  iPoseProof (blob_loads28_24_correct row base bytes index
    (blobLoaded20Frame bytes index (blobLoaded16Frame bytes index
      (blobLowerLoadFrame count bytes index P))) with "H28 H24 Hhandoff") as "Hupper".
  iApply (blob_loads16_20_correct row base bytes index
    (blobUpperLoadFrame count bytes index P) with "H16 H20").
  iApply (instr_pre_wand 0x153f4 0x153f4 false false with "Hupper");
    [done | reflexivity |]. iApply blob_load20_to_load28.
Qed.
Print Assumptions blob_initial_loads_correct.
