Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsFlagLoads.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactStorageKeysLoads16 WriteSuccessExactStorageKeysLoads20
  WriteSuccessExactStorageKeysLoads28 WriteSuccessExactStorageKeysLoads24
  WriteSuccessExactStorageKeysLoads4 WriteSuccessExactStorageKeysLoads12.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactStorageKeysLoadHandoff.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactStorageKeysUpperLoadHandoff.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactStorageKeysLowerLoadHandoff.
From IslaTraces.write_success_58 Require Import instrs.

Definition storageKeysLoaded20Frame `{!islaG Sigma} `{!threadG}
    (bytes : list (bv 8)) (index : nat) (P : iProp Sigma) : iProp Sigma :=
  ("x8" ↦ᵣ RVal_Bits (transactionRowByte bytes index 20) ∗
   "x26" ↦ᵣ RVal_Bits (transactionRowByte bytes index 21) ∗
   "x9" ↦ᵣ RVal_Bits (transactionRowByte bytes index 22) ∗
   "x25" ↦ᵣ RVal_Bits (transactionRowByte bytes index 23) ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@storageKeysLoaded20Frame) := I.

Definition storageKeysLoaded24Frame `{!islaG Sigma} `{!threadG}
    (bytes : list (bv 8)) (index : nat) (P : iProp Sigma) : iProp Sigma :=
  ("x11" ↦ᵣ RVal_Bits (transactionRowByte bytes index 24) ∗
   "x5" ↦ᵣ RVal_Bits (transactionRowByte bytes index 25) ∗
   "x17" ↦ᵣ RVal_Bits (transactionRowByte bytes index 26) ∗
   "x16" ↦ᵣ RVal_Bits (transactionRowByte bytes index 27) ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@storageKeysLoaded24Frame) := I.

Definition storageKeysLowerLoadFrame `{!islaG Sigma} `{!threadG}
    (bytes : list (bv 8)) (index : nat) (P : iProp Sigma) : iProp Sigma :=
  (reg_col [(KindReg "x15", BitsShape 64); (KindReg "x31", BitsShape 64);
    (KindReg "x30", BitsShape 64); (KindReg "x29", BitsShape 64)] ∗
   storageKeysLoad12Frame bytes index P ∗ True)%I.
Global Instance : LithiumUnfold (@storageKeysLowerLoadFrame) := I.

Definition storageKeysUpperLoadFrame `{!islaG Sigma} `{!threadG}
    (bytes : list (bv 8)) (index : nat) (P : iProp Sigma) : iProp Sigma :=
  (reg_col [(KindReg "x10", BitsShape 64); (KindReg "x14", BitsShape 64);
    (KindReg "x13", BitsShape 64); (KindReg "x12", BitsShape 64)] ∗
   ⌜(index + 32 <= length bytes)%nat⌝ ∗
   storageKeysLoad24Frame bytes index (storageKeysLowerLoadFrame bytes index P) ∗ True)%I.
Global Instance : LithiumUnfold (@storageKeysUpperLoadFrame) := I.

Lemma storage_keys_load20_to_load28 `{!islaG Sigma} `{!threadG}
    row base bytes index (P : iProp Sigma) :
  storageKeysLoads20Post row base bytes index (storageKeysLoaded16Frame bytes index
    (storageKeysUpperLoadFrame bytes index P)) -∗
  storageKeysLoads28Entry row base bytes index (storageKeysLoad24Frame bytes index
    (storageKeysLoaded20Frame bytes index (storageKeysLoaded16Frame bytes index
      (storageKeysLowerLoadFrame bytes index P)))).
Proof.
  iIntros "Hfirst".
  iEval (unfold storageKeysLoads20Post, storageKeysLoaded16Frame,
    storageKeysUpperLoadFrame, storageKeysLoad24Frame) in "Hfirst".
  iDestruct "Hfirst" as
    "(Hsys & H8 & H26 & H9 & H25 & Hrow & Harray & %Hcursor & %Hbound24 & %Hlow & %Hhigh & (H6 & H7 & H28 & H1 & (Hregs & %Hbound32 & (Hregs24 & %Hbound28 & Hlower & _) & _) & _) & _)".
  iEval (unfold storageKeysLoads28Entry, storageKeysLoad24Frame,
    storageKeysLoaded20Frame, storageKeysLoaded16Frame).
  iFrame. done.
Qed.
Print Assumptions storage_keys_load20_to_load28.

Lemma storage_keys_load24_to_load4 `{!islaG Sigma} `{!threadG}
    row base bytes index (P : iProp Sigma) :
  storageKeysLoads24Post row base bytes index (storageKeysLoaded28Frame bytes index
    (storageKeysLoaded20Frame bytes index (storageKeysLoaded16Frame bytes index
      (storageKeysLowerLoadFrame bytes index P)))) -∗
  storageKeysLoads4Entry row base bytes index (storageKeysLoad12Frame bytes index
    (storageKeysLoaded24Frame bytes index (storageKeysLoaded28Frame bytes index
      (storageKeysLoaded20Frame bytes index (storageKeysLoaded16Frame bytes index P))))).
Proof.
  iIntros "Hfirst".
  iEval (unfold storageKeysLoads24Post, storageKeysLoaded28Frame,
    storageKeysLoaded20Frame, storageKeysLoaded16Frame, storageKeysLowerLoadFrame) in "Hfirst".
  iDestruct "Hfirst" as
    "(Hsys & H11 & H5 & H17 & H16 & Hrow & Harray & %Hcursor & %Hbound28 & %Hlow & %Hhigh & (H10 & H14 & H13 & H12 & (H8 & H26 & H9 & H25 & (H6 & H7 & H28 & H1 & (Hregs & Hlower & _) & _) & _) & _) & _)".
  iEval (unfold storageKeysLoads4Entry, storageKeysLoad12Frame,
    storageKeysLoaded24Frame, storageKeysLoaded28Frame,
    storageKeysLoaded20Frame, storageKeysLoaded16Frame).
  iEval (unfold storageKeysLoad12Frame) in "Hlower".
  iDestruct "Hlower" as "(Hregs12 & %Hbound16 & HP & _)".
  iFrame. iPureIntro. lia.
Qed.
Print Assumptions storage_keys_load24_to_load4.

Lemma storage_keys_initial_loads_correct `{!islaG Sigma} `{!threadG}
    row base bytes index (P : iProp Sigma) :
  ([∗ list] instruction ∈ take 4 IslaTraces.write_success_58.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ take 4 (drop 4 IslaTraces.write_success_58.instrs.instr_map),
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ take 4 (drop 8 IslaTraces.write_success_58.instrs.instr_map),
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ take 4 (drop 12 IslaTraces.write_success_58.instrs.instr_map),
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ take 4 (drop 16 IslaTraces.write_success_58.instrs.instr_map),
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ take 4 (drop 20 IslaTraces.write_success_58.instrs.instr_map),
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15288 (storageKeysLoads12Post row base bytes index
    (storageKeysLoaded4Frame bytes index (storageKeysLoaded24Frame bytes index
      (storageKeysLoaded28Frame bytes index (storageKeysLoaded20Frame bytes index
        (storageKeysLoaded16Frame bytes index P)))))) -∗
  instr_body 0x15228 (storageKeysLoads16Entry row base bytes index
    (storageKeysLoad20Frame bytes index (storageKeysUpperLoadFrame bytes index P))).
Proof.
  iStartProof. iIntros "#H16 #H20 #H28 #H24 #H4 #H12 Hnext".
  iPoseProof (storage_keys_loads4_12_correct row base bytes index
    (storageKeysLoaded24Frame bytes index (storageKeysLoaded28Frame bytes index
      (storageKeysLoaded20Frame bytes index (storageKeysLoaded16Frame bytes index P))))
    with "H4 H12 Hnext") as "Hlower".
  iAssert (instr_body 0x15268 (storageKeysLoads24Post row base bytes index
    (storageKeysLoaded28Frame bytes index (storageKeysLoaded20Frame bytes index
      (storageKeysLoaded16Frame bytes index (storageKeysLowerLoadFrame bytes index P))))))
    with "[Hlower]" as "Hhandoff".
  { iApply (instr_pre_wand 0x15268 0x15268 false false with "Hlower");
      [done | reflexivity |]. iApply storage_keys_load24_to_load4. }
  iPoseProof (storage_keys_loads28_24_correct row base bytes index
    (storageKeysLoaded20Frame bytes index (storageKeysLoaded16Frame bytes index
      (storageKeysLowerLoadFrame bytes index P))) with "H28 H24 Hhandoff") as "Hupper".
  iApply (storage_keys_loads16_20_correct row base bytes index
    (storageKeysUpperLoadFrame bytes index P) with "H16 H20").
  iApply (instr_pre_wand 0x15248 0x15248 false false with "Hupper");
    [done | reflexivity |]. iApply storage_keys_load20_to_load28.
Qed.
Print Assumptions storage_keys_initial_loads_correct.
