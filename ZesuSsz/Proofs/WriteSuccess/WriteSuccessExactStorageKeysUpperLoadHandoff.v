Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactStorageKeysLoads28.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactStorageKeysLoads24.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsFlagLoads.
From IslaTraces.write_success_58 Require Import instrs.

Definition storageKeysLoad24Frame `{!islaG Sigma} `{!threadG} (bytes : list (bv 8))
    (index : nat) (P : iProp Sigma) : iProp Sigma :=
  (reg_col [(KindReg "x11", BitsShape 64); (KindReg "x5", BitsShape 64);
    (KindReg "x17", BitsShape 64); (KindReg "x16", BitsShape 64)] ∗
   ⌜(index + 28 <= length bytes)%nat⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@storageKeysLoad24Frame) := I.

Definition storageKeysLoaded28Frame `{!islaG Sigma} `{!threadG}
    (bytes : list (bv 8)) (index : nat) (P : iProp Sigma) : iProp Sigma :=
  ("x10" ↦ᵣ RVal_Bits (transactionRowByte bytes index 28) ∗
   "x14" ↦ᵣ RVal_Bits (transactionRowByte bytes index 29) ∗
   "x13" ↦ᵣ RVal_Bits (transactionRowByte bytes index 30) ∗
   "x12" ↦ᵣ RVal_Bits (transactionRowByte bytes index 31) ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@storageKeysLoaded28Frame) := I.

Lemma storage_keys_load28_to_load24 `{!islaG Sigma} `{!threadG}
    row base bytes index (P : iProp Sigma) :
  storageKeysLoads28Post row base bytes index (storageKeysLoad24Frame bytes index P) -∗
  storageKeysLoads24Entry row base bytes index (storageKeysLoaded28Frame bytes index P).
Proof.
  iIntros "Hfirst". iEval (unfold storageKeysLoads28Post) in "Hfirst".
  iDestruct "Hfirst" as
    "(Hsys & H6 & H7 & H28 & H1 & Hrow & Harray & %Hcursor & %Hbound & %Hlow & %Hhigh & Hframe & _)".
  iEval (unfold storageKeysLoad24Frame) in "Hframe".
  iDestruct "Hframe" as "(Hregs & %Hbound24 & HP & _)".
  iEval (unfold storageKeysLoads24Entry, storageKeysLoaded28Frame).
  iFrame. done.
Qed.
Print Assumptions storage_keys_load28_to_load24.

Lemma storage_keys_loads28_24_correct `{!islaG Sigma} `{!threadG}
    row base bytes index (P : iProp Sigma) :
  ([∗ list] instruction ∈ take 4 (drop 8 IslaTraces.write_success_58.instrs.instr_map),
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ take 4 (drop 12 IslaTraces.write_success_58.instrs.instr_map),
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15268 (storageKeysLoads24Post row base bytes index
    (storageKeysLoaded28Frame bytes index P)) -∗
  instr_body 0x15248 (storageKeysLoads28Entry row base bytes index
    (storageKeysLoad24Frame bytes index P)).
Proof.
  iStartProof. iIntros "#H16 #H20 Hnext".
  iPoseProof (storage_keys_loads24_correct row base bytes index
    (storageKeysLoaded28Frame bytes index P) with "H20 Hnext") as "Hmid".
  iApply (storage_keys_loads28_correct row base bytes index
    (storageKeysLoad24Frame bytes index P) with "H16").
  iApply (instr_pre_wand 0x15258 0x15258 false false with "Hmid");
    [done | reflexivity |].
  iApply storage_keys_load28_to_load24.
Qed.
Print Assumptions storage_keys_loads28_24_correct.
