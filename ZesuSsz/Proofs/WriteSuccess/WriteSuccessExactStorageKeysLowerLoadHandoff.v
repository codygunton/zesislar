Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactStorageKeysLoads4.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactStorageKeysLoads12.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsFlagLoads.
From IslaTraces.write_success_58 Require Import instrs.

Definition storageKeysLoad12Frame `{!islaG Sigma} `{!threadG} (bytes : list (bv 8))
    (index : nat) (P : iProp Sigma) : iProp Sigma :=
  (reg_col [(KindReg "x24", BitsShape 64); (KindReg "x20", BitsShape 64);
    (KindReg "x18", BitsShape 64); (KindReg "x23", BitsShape 64)] ∗
   ⌜(index + 16 <= length bytes)%nat⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@storageKeysLoad12Frame) := I.

Definition storageKeysLoaded4Frame `{!islaG Sigma} `{!threadG}
    (bytes : list (bv 8)) (index : nat) (P : iProp Sigma) : iProp Sigma :=
  ("x15" ↦ᵣ RVal_Bits (transactionRowByte bytes index 4) ∗
   "x31" ↦ᵣ RVal_Bits (transactionRowByte bytes index 5) ∗
   "x30" ↦ᵣ RVal_Bits (transactionRowByte bytes index 6) ∗
   "x29" ↦ᵣ RVal_Bits (transactionRowByte bytes index 7) ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@storageKeysLoaded4Frame) := I.

Lemma storage_keys_load4_to_load12 `{!islaG Sigma} `{!threadG}
    row base bytes index (P : iProp Sigma) :
  storageKeysLoads4Post row base bytes index (storageKeysLoad12Frame bytes index P) -∗
  storageKeysLoads12Entry row base bytes index (storageKeysLoaded4Frame bytes index P).
Proof.
  iIntros "Hfirst". iEval (unfold storageKeysLoads4Post) in "Hfirst".
  iDestruct "Hfirst" as
    "(Hsys & H6 & H7 & H28 & H1 & Hrow & Harray & %Hcursor & %Hbound & %Hlow & %Hhigh & Hframe & _)".
  iEval (unfold storageKeysLoad12Frame) in "Hframe".
  iDestruct "Hframe" as "(Hregs & %Hbound24 & HP & _)".
  iEval (unfold storageKeysLoads12Entry, storageKeysLoaded4Frame).
  iFrame. done.
Qed.
Print Assumptions storage_keys_load4_to_load12.

Lemma storage_keys_loads4_12_correct `{!islaG Sigma} `{!threadG}
    row base bytes index (P : iProp Sigma) :
  ([∗ list] instruction ∈ take 4 (drop 16 IslaTraces.write_success_58.instrs.instr_map),
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ take 4 (drop 20 IslaTraces.write_success_58.instrs.instr_map),
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15288 (storageKeysLoads12Post row base bytes index
    (storageKeysLoaded4Frame bytes index P)) -∗
  instr_body 0x15268 (storageKeysLoads4Entry row base bytes index
    (storageKeysLoad12Frame bytes index P)).
Proof.
  iStartProof. iIntros "#H16 #H20 Hnext".
  iPoseProof (storage_keys_loads12_correct row base bytes index
    (storageKeysLoaded4Frame bytes index P) with "H20 Hnext") as "Hmid".
  iApply (storage_keys_loads4_correct row base bytes index
    (storageKeysLoad12Frame bytes index P) with "H16").
  iApply (instr_pre_wand 0x15278 0x15278 false false with "Hmid");
    [done | reflexivity |].
  iApply storage_keys_load4_to_load12.
Qed.
Print Assumptions storage_keys_loads4_12_correct.
