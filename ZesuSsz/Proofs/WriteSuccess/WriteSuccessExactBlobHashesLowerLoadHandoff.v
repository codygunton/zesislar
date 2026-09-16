Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactBlobHashesLoads4.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactBlobHashesSaveLoads12.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsFlagLoads.
From IslaTraces.write_success_66 Require Import instrs.

Definition blobLoad12Frame `{!islaG Sigma} `{!threadG} (count : bv 64)
    (bytes : list (bv 8)) (index : nat) (P : iProp Sigma) : iProp Sigma :=
  (reg_col [(KindReg "x27", BitsShape 64); (KindReg "x23", BitsShape 64);
     (KindReg "x24", BitsShape 64)] ∗ "x22" ↦ᵣ RVal_Bits count ∗
   ⌜(index + 15 <= length bytes)%nat⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@blobLoad12Frame) := I.

Definition blobLoaded4Frame `{!islaG Sigma} `{!threadG}
    (bytes : list (bv 8)) (index : nat) (P : iProp Sigma) : iProp Sigma :=
  ("x15" ↦ᵣ RVal_Bits (transactionRowByte bytes index 4) ∗
   "x31" ↦ᵣ RVal_Bits (transactionRowByte bytes index 5) ∗
   "x30" ↦ᵣ RVal_Bits (transactionRowByte bytes index 6) ∗
   "x29" ↦ᵣ RVal_Bits (transactionRowByte bytes index 7) ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@blobLoaded4Frame) := I.

Lemma blob_load4_to_save_load12 `{!islaG Sigma} `{!threadG}
    row count base bytes index (P : iProp Sigma) :
  blobLoads4Post row base bytes index (blobLoad12Frame count bytes index P) -∗
  blobSaveLoads12Entry row count base bytes index (blobLoaded4Frame bytes index P).
Proof.
  iIntros "Hfirst". iEval (unfold blobLoads4Post) in "Hfirst".
  iDestruct "Hfirst" as
    "(Hsys & H15 & H31 & H30 & H29 & Hrow & Harray & %Hcursor & %Hbound & %Hlow & %Hhigh & Hframe & _)".
  iEval (unfold blobLoad12Frame) in "Hframe".
  iDestruct "Hframe" as "(Hregs & Hcount & %Hbound15 & HP & _)".
  iEval (unfold blobSaveLoads12Entry, blobLoaded4Frame).
  iFrame. done.
Qed.
Print Assumptions blob_load4_to_save_load12.

Lemma blob_loads4_save12_correct `{!islaG Sigma} `{!threadG}
    row count base bytes index (P : iProp Sigma) :
  ([∗ list] instruction ∈ take 4 (drop 16 IslaTraces.write_success_66.instrs.instr_map),
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ take 4 (drop 20 IslaTraces.write_success_66.instrs.instr_map),
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15434 (blobSaveLoads12Post row count base bytes index
    (blobLoaded4Frame bytes index P)) -∗
  instr_body 0x15414 (blobLoads4Entry row base bytes index
    (blobLoad12Frame count bytes index P)).
Proof.
  iStartProof. iIntros "#H4 #H12 Hnext".
  iPoseProof (blob_save_loads12_correct row count base bytes index
    (blobLoaded4Frame bytes index P) with "H12 Hnext") as "Hmid".
  iApply (blob_loads4_correct row base bytes index
    (blobLoad12Frame count bytes index P) with "H4").
  iApply (instr_pre_wand 0x15424 0x15424 false false with "Hmid");
    [done | reflexivity |].
  iApply blob_load4_to_save_load12.
Qed.
Print Assumptions blob_loads4_save12_correct.
