Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.RegPacking.
Require Import ZesuSsz.Automation.Resources.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsWideSignatureSuffixEntry WriteSuccessExactTransactionsSignatureTail
  WriteSuccessExactTransactionsNestedLists WriteSuccessExactTransactionsNestedSuffix
  WriteSuccessExactTransactionsSignatureLowWideEntry WriteSuccessExactTransactionsValueMiddleWordsEntry
  WriteSuccessExactTransactionsRecipientTagShiftEntry WriteSuccessExactTransactionsSignatureFieldEntry
  WriteSuccessExactTransactionsGasSignatureEntry WriteSuccessExactTransactionsGasLoads
  WriteSuccessExactTransactionsFlagLoads.
Local Open Scope Z_scope.

Definition transactionNestedListsCaller `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (reg_col [(KindReg "x22", BitsShape 64)] ∗
   (bv_unsigned sp + 256) ↦ₘ? 16 ∗ (bv_unsigned sp + 1640) ↦ₘ? 8 ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionNestedListsCaller) := I.

Definition transactionNestedSuffixCaller `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (P : iProp Sigma) : iProp Sigma :=
  ((bv_unsigned sp + 136) ↦ₘ? 8 ∗ (bv_unsigned sp + 160) ↦ₘ? 16 ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionNestedSuffixCaller) := I.

Definition transactionNestedRecipientContext `{!islaG Sigma} `{!threadG}
    (bytes : list (bv 8)) (index : nat) (P : iProp Sigma) : iProp Sigma :=
  ("x16" ↦ᵣ RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8 [(default (BV 8 0) (bytes !! (index + 269)%nat)); (default (BV 8 0) (bytes !! (index + 270)%nat)); (default (BV 8 0) (bytes !! (index + 271)%nat)); (default (BV 8 0) (bytes !! (index + 272)%nat))] * 4294967296)) ∗
   "x13" ↦ᵣ RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8 [(default (BV 8 0) (bytes !! (index + 273)%nat)); (default (BV 8 0) (bytes !! (index + 274)%nat)); (default (BV 8 0) (bytes !! (index + 275)%nat)); (default (BV 8 0) (bytes !! (index + 276)%nat)); (default (BV 8 0) (bytes !! (index + 277)%nat)); (default (BV 8 0) (bytes !! (index + 278)%nat)); (default (BV 8 0) (bytes !! (index + 279)%nat)); (default (BV 8 0) (bytes !! (index + 280)%nat))])) ∗
   "x7" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (default (BV 8 0) (bytes !! (index + 267)%nat)) * 65536 + bv_unsigned (default (BV 8 0) (bytes !! (index + 268)%nat)) * 16777216)) ∗
   "x28" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (default (BV 8 0) (bytes !! (index + 269)%nat)) + bv_unsigned (default (BV 8 0) (bytes !! (index + 270)%nat)) * 256)) ∗
   "x5" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (default (BV 8 0) (bytes !! (index + 271)%nat)) * 65536 + bv_unsigned (default (BV 8 0) (bytes !! (index + 272)%nat)) * 16777216)) ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionNestedRecipientContext) := I.

Definition transactionStoredSignatureTail `{!islaG Sigma} `{!threadG}
    (sp row chain chainTag : bv 64) (bytes : list (bv 8)) (index : nat) (P : iProp Sigma) : iProp Sigma :=
  ("x15" ↦ᵣ RVal_Bits (transactionRowWord bytes index 128) ∗
   (bv_unsigned sp + 208) ↦ₘ (transactionRowWord bytes index 128) ∗
   (bv_unsigned sp + 184) ↦ₘ (transactionRowWord bytes index 120) ∗
   (bv_unsigned sp + 192) ↦ₘ (transactionRowWord bytes index 112) ∗
   (bv_unsigned sp + 200) ↦ₘ (transactionRowWord bytes index 104) ∗
   transactionSignatureStackFrame sp row chain chainTag bytes index P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionStoredSignatureTail) := I.

Definition transactionNestedListsRetained `{!islaG Sigma} `{!threadG}
    (sp row chain chainTag : bv 64) (bytes : list (bv 8)) (index : nat) (P : iProp Sigma) : iProp Sigma :=
  transactionNestedRecipientContext bytes index
    (transactionRecipientWideRegisters bytes index
      (transactionStoredSignatureTail sp row chain chainTag bytes index P)).
Global Instance : LithiumUnfold (@transactionNestedListsRetained) := I.

Definition transactionNestedRegistersNo19 `{!islaG Sigma} `{!threadG}
    (bytes : list (bv 8)) (index : nat) (P : iProp Sigma) : iProp Sigma :=
  ("x14" ↦ᵣ RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8 [(default (BV 8 0) (bytes !! (index + 281)%nat)); (default (BV 8 0) (bytes !! (index + 282)%nat)); (default (BV 8 0) (bytes !! (index + 283)%nat)); (default (BV 8 0) (bytes !! (index + 284)%nat))])) ∗
   "x17" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (default (BV 8 0) (bytes !! (index + 275)%nat)) * 65536 + bv_unsigned (default (BV 8 0) (bytes !! (index + 276)%nat)) * 16777216)) ∗
   "x6" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (default (BV 8 0) (bytes !! (index + 277)%nat)) + bv_unsigned (default (BV 8 0) (bytes !! (index + 278)%nat)) * 256)) ∗
   "x29" ↦ᵣ RVal_Bits (transactionRowWord bytes index 64) ∗
   "x30" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (default (BV 8 0) (bytes !! (index + 271)%nat)) * 65536)) ∗
   "x27" ↦ᵣ RVal_Bits (transactionRowByte bytes index 32) ∗
   "x18" ↦ᵣ RVal_Bits (transactionRowWord bytes index 48) ∗
   "x20" ↦ᵣ RVal_Bits (transactionRowWord bytes index 56) ∗
   "x31" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (default (BV 8 0) (bytes !! (index + 278)%nat)) * 256)) ∗
   "x11" ↦ᵣ RVal_Bits (transactionRowByte bytes index 264) ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionNestedRegistersNo19) := I.

Definition transactionNestedSuffixRetained `{!islaG Sigma} `{!threadG}
    (sp row chain chainTag : bv 64) (bytes : list (bv 8)) (index : nat) (P : iProp Sigma) : iProp Sigma :=
  ("x22" ↦ᵣ RVal_Bits (transactionRowWord bytes index 200) ∗
   (bv_unsigned sp + 256) ↦ₘ (transactionRowWord bytes index 208) ∗
   (bv_unsigned sp + 264) ↦ₘ (transactionRowWord bytes index 216) ∗
   (bv_unsigned sp + 1640) ↦ₘ (Z_to_bv 64 (little_endian_to_bv 8 [(default (BV 8 0) (bytes !! (index + 265)%nat)); (default (BV 8 0) (bytes !! (index + 266)%nat)); (default (BV 8 0) (bytes !! (index + 267)%nat)); (default (BV 8 0) (bytes !! (index + 268)%nat)); (default (BV 8 0) (bytes !! (index + 269)%nat)); (default (BV 8 0) (bytes !! (index + 270)%nat)); (default (BV 8 0) (bytes !! (index + 271)%nat)); (default (BV 8 0) (bytes !! (index + 272)%nat))])) ∗
   transactionNestedRecipientContext bytes index
     (transactionNestedRegistersNo19 bytes index
       (transactionStoredSignatureTail sp row chain chainTag bytes index P)) ∗ True)%I.
Global Instance : LithiumUnfold (@transactionNestedSuffixRetained) := I.

Lemma transactions_signature_tail_nested_lists_entry `{!islaG Sigma} `{!threadG}
    sp row chain chainTag base (bytes : list (bv 8)) (index : nat) (P : iProp Sigma) :
  transactionSignatureTailPost sp row base bytes index
    (transactionSignatureTailRetained sp row chain chainTag bytes index (transactionNestedListsCaller sp P)) -∗
  transactionNestedListsEntry sp row (Z_to_bv 64 (little_endian_to_bv 8 [(default (BV 8 0) (bytes !! (index + 265)%nat)); (default (BV 8 0) (bytes !! (index + 266)%nat)); (default (BV 8 0) (bytes !! (index + 267)%nat)); (default (BV 8 0) (bytes !! (index + 268)%nat)); (default (BV 8 0) (bytes !! (index + 269)%nat)); (default (BV 8 0) (bytes !! (index + 270)%nat)); (default (BV 8 0) (bytes !! (index + 271)%nat)); (default (BV 8 0) (bytes !! (index + 272)%nat))])) base bytes index
    (transactionNestedListsRetained sp row chain chainTag bytes index P).
Proof.
  iStartProof. iIntros "Hpost".
  iEval (rewrite /transactionSignatureTailPost /transactionSignatureTailRetained
    /transactionSignatureSuffixRetained /transactionRecipientWideRegisters
    /transactionSignatureStackFrame /transactionRecipientAssemblyStackContents
    /transactionRecipientAssemblyFields /transactionSignatureFieldRetained
    /transactionGasSignatureRetained /transactionNestedListsCaller) in "Hpost".
  zesu_open_resource_groups.
  rewrite /transactionNestedListsEntry /transactionNestedListsRetained /transactionNestedRecipientContext
    /transactionRecipientWideRegisters /transactionStoredSignatureTail /transactionSignatureStackFrame
    /transactionRecipientAssemblyStackContents /transactionRecipientAssemblyFields
    /transactionSignatureFieldRetained /transactionGasSignatureRetained.
  iFrame. repeat iSplit; try done; iPureIntro; lia.
Qed.
Print Assumptions transactions_signature_tail_nested_lists_entry.

Lemma transactions_nested_lists_suffix_entry `{!islaG Sigma} `{!threadG}
    sp row chain chainTag base (bytes : list (bv 8)) (index : nat) (P : iProp Sigma) :
  transactionNestedListsPost sp row (Z_to_bv 64 (little_endian_to_bv 8 [(default (BV 8 0) (bytes !! (index + 265)%nat)); (default (BV 8 0) (bytes !! (index + 266)%nat)); (default (BV 8 0) (bytes !! (index + 267)%nat)); (default (BV 8 0) (bytes !! (index + 268)%nat)); (default (BV 8 0) (bytes !! (index + 269)%nat)); (default (BV 8 0) (bytes !! (index + 270)%nat)); (default (BV 8 0) (bytes !! (index + 271)%nat)); (default (BV 8 0) (bytes !! (index + 272)%nat))])) base bytes index
    (transactionNestedListsRetained sp row chain chainTag bytes index (transactionNestedSuffixCaller sp P)) -∗
  transactionNestedSuffixEntry sp row base bytes index
    (transactionNestedSuffixRetained sp row chain chainTag bytes index P).
Proof.
  iStartProof. iIntros "Hpost".
  iEval (rewrite /transactionNestedListsPost) in "Hpost".
  iDestruct "Hpost" as "(Hsys & Hsp & Hrow & H12 & H22 & Hframe)".
  iEval (rewrite /transactionNestedListsRetained /transactionNestedRecipientContext
    /transactionRecipientWideRegisters) in "Hframe".
  iDestruct "Hframe" as "(Hbytes & H256 & H264 & H1640 & %Hcursor & %Hlength & %Hrowalign &
    %Hspalign & %Hmin & %Hmax & %Hspmin & %Hspmax & (H16 & H13 & H7 & H28 & H5 &
    (H14 & H17 & H6 & H29 & H30 & H27 & H18 & H20 & H19 & H31 & H11 & Hrest & _) & _) & _)".
  iPoseProof (reg_col_bv_list_shape
    [("x19", Z_to_bv 64 (bv_unsigned (default (BV 8 0) (bytes !! (index + 266)%nat)) * 256)); ("x12", transactionRowWord bytes index 216)]
    with "[H19 H12]") as "Hregs".
  { cbn. iFrame. }
  iEval (rewrite /transactionStoredSignatureTail /transactionSignatureStackFrame
    /transactionRecipientAssemblyStackContents /transactionRecipientAssemblyFields
    /transactionSignatureFieldRetained /transactionGasSignatureRetained
    /transactionNestedSuffixCaller) in "Hrest".
  zesu_open_resource_groups.
  rewrite /transactionNestedSuffixEntry /transactionNestedSuffixRetained /transactionNestedRecipientContext
    /transactionNestedRegistersNo19 /transactionStoredSignatureTail /transactionSignatureStackFrame
    /transactionRecipientAssemblyStackContents /transactionRecipientAssemblyFields
    /transactionSignatureFieldRetained /transactionGasSignatureRetained.
  iFrame. repeat iSplit; try done; iPureIntro; lia.
Qed.
Print Assumptions transactions_nested_lists_suffix_entry.

