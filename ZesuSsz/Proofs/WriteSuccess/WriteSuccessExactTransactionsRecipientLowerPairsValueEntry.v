Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.ArrayByteViews.
Require Import ZesuSsz.Automation.RegPacking.
Require Import ZesuSsz.Automation.Resources.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsRecipientLowerShiftsPairsEntry WriteSuccessExactTransactionsRecipientLowerPairs
  WriteSuccessExactTransactionsValuePrefix WriteSuccessExactTransactionsRecipientTagShiftEntry
  WriteSuccessExactTransactionsSignatureFieldEntry WriteSuccessExactTransactionsGasSignatureEntry
  WriteSuccessExactTransactionsGasLoads WriteSuccessExactTransactionsFlagLoads.
Local Open Scope Z_scope.

Definition transactionValuePrefixCaller `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col [(KindReg "x27", BitsShape 64)] ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionValuePrefixCaller) := I.

Definition transactionValuePrefixRetained `{!islaG Sigma} `{!threadG}
    (sp row chain chainTag : bv 64) bytes index (P : iProp Sigma) : iProp Sigma :=
  ("x13" ↦ᵣ RVal_Bits (Z_to_bv 64
     (bv_unsigned (default (BV 8 0) (bytes !! (index + 279)%nat)) * 65536 + bv_unsigned (default (BV 8 0) (bytes !! (index + 280)%nat)) * 16777216)) ∗
   "x12" ↦ᵣ RVal_Bits (Z_to_bv 64
     (bv_unsigned (default (BV 8 0) (bytes !! (index + 265)%nat)) + bv_unsigned (default (BV 8 0) (bytes !! (index + 266)%nat)) * 256)) ∗
   "x7" ↦ᵣ RVal_Bits (Z_to_bv 64
     (bv_unsigned (default (BV 8 0) (bytes !! (index + 267)%nat)) * 65536 + bv_unsigned (default (BV 8 0) (bytes !! (index + 268)%nat)) * 16777216)) ∗
   "x28" ↦ᵣ RVal_Bits (Z_to_bv 64
     (bv_unsigned (default (BV 8 0) (bytes !! (index + 269)%nat)) + bv_unsigned (default (BV 8 0) (bytes !! (index + 270)%nat)) * 256)) ∗
   "x19" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned (default (BV 8 0) (bytes !! (index + 266)%nat)) * 256)) ∗
   transactionRecipientLowerPairRegisters bytes index
     (transactionRecipientAssemblyStackFrame sp row chain chainTag bytes index P) ∗ True)%I.
Global Instance : LithiumUnfold (@transactionValuePrefixRetained) := I.

Lemma transactions_recipient_lower_pairs_value_entry `{!islaG Sigma} `{!threadG}
    sp row chain chainTag base bytes index (P : iProp Sigma) :
  transactionRecipientLowerPairsPost
    (default (BV 8 0) (bytes !! (index + 279)%nat))
    (default (BV 8 0) (bytes !! (index + 280)%nat))
    (default (BV 8 0) (bytes !! (index + 265)%nat))
    (default (BV 8 0) (bytes !! (index + 266)%nat))
    (default (BV 8 0) (bytes !! (index + 267)%nat))
    (default (BV 8 0) (bytes !! (index + 268)%nat))
    (default (BV 8 0) (bytes !! (index + 269)%nat))
    (default (BV 8 0) (bytes !! (index + 270)%nat))
    (transactionRecipientLowerPairRetained sp row chain chainTag base bytes index (transactionValuePrefixCaller P)) -∗
  transactionValuePrefixEntry row base bytes index
    (transactionValuePrefixRetained sp row chain chainTag bytes index P).
Proof.
  iStartProof. iIntros "Hpost".
  iEval (rewrite /transactionRecipientLowerPairsPost /transactionRecipientLowerPairRetained
    /transactionRecipientLowerPairRegisters /transactionRecipientAssemblyDataFrame
    /transactionRecipientAssemblyStackFrame /transactionRecipientAssemblyFields
    /transactionSignatureFieldRetained /transactionGasSignatureRetained) in "Hpost".
  iDestruct "Hpost" as "(Hsys & H13 & H18 & H12 & H19 & H7 & H20 & H28 & H29 & Hframe & _)".
  iPoseProof (reg_col_bv_list_shape
    [("x18", Z_to_bv 64 (bv_unsigned (default (BV 8 0) (bytes !! (index + 279)%nat)) * 65536));
     ("x20", Z_to_bv 64 (bv_unsigned (default (BV 8 0) (bytes !! (index + 267)%nat)) * 65536));
     ("x29", Z_to_bv 64 (bv_unsigned (default (BV 8 0) (bytes !! (index + 270)%nat)) * 256))]
    with "[H18 H20 H29]") as "Hclobbered".
  { cbn. iFrame. }
  zesu_open_resource_groups.
  iSelect (transactionValuePrefixCaller P) ltac:(fun H =>
    iDestruct H as "(H27 & HP & _)").
  iAssert (reg_col [(KindReg "x27", BitsShape 64); (KindReg "x18", BitsShape 64);
    (KindReg "x20", BitsShape 64); (KindReg "x29", BitsShape 64)])%I
    with "[H27 Hclobbered]" as "Hregs".
  { rewrite /reg_col /=.
    iEval (rewrite /reg_col /=) in "H27".
    iEval (rewrite /reg_col /=) in "Hclobbered".
    iDestruct "H27" as "[H27 _]". iFrame. }
  rewrite /transactionValuePrefixEntry /transactionValuePrefixRetained
    /transactionRecipientLowerPairRegisters /transactionRecipientAssemblyStackFrame
    /transactionRecipientAssemblyFields /transactionSignatureFieldRetained /transactionGasSignatureRetained.
  iFrame. repeat iSplit; try done; iPureIntro; lia.
Qed.
Print Assumptions transactions_recipient_lower_pairs_value_entry.

