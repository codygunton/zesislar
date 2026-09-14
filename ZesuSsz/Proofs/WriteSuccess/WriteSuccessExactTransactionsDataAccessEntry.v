Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.RegPacking.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsRecipientAccessMemory WriteSuccessExactTransactionsGasToRecipient
  WriteSuccessExactTransactionsGasPriceCall WriteSuccessExactTransactionsNonceToGasPrice
  WriteSuccessExactTransactionsRecipientValueRegion WriteSuccessExactTransactionsValueToData
  WriteSuccessExactTransactionsValueCall WriteSuccessExactTransactionsDataToAccessCount
  WriteSuccessExactTransactionsAccessCountCall WriteSuccessExactEncoderIntFramedCall
  WriteSuccessExactAccessListsControl WriteSuccessExactAccessListsControlEntry
  WriteSuccessExactAccessListsReturnLoopEntry WriteSuccessExactAccessListsRegisterGroups
  WriteSuccessAccessListsSpec WriteSuccessStorageKeysSpec WriteSuccessExactAccessListsSpec
  WriteSuccessObservation WriteSuccessOutputSemantic.

Definition transactionAccessAfterDataCaller `{!islaG Sigma} `{!threadG}
    (sp x19 savedX22 count : bv 64) (base : Z) (entries : list writeSuccessAccessEntry)
    (bytes : list (bv 8)) (P : iProp Sigma) : iProp Sigma :=
  (accessRegisterGroup ["x3"; "x4"; "x7"; "x14"; "x15"; "x16"; "x17";
     "x28"; "x29"; "x30"; "x31"] ∗ "x19" ↦ᵣ RVal_Bits x19 ∗
   (bv_unsigned sp + 136) ↦ₘ savedX22 ∗ (bv_unsigned sp + 256) ↦ₘ Z_to_bv 64 base ∗
   (bv_unsigned sp + 1764) ↦ₘ? 20 ∗ writeSuccessStorageKeysScratch sp ∗
   base ↦ₘ∗ bytes ∗ writeSuccessAccessEntriesOwn entries ∗
   ⌜count = Z_to_bv 64 (Z.of_nat (length entries))⌝ ∗
   ⌜bytes = writeSuccessAccessEntriesBytes entries⌝ ∗
   ⌜length bytes = (40 * length entries)%nat⌝ ∗ ⌜(length entries < 2 ^ 64)%nat⌝ ∗
   ⌜bv_unsigned sp + 1896 < (machineRamEnd defaultMap)⌝ ∗
   ⌜entries <> [] -> (mapRamBase defaultMap) <= base⌝ ∗
   ⌜entries <> [] -> base + Z.of_nat (length bytes) < (machineRamEnd defaultMap)⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionAccessAfterDataCaller) := I.

Definition transactionAccessRetainedMemory `{!islaG Sigma} `{!threadG}
    (sp tag first second w2 data : bv 64) (last : bv 32) (bytes : list (bv 8))
    (P : iProp Sigma) : iProp Sigma :=
  ((bv_unsigned sp + 1640) ↦ₘ first ∗ (bv_unsigned sp + 1648) ↦ₘ second ∗
   (bv_unsigned sp + 1656) ↦ₘ last ∗ (bv_unsigned sp + 120) ↦ₘ tag ∗
   (bv_unsigned sp + 128) ↦ₘ w2 ∗ bv_unsigned data ↦ₘ∗ bytes ∗
   (bv_unsigned sp - 48) ↦ₘ? 32 ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionAccessRetainedMemory) := I.

Lemma transactions_data_to_access_entry `{!islaG Sigma} `{!threadG}
    (sp nonce gaslow gashigh feeTag feeLow feeHigh value tag first second w0 w1 w2 w3
      data size count x19 savedX22 : bv 64) (last : bv 32) dataBytes base entries accessBytes tail
    (P : iProp Sigma) :
  transactionAccessCountPost sp count
    (writeSuccessExactAccessListsEvents sp entries
      (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
        (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned savedX22))) tail))
    (transactionDataAccessFrame data size sp feeLow dataBytes
      (transactionValueDataSourceFrame sp w0 w1 w2 w3
        (transactionRecipientValueExitFrame sp tag first second last
          (transactionGasRecipientCarry sp gaslow gashigh feeTag feeHigh value nonce
            (transactionAccessAfterDataCaller sp x19 savedX22 count base entries accessBytes P))))) -∗
  accessListsControlState sp (Z_to_bv 64 (Z.of_nat (length entries))) (BV 64 8) (sp - BV 64 16)%bv
    (accessControlFrame sp base entries [] entries accessBytes nonce x19 savedX22 (sp - BV 64 16)%bv
      size feeTag (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
        (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned savedX22))) tail)
      (accessReturnRuntimeBounds sp
        (transactionAccessRetainedMemory sp tag first second w2 data last dataBytes P))).
Proof.
  iIntros "Hpost".
  iDestruct "Hpost" as "(Hsys & H1 & Hsp & H5 & H10 & H11 & Hupper & Hmmio & Htrace & HcountFrame & _)".
  iDestruct "HcountFrame" as "(Hcount & %HcountAlign & %HcountLow & %HcountHigh & Hdata & _)".
  iDestruct "Hdata" as "(H6 & H8 & H9 & H22 & HdataBytes & Hlower & %HdataAlign & %HdataLow & %HdataHigh & Hsource & _)".
  iDestruct "Hsource" as "(H12 & H13 & HvalueFrame & _)".
  iDestruct "HvalueFrame" as "(H18 & H20 & Hword2 & H21 & %HvalueAlign & %HvalueLow & %HvalueHigh & Hrecipient & _)".
  iPoseProof (transactions_recipient_exit_access_memory with "Hrecipient") as "Hmemory".
  iDestruct "Hmemory" as "(Hsrc0 & Hsrc1 & Hsrc2 & Htag & Hdestination & %Halign & %Hlow & %Hhigh & Hcarry & _)".
  iDestruct "Hcarry" as "(H26 & H27 & H23 & Hprice & _)".
  iDestruct "Hprice" as "(H24 & H25 & %HpriceAlign & %HpriceLow & %HpriceHigh & Hnonce & _)".
  iDestruct "Hnonce" as "(Hindex & %HnonceAlign & %HnonceLow & %HnonceHigh & Hcaller & _)".
  iDestruct "Hcaller" as "(Hother & H19 & Hsaved & Hbase & Hextra & Hkeys & HaccessBytes & Hown & %HcountEq & Hencoding & Hlength & Hbound & %HstackHigh & HbaseLow & HbaseHigh & HP & _)".
  iAssert ((bv_unsigned sp + 1744) ↦ₘ? 40)%I with "[Hdestination Hextra]" as "Hscratch".
  { iApply (mem_mapsto_uninit_combine 20 with "Hdestination"); first lia.
    replace (bv_unsigned sp + 1744 + 20)%Z with (bv_unsigned sp + 1764)%Z by lia. iExact "Hextra". }
  iAssert (reg_col writeSuccessAccessListsOtherRegShapes)%I
    with "[H1 H5 H6 H8 H9 H12 H13 H18 H20 H21 H23 H24 H25 H26 Hother]" as "Hregs".
  { iPoseProof (reg_col_shape_predicate with "H6") as "Hpredicate".
    iApply (reg_col_mixed_collect [("x1", BV 64 0x151d0); ("x5", BV 64 (mapIoContextAddress defaultMap));
      ("x8", data); ("x9", feeLow); ("x12", w2); ("x13", w3); ("x18", w0);
      ("x20", w1); ("x21", w3); ("x23", feeHigh); ("x24", gashigh); ("x25", gaslow); ("x26", value)]
      [(KindReg "x6", BitsShape 64)]
      ((fun r => (KindReg r, BitsShape 64)) <$>
        ["x3"; "x4"; "x7"; "x14"; "x15"; "x16"; "x17"; "x28"; "x29"; "x30"; "x31"])).
    - cbn [writeSuccessAccessListsOtherRegShapes writeSuccessAccessListsOtherRegisters fmap]. solve_Permutation.
    - iEval (unfold accessRegisterGroup) in "Hother". cbn. iFrame. }
  subst count. unfold accessListsControlState, accessControlFrame, accessControlScratch,
    accessReturnRuntimeBounds, transactionAccessRetainedMemory.
  iFrame. repeat iSplit; try done; iPureIntro; first [lia | bv_solve].
Qed.
Print Assumptions transactions_data_to_access_entry.
