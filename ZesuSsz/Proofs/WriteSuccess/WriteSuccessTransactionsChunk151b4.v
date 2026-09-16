Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import
  Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderBytesCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsValidFrame.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary1519c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary151b4.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary151c4.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Lemma write_success_transactions_chunk_151b4
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15c6c zesuEncoderBytesCallSpec -∗
  instr_body 0x151c4 (writeSuccessTransactionsAt151c4Spec P) -∗
  instr_body 0x151b4 (writeSuccessTransactionsAt151b4Spec P).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode #Hbytes Hnext".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve.
  all: repeat iIntros "?".
  all: li_unfold_lets_in_context; simpl; try liToSyntaxGoal.
  all: iDestruct select (base ↦ₘ∗ prefix ∗ _)%I as
    "(HbasePrefix & HbaseSuffix & Hprocessed & Htransaction & Hremaining &
      Hmmio & Htrace & HP & #Hinvariant & Hexit & _)".
  all: iPoseProof "Hinvariant" as "#HinvariantCopy".
  all: iDestruct "HinvariantCopy" as
    "(_ & _ & _ & _ & _ & _ & _ & _ & _ & %Halign & %Hmin & %Hmax & _)".
  all: have HmaxSp : (bv_unsigned sp < (machineRamEnd defaultMap))%Z by lia.
  all: iPoseProof (write_success_transactions_valid_frame transaction
    with "Htransaction") as "[%Hvalid Htransaction]".
  all: have HdataPointer :
      WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 192 =
      WriteSuccessTransactionsSpec.writeSuccessTransactionDataPointer transaction.
  { unfold WriteSuccessTransactionsSpec.writeSuccessTransactionValid in Hvalid.
    naive_solver. }
  all: have HdataLength :
      bv_unsigned
        (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 200) =
      Z.of_nat
        (length (WriteSuccessTransactionsSpec.writeSuccessTransactionData transaction)).
  { unfold WriteSuccessTransactionsSpec.writeSuccessTransactionValid in Hvalid.
    naive_solver. }
  all: have HdataSizeEq :
      (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 200 + 0)%bv =
      Z_to_bv 64
        (Z.of_nat
          (length (WriteSuccessTransactionsSpec.writeSuccessTransactionData transaction))).
  { apply bv_eq.
    rewrite bv_add_unsigned Z_to_bv_unsigned HdataLength.
    bv_solve. }
  all: have Hword200Zero :
      (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 200 + 0)%bv =
      WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 200.
  { apply bv_add_0_r. apply (bv_0_unsigned (n := 64)). }
  all: have HdataSize :
      WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 200 =
      Z_to_bv 64
        (Z.of_nat
          (length (WriteSuccessTransactionsSpec.writeSuccessTransactionData transaction))).
  { rewrite <- Hword200Zero. exact HdataSizeEq. }
  all: liARun.
  all: li_unfold_lets_in_context; simpl; try liToSyntaxGoal.
  all: try unLET.
  all: try rewrite HdataPointer.
  all: try rewrite bv_add_zero.
  all: try rewrite HdataLength.
  all: try (replace
    (WriteSuccessTransactionsSpec.writeSuccessTransactionDataPointer transaction + 0)%bv
      with (WriteSuccessTransactionsSpec.writeSuccessTransactionDataPointer transaction)
      by bv_solve).
  all: try (replace
    (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 200 + 0)%bv
      with (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 200)
      by bv_solve).
  all: try rewrite Hword200Zero.
  all: iExists
    (WriteSuccessTransactionsSpec.writeSuccessTransactionPhaseEvents
       WriteSuccessTransactionsSpec.TransactionAccessCount sp transaction
      (WriteSuccessTransactionsSpec.writeSuccessTransactionsEvents
         sp remaining tail),
      WriteSuccessTransactionsSpec.writeSuccessTransactionData transaction,
      tt)ₗ.
  all: cbn.
  all: try rewrite Hword200Zero.
  all: try rewrite HdataLength.
  all: try match goal with
    | |- context [bv_unsigned (bv_add ?e ?z)] =>
      have Hz : bv_unsigned ?z = 0%Z by bv_solve;
      rewrite (bv_add_0_r e z Hz)
    end.
  all: iEval (cbn [WriteSuccessTransactionsSpec.writeSuccessTransactionPhaseEvents]).
  all: iEval (rewrite <- HdataSize) in "Htrace".
  all: iFrame "Hmmio Htrace".
  all: iEval (unfold WriteSuccessTransactionsSpec.writeSuccessTransactionOwn)
    in "Htransaction".
  all: iDestruct "Htransaction" as
    "(HdataOwn & HaccessOwn & HaccessEntriesOwn & HblobOwn & HauthOwn &
      %HvalidKeep & _)".
  all: iRename select
    ("x18" ↦ᵣ _)%I into "H18".
  iAssert
      ((bv_unsigned
        (WriteSuccessTransactionsSpec.writeSuccessTransactionDataPointer transaction)
        ↦ₘ∗ WriteSuccessTransactionsSpec.writeSuccessTransactionData transaction) ∗
       match WriteSuccessTransactionsSpec.writeSuccessTransactionData transaction with
       | [] => True
       | _ :: _ =>
           ⌜(mapRamBase defaultMap) <=
             bv_unsigned
               (WriteSuccessTransactionsSpec.writeSuccessTransactionDataPointer
                  transaction)⌝ ∗
           ⌜bv_unsigned
               (WriteSuccessTransactionsSpec.writeSuccessTransactionDataPointer
                  transaction) +
             Z.of_nat
               (length
                  (WriteSuccessTransactionsSpec.writeSuccessTransactionData
                     transaction)) < (machineRamEnd defaultMap)⌝
       end)%I with "[HdataOwn]" as "(HdataArray & HdataBounds)".
  { destruct
      (WriteSuccessTransactionsSpec.writeSuccessTransactionData transaction)
      as [|datum dataTail] eqn:Hdata.
    - iEval (cbn [WriteSuccessTransactionsSpec.writeSuccessByteArrayOwn])
        in "HdataOwn".
      iSplitR.
      { rewrite mem_mapsto_array_eq /mem_mapsto_array_def.
        iExists 1%N.
        iSplit; [iPureIntro; lia|].
        iSplit; [iPureIntro; pose proof (bv_unsigned_in_range 64
          (WriteSuccessTransactionsSpec.writeSuccessTransactionDataPointer
            transaction)) as Hrange; unfold bv_modulus in Hrange; cbn in Hrange;
          cbn; rewrite Z.mul_0_r; split; lia|].
        done. }
      done.
    - iEval (unfold WriteSuccessTransactionsSpec.writeSuccessByteArrayOwn)
        in "HdataOwn".
      iDestruct "HdataOwn" as
        "(HdataMem & %HdataLower & %HdataUpper & _)".
      iSplitL "HdataMem".
      { iExact "HdataMem". }
      iSplitR.
      { iPureIntro; exact HdataLower. }
      iPureIntro; exact HdataUpper. }
  all: iRename select ((bv_unsigned sp - 48 + 48) ↦ₘ? 104)%I
    into "HupperRaw".
  all: iRename select
    ((∃ vact : valu,
        ⌜valu_has_shape vact (BitsShape 64)⌝ ∗ "x3" ↦ᵣ vact) ∗ _)%I
    into "HotherRaw".
  all: iDestruct "HotherRaw" as
    "(Hx3 & Hx4 & Hx7 & Hx12 & Hx13 & Hx14 & Hx15 & Hx16 & Hx17 &
      Hx28 & Hx29 & Hx30 & Hx31 & _)".
  all: iRename select ("x19" ↦ᵣ _)%I into "H19".
  all: iRename select ("x20" ↦ᵣ _)%I into "H20".
  all: iRename select ("x21" ↦ᵣ _)%I into "H21".
  all: iRename select ("x22" ↦ᵣ _)%I into "H22".
  all: iRename select ("x23" ↦ᵣ _)%I into "H23".
  all: iRename select ("x24" ↦ᵣ _)%I into "H24".
  all: iRename select ("x25" ↦ᵣ _)%I into "H25".
  all: iRename select ("x26" ↦ᵣ _)%I into "H26".
  all: iRename select ("x27" ↦ᵣ _)%I into "H27".
  all: iRename select ((bv_unsigned sp + 104) ↦ₘ _)%I into "H104".
  all: iRename select ((bv_unsigned sp + 112) ↦ₘ _)%I into "H112".
  all: iRename select ((bv_unsigned sp + 120) ↦ₘ _)%I into "H120".
  all: iRename select ((bv_unsigned sp + 128) ↦ₘ _)%I into "H128".
  all: iRename select ((bv_unsigned sp + 136) ↦ₘ _)%I into "H136".
  all: iRename select ((bv_unsigned sp + 144) ↦ₘ _)%I into "H144".
  all: iRename select ((bv_unsigned sp + 152) ↦ₘ _)%I into "H152".
  all: iRename select ((bv_unsigned sp + 160) ↦ₘ _)%I into "H160".
  all: iRename select ((bv_unsigned sp + 168) ↦ₘ _)%I into "H168".
  all: iRename select ((bv_unsigned sp + 176) ↦ₘ _)%I into "H176".
  all: iRename select ((bv_unsigned sp + 184) ↦ₘ _)%I into "H184".
  all: iRename select ((bv_unsigned sp + 192) ↦ₘ _)%I into "H192".
  all: iRename select ((bv_unsigned sp + 200) ↦ₘ _)%I into "H200".
  all: iRename select ((bv_unsigned sp + 208) ↦ₘ _)%I into "H208".
  all: iRename select ((bv_unsigned sp + 216) ↦ₘ _)%I into "H216".
  all: iRename select ((bv_unsigned sp + 224) ↦ₘ _)%I into "H224".
  all: iRename select ((bv_unsigned sp + 232) ↦ₘ _)%I into "H232".
  all: iRename select ((bv_unsigned sp + 240) ↦ₘ _)%I into "H240".
  all: iRename select ((bv_unsigned sp + 248) ↦ₘ _)%I into "H248".
  all: iRename select ((bv_unsigned sp + 256) ↦ₘ _)%I into "H256".
  all: iRename select ((bv_unsigned sp + 264) ↦ₘ _)%I into "H264".
  all: iRename select ((bv_unsigned sp + 272) ↦ₘ _)%I into "H272".
  all: iRename select ((bv_unsigned sp + 280) ↦ₘ? 1360)%I into "H280".
  all: iRename select ((bv_unsigned sp + 1640) ↦ₘ _)%I into "H1640".
  all: iRename select ((bv_unsigned sp + 1648) ↦ₘ _)%I into "H1648".
  all: iRename select ((bv_unsigned sp + 1656) ↦ₘ _)%I into "H1656".
  all: iRename select ((bv_unsigned sp + 1660) ↦ₘ? 4)%I into "H1660".
  all: iRename select ((bv_unsigned sp + 1664) ↦ₘ _)%I into "H1664".
  all: iRename select ((bv_unsigned sp + 1672) ↦ₘ _)%I into "H1672".
  all: iRename select ((bv_unsigned sp + 1680) ↦ₘ? 64)%I into "H1680".
  all: iRename select
    (match WriteSuccessTransactionsSpec.writeSuccessTransactionTo transaction with
     | None => _
     | Some _ => _
     end)%I into "HtoTail".
  all: iAssert
      (reg_col (delete 2%nat writeSuccessTransactions151c4OtherRegShapes) ∗
       "x18" ↦ᵣ RVal_Bits
         (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 48) ∗
       "x19" ↦ᵣ RVal_Bits
         (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 224) ∗
       "x20" ↦ᵣ RVal_Bits
         (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 56) ∗
       "x21" ↦ᵣ RVal_Bits
         (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 72) ∗
       "x22" ↦ᵣ RVal_Bits
         (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 200) ∗
       "x23" ↦ᵣ RVal_Bits
         (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 24) ∗
       "x24" ↦ᵣ RVal_Bits
         (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 8) ∗
       "x25" ↦ᵣ RVal_Bits
         (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 0) ∗
       "x26" ↦ᵣ RVal_Bits
         (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 184) ∗
       "x27" ↦ᵣ RVal_Bits
         (bv_zero_extend 64
           (WriteSuccessTransactionsSpec.writeSuccessTransactionByte transaction 32)) ∗
       ((bv_unsigned sp + 104) ↦ₘ Z_to_bv 64 base ∗
       (bv_unsigned sp + 112) ↦ₘ
         Z_to_bv 64 (Z.of_nat (length transactions)) ∗
       (bv_unsigned sp + 120) ↦ₘ
         bv_zero_extend 64
           (WriteSuccessTransactionsSpec.writeSuccessTransactionByte transaction 285) ∗
       (bv_unsigned sp + 128) ↦ₘ
         WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 64 ∗
       (bv_unsigned sp + 136) ↦ₘ
         WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 232 ∗
       (bv_unsigned sp + 144) ↦ₘ
         WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 88 ∗
       (bv_unsigned sp + 152) ↦ₘ
         WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 80 ∗
       (bv_unsigned sp + 160) ↦ₘ
         WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 248 ∗
       (bv_unsigned sp + 168) ↦ₘ
         WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 240 ∗
       (bv_unsigned sp + 176) ↦ₘ
         WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 256 ∗
       (bv_unsigned sp + 184) ↦ₘ
         WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 120 ∗
       (bv_unsigned sp + 192) ↦ₘ
         WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 112 ∗
       (bv_unsigned sp + 200) ↦ₘ
         WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 104 ∗
       (bv_unsigned sp + 208) ↦ₘ
         WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 128 ∗
       (bv_unsigned sp + 216) ↦ₘ
         WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 96 ∗
       (bv_unsigned sp + 224) ↦ₘ
         WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 152 ∗
       (bv_unsigned sp + 232) ↦ₘ
         WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 144 ∗
       (bv_unsigned sp + 240) ↦ₘ
         WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 136 ∗
       (bv_unsigned sp + 248) ↦ₘ
         Z_to_bv 64 (Z.of_nat (length processed)) ∗
       (bv_unsigned sp + 256) ↦ₘ
         WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 208 ∗
       (bv_unsigned sp + 264) ↦ₘ
         WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 216 ∗
       (bv_unsigned sp + 272) ↦ₘ
         WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 176 ∗
       (bv_unsigned sp + 280) ↦ₘ? 1360 ∗
       (bv_unsigned sp + 1640) ↦ₘ
         WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 265 ∗
       (bv_unsigned sp + 1648) ↦ₘ
         WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 273 ∗
       (bv_unsigned sp + 1656) ↦ₘ
         bv_extract 0 32
           (bv_or
             (bv_or
               (bv_shiftl
                 (bv_zero_extend 64
                   (WriteSuccessTransactionsSpec.writeSuccessTransactionByte transaction 284))
                 (BV 64 24))
               (bv_shiftl
                 (bv_zero_extend 64
                   (WriteSuccessTransactionsSpec.writeSuccessTransactionByte transaction 283))
                 (BV 64 16)))
             (bv_or
               (bv_shiftl
                 (bv_zero_extend 64
                   (WriteSuccessTransactionsSpec.writeSuccessTransactionByte transaction 282))
                 (BV 64 8))
               (bv_zero_extend 64
                 (WriteSuccessTransactionsSpec.writeSuccessTransactionByte transaction 281)))) ∗
       (bv_unsigned sp + 1660) ↦ₘ? 4 ∗
       (bv_unsigned sp + 1664) ↦ₘ
         WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 160 ∗
       (bv_unsigned sp + 1672) ↦ₘ
         WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 168 ∗
       (bv_unsigned sp + 1680) ↦ₘ? 64 ∗
       match WriteSuccessTransactionsSpec.writeSuccessTransactionTo transaction with
       | None =>
           (bv_unsigned sp + 1744) ↦ₘ
             WriteSuccessTransactionsSpec.writeSuccessTransactionByte transaction 264 ∗
           (bv_unsigned sp + 1745) ↦ₘ? 151
       | Some _ =>
           (bv_unsigned sp + 1744) ↦ₘ
             WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 265 ∗
           (bv_unsigned sp + 1752) ↦ₘ
             WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 273 ∗
           (bv_unsigned sp + 1760) ↦ₘ
             bv_extract 0 32
               (bv_sign_extend 64
                (bv_extract 0 32
                 (bv_or
                 (bv_or
                   (bv_shiftl
                     (bv_zero_extend 64
                       (WriteSuccessTransactionsSpec.writeSuccessTransactionByte transaction 284))
                     (BV 64 24))
                   (bv_shiftl
                     (bv_zero_extend 64
                       (WriteSuccessTransactionsSpec.writeSuccessTransactionByte transaction 283))
                     (BV 64 16)))
                 (bv_or
                   (bv_shiftl
                     (bv_zero_extend 64
                       (WriteSuccessTransactionsSpec.writeSuccessTransactionByte transaction 282))
                     (BV 64 8))
                   (bv_zero_extend 64
                     (WriteSuccessTransactionsSpec.writeSuccessTransactionByte transaction 281)))))) ∗
           (bv_unsigned sp + 1764) ↦ₘ? 132
       end ∗ True))%I
    with "[Hx3 Hx4 Hx7 Hx12 Hx13 Hx14 Hx15 Hx16 Hx17 Hx28 Hx29 Hx30 Hx31
      H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H104 H112 H120 H128 H136 H144
      H152 H160 H168 H176 H184 H192 H200 H208 H216 H224 H232 H240 H248 H256
      H264 H272 H280 H1640 H1648 H1656 H1660 H1664 H1672 H1680 HtoTail]"
    as "Hhidden".
  { rewrite /reg_col. cbn.
    iFrame "Hx3 Hx4 Hx7 Hx12 Hx13 Hx14 Hx15 Hx16 Hx17 Hx28 Hx29 Hx30 Hx31
      H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H104 H112 H120 H128 H136 H144
      H152 H160 H168 H176 H184 H192 H200 H208 H216 H224 H232 H240 H248 H256
      H264 H272 H280 H1640 H1648 H1656 H1660 H1664 H1672 H1680 HtoTail". }
  iAssert
      (base ↦ₘ∗ prefix ∗
       (base + 288 * length processed) ↦ₘ∗ suffix ∗
       WriteSuccessTransactionsSpec.writeSuccessTransactionsProcessedOwn processed ∗
       WriteSuccessTransactionsSpec.writeSuccessTransactionsOwn remaining ∗
       P ∗
       instr_pre WriteSuccessTransactionsSpec.writeSuccessTransactionsLoopExitAddress
         (WriteSuccessTransactionsSpec.writeSuccessTransactionsLoopExit
            sp base transactions bytes tail P))%I
    with "[HbasePrefix HbaseSuffix Hprocessed Hremaining HP Hexit]" as "Houter".
  { iFrame. }
  iAssert
      (match WriteSuccessTransactionsSpec.writeSuccessTransactionData transaction with
       | [] => True
       | _ :: _ =>
           ⌜(mapRamBase defaultMap) <=
             bv_unsigned
               (WriteSuccessTransactionsSpec.writeSuccessTransactionDataPointer
                  transaction)⌝ ∗
           ⌜bv_unsigned
               (WriteSuccessTransactionsSpec.writeSuccessTransactionDataPointer
                  transaction) +
             Z.of_nat
               (length
                  (WriteSuccessTransactionsSpec.writeSuccessTransactionData
                     transaction)) < (machineRamEnd defaultMap)⌝
       end ∗
       WriteSuccessTransactionsSpec.writeSuccessByteArrayOwn
         (WriteSuccessTransactionsSpec.writeSuccessTransactionAccessPointer transaction)
         (WriteSuccessTransactionsSpec.writeSuccessTransactionAccessBytes transaction) ∗
       WriteSuccessAccessListsSpec.writeSuccessAccessEntriesOwn
         (WriteSuccessTransactionsSpec.writeSuccessTransactionAccessEntries transaction) ∗
       WriteSuccessTransactionsSpec.writeSuccessByteArrayOwn
         (WriteSuccessTransactionsSpec.writeSuccessTransactionBlobPointer transaction)
         (WriteSuccessTransactionsSpec.writeSuccessTransactionBlobBytes transaction) ∗
       WriteSuccessTransactionsSpec.writeSuccessByteArrayOwn
         (WriteSuccessTransactionsSpec.writeSuccessTransactionAuthorizationPointer transaction)
         (WriteSuccessTransactionsSpec.writeSuccessTransactionAuthorizationBytes transaction))%I
    with "[HdataBounds HaccessOwn HaccessEntriesOwn HblobOwn HauthOwn]"
    as "HtransactionRest".
  { iFrame. }
  iFrame "HdataArray".
  iSplitR "Hnext HupperRaw Houter HtransactionRest Hhidden".
  { iPureIntro; reflexivity. }
  iSplitR "Hnext HupperRaw Houter HtransactionRest Hhidden".
  { iPureIntro; exact Halign. }
  iSplitR "Hnext HupperRaw Houter HtransactionRest Hhidden".
  { iPureIntro; exact Hmin. }
  iSplitR "Hnext HupperRaw Houter HtransactionRest Hhidden".
  { iPureIntro; exact HmaxSp. }
  iSplitR "Hnext HupperRaw Houter HtransactionRest Hhidden".
  { iPureIntro; lia. }
  iSplitR "Hnext HupperRaw Houter HtransactionRest Hhidden".
  { iPureIntro; bv_solve. }
  iSplitR "Hnext HupperRaw Houter HtransactionRest Hhidden".
  { iPureIntro; bv_solve. }
  iSplitR "Hnext HupperRaw Houter HtransactionRest Hhidden".
  { iPureIntro; bv_solve. }
  iSplitL "Hnext HupperRaw Houter HtransactionRest Hhidden"; [|done].
  iApply (instr_pre_wand 0x151c4 0x151c4 false true with "Hnext");
    [done | done |].
  iIntros "Hpost".
  iDestruct "Hpost" as
    "(Hsys & H1 & H2 & H5 & H6 & H8 & H9 & H10 & H11 & Hstack &
      HdataPost & Hmmio & Htrace & HtailPost)".
  all: iDestruct "HtransactionRest" as
    "(HdataBounds & HaccessOwn & HaccessEntriesOwn & HblobOwn & HauthOwn)".
  all: iAssert
      (⌜WriteSuccessTransactionsSpec.writeSuccessTransactionValid transaction⌝)%I
      with "[]" as "HvalidKeep".
  { iPureIntro; exact Hvalid. }
  iAssert (reg_col zesu_ram_sys_regs)%I with "[Hsys]" as "HsysPacked".
  { rewrite /reg_col; iFrame;
    repeat iSplit; try iPureIntro; try reflexivity; try assumption; try done. }
  iDestruct (mem_mapsto_uninit_split 32 with "Hstack") as
    "[Hlower HstackRest]"; [lia|].
  have HstackAddress : bv_unsigned sp - 48 + 32 = bv_unsigned sp - 16 by lia.
  iEval (rewrite HstackAddress) in "HstackRest".
  have HupperAddress : bv_unsigned sp - 48 + 48 = bv_unsigned sp by lia.
  iEval (rewrite HupperAddress) in "HupperRaw".
  iRename "HupperRaw" into "Hupper".
  iAssert ((bv_unsigned sp - 48) ↦ₘ? 48)%I
    with "[Hlower HstackRest]" as "Hlower48".
  { iApply (mem_mapsto_uninit_combine 32 with "Hlower"); first lia.
    have -> : bv_unsigned sp - 48 + 32 = bv_unsigned sp - 16 by lia.
    iExact "HstackRest". }
  all: iAssert ((bv_unsigned sp - 48) ↦ₘ? 152)%I
    with "[Hlower48 Hupper]" as "HscratchPrefix".
  { iApply (mem_mapsto_uninit_combine 48 with "Hlower48"); first lia.
    have -> : bv_unsigned sp - 48 + 48 = bv_unsigned sp by lia.
    iExact "Hupper". }
  all: iAssert ("x1" ↦ᵣ RVal_Bits (BV 64 0x151c4))%I
    with "[H1]" as "H1target".
  { replace (BV 64 0x151c4) with (Z_to_bv 64 (0x151c0 + 4)) by bv_solve.
    iExact "H1". }
  all: iAssert ("x8" ↦ᵣ RVal_Bits
      (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 192))%I
    with "[H8]" as "H8target".
  { rewrite HdataPointer. iExact "H8". }
  all: iAssert ("x10" ↦ᵣ RVal_Bits
      (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 192))%I
    with "[H10]" as "H10target".
  { rewrite HdataPointer. iExact "H10". }
  all: iAssert ("x11" ↦ᵣ RVal_Bits
      (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 200))%I
    with "[H11]" as "H11target".
  { rewrite HdataSize. iExact "H11". }
  all: iAssert (WriteSuccessTransactionsSpec.writeSuccessTransactionOwn transaction)
    with "[HdataPost HdataBounds HaccessOwn HaccessEntriesOwn HblobOwn HauthOwn
      HvalidKeep]" as "HtransactionRestore".
  { rewrite /WriteSuccessTransactionsSpec.writeSuccessTransactionOwn
      /WriteSuccessTransactionsSpec.writeSuccessByteArrayOwn.
    destruct
      (WriteSuccessTransactionsSpec.writeSuccessTransactionData transaction)
      as [|datum dataTail] eqn:Hdata.
    - cbn. iFrame "HaccessOwn HaccessEntriesOwn HblobOwn HauthOwn HvalidKeep".
    - cbn.
      iDestruct "HdataBounds" as "(%HdataLower & %HdataUpper)".
      iFrame "HdataPost HaccessOwn HaccessEntriesOwn HblobOwn HauthOwn
        HvalidKeep".
      iSplit.
      + iPureIntro; exact HdataLower.
      + iSplit; [iPureIntro; exact HdataUpper | done]. }
  all: iDestruct "Hhidden" as
    "(HotherNo6 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27 &
      HscratchTail)".
  all: iAssert (reg_col writeSuccessTransactions151c4OtherRegShapes)%I
    with "[H6 HotherNo6]" as "HotherPacked".
  { iEval (rewrite /reg_col) in "HotherNo6".
    iEval (cbn) in "HotherNo6".
    iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "H6".
    iDestruct "H6" as (v6) "(H6map & %H6shape)".
    iDestruct "HotherNo6" as
      "(Hx3 & Hx4 & Hx7 & Hx12 & Hx13 & Hx14 & Hx15 & Hx16 & Hx17 &
        Hx28 & Hx29 & Hx30 & Hx31 & _)".
    rewrite /reg_col; cbn; iFrame "Hx3 Hx4 Hx7 Hx12 Hx13 Hx14 Hx15 Hx16
      Hx17 Hx28 Hx29 Hx30 Hx31".
    iExists v6; iSplit; [iPureIntro; exact H6shape | iExact "H6map"]. }
  all: iAssert
      (writeSuccessTransactionsScratch1519c
        sp base transactions processed transaction)%I
      with "[HscratchPrefix HscratchTail]" as "HscratchFull".
  { rewrite /writeSuccessTransactionsScratch1519c. iFrame. }
  all: iDestruct "Houter" as
    "(HbasePrefix & HbaseSuffix & Hprocessed & Hremaining & HP & Hexit)".
  all: iExists sp, base, transaction, transactions, processed, remaining,
    bytes, prefix, suffix, tail.
  all: iFrame "HsysPacked HotherPacked H1target H2 H5 H8target H10target H11target HscratchFull
    HbasePrefix HbaseSuffix Hprocessed HtransactionRestore Hremaining Hmmio Htrace
    HP Hinvariant Hexit H18 H19 H20 H21 H22 H23 H24 H25 H26 H27".
  all: iFrame.
  all: repeat iSplit; iPureIntro; try assumption; try bv_solve; lia.
  Unshelve. all: prepare_sidecond.
  all: try bv_solve.
  all: try lia.
  Unshelve.
  all: try exact Halign.
  all: try exact Hmin.
  all: try exact Hmax.
Qed.
