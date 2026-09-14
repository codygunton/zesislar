Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCalls.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderBytesCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderIntCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessHeaderBlock.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessHeaderSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSemanticAdapter.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessValueBlock.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessValueTransactionsEntry.

Definition writeSuccessHeaderValueTransactionsSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (sourceBytes : list (bv 8))
    (values : list (bv 64)) (payload : list (bv 8))
    (tail : spec) (base : Z) (transactions : list writeSuccessTransaction)
    (transactionBytes : list (bv 8)) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ reg_col writeSuccessHeaderRegShapes ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   (bv_unsigned sp + 104) ↦ₘ? 16 ∗
   (bv_unsigned sp + 312) ↦ₘ∗ sourceBytes ∗
   (bv_unsigned sp + 1032) ↦ₘ? 864 ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace
     (writeSuccessHeaderEvents sp
       (writeSuccessValueEvents sp values
         (writeSuccessTransactionsEvents sp transactions tail))) ∗
   writeSuccessHeaderValueProviderResources P sp sourceBytes values payload tail
     base transactions transactionBytes ∗ True)%I.

Global Instance : LithiumUnfold
    (@writeSuccessHeaderValueTransactionsSpec) := I.

Lemma write_success_header_value_transactions
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (sourceBytes : list (bv 8))
    (values : list (bv 64)) (payload : list (bv 8))
    (tail : spec) (base : Z) (transactions : list writeSuccessTransaction)
    (transactionBytes : list (bv 8)) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x101d4 zesuMemcpyCallSpec -∗
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  □ instr_pre 0x15c6c zesuEncoderBytesCallSpec -∗
  □ instr_pre 0x15d10 zesuEncoderIntCallSpec -∗
  □ instr_pre 0x14f04
    (writeSuccessTransactionsLoopSpec
      (writeSuccessValueTransactionsContinuation values payload P)) -∗
  instr_body 0x14e00
    (writeSuccessHeaderValueTransactionsSpec P sp sourceBytes values payload tail
      base transactions transactionBytes).
Proof.
  iStartProof.
  iIntros "#Hlookup #Hcode #Hmemcpy #Houtput #Hbytes #Hint #Hloop".
  iPoseProof (write_success_transactions_semantic_adapter_pre
    (writeSuccessValuePost sp values payload
      (writeSuccessTransactionsEvents sp transactions tail)
      (writeSuccessValueTransactionsProviderFrame P sp values payload tail base
        transactions sourceBytes transactionBytes))
    (writeSuccessValueTransactionsContinuation values payload P)
    with "[] Hloop") as "#Htransactions".
  { iModIntro.
    rewrite /writeSuccessTransactionsSemanticAdapter.
    iIntros "Hpost".
    iApply write_success_value_transactions_entry_adapter.
    iApply write_success_value_transactions_provider.
    iExact "Hpost". }
  iPoseProof (write_success_value_block
    (writeSuccessValueTransactionsProviderFrame P sp values payload tail base
      transactions sourceBytes transactionBytes)
    with "Hlookup Hcode Houtput Hint Hbytes") as "Hvalue".
  iAssert (□ instr_pre 0x14e88
    (writeSuccessHeaderPost sp sourceBytes
      (writeSuccessValueEvents sp values
        (writeSuccessTransactionsEvents sp transactions tail))
      (writeSuccessHeaderValueProviderFrame P sp sourceBytes values payload tail
        base transactions transactionBytes)))%I as "#HvaluePre".
  { iModIntro.
    iApply instr_pre_to_body. iNext.
    iApply (instr_pre_wand 0x14e88 0x14e88 false false with "Hvalue");
      [done | reflexivity |].
    iIntros "Hpost".
    iApply write_success_header_value_transactions_provider.
    iExact "Hpost". }
  iPoseProof (write_success_header_block
    (writeSuccessHeaderValueProviderFrame P sp sourceBytes values payload tail
      base transactions transactionBytes)
    with "Hlookup Hcode Hmemcpy Houtput") as "Hheader".
  iApply (instr_pre_wand 0x14e00 0x14e00 false false with "Hheader");
    [done | reflexivity |].
  iIntros "Hentry".
  iEval (rewrite /writeSuccessHeaderValueTransactionsSpec) in "Hentry".
  iDestruct "Hentry" as
    "(Hsys & Hother & H2 & Hfields & Hsource & Hdestination & Hmmio &
      Htrace & Hresources & _)".
  iEval (rewrite /writeSuccessHeaderValueProviderResources) in "Hresources".
  iDestruct "Hresources" as
    "(Hlower & Hgap104 & Hgap192 & Hpayload & Harray & Hown & Hexit &
      Hinvariant & %HsourceLength & %HvaluesBytes & %HvaluesLength &
      %HpayloadLength & %HbaseEq & %HcountEq & %Halign16 & %Halign8 &
      %HlowerBound & %HupperBound & HP & _)".
  rewrite /writeSuccessHeaderSpec /writeSuccessHeaderBeforeCopySpec.
  iExists sp, sourceBytes,
    (writeSuccessValueEvents sp values
      (writeSuccessTransactionsEvents sp transactions tail)).
  iFrame "Hsys Hother H2 Hfields Hsource Hdestination Hmmio Htrace".
  iSplit; [iPureIntro; exact HsourceLength |].
  iSplit; [iPureIntro; exact Halign16 |].
  iSplit; [iPureIntro; lia |].
  iSplit; [iPureIntro; exact HupperBound |].
  rewrite /writeSuccessHeaderValueProviderFrame
    /writeSuccessHeaderValueProviderResources.
  iFrame "Htransactions HvaluePre Hlower Hgap104 Hgap192 Hpayload Harray Hown
    Hexit Hinvariant HP".
  repeat iSplit; try iPureIntro; try assumption; done.
Qed.
