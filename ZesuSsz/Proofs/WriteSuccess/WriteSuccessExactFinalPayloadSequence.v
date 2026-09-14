Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import WriteSuccessByteLists.
Require Import ZesuSsz.Contracts.IslarisMachine.
From iris.proofmode Require Import environments.
From IslaTraces.write_success_blocks Require Import Index.
From ZesuSsz.Proofs.WriteSuccess Require Import WriteSuccessExactFinalByteListCall.
Open Scope Z_scope.
From ZesuSsz.Proofs.WriteSuccess Require Import WriteSuccessExactFinalPayloadSetup
  WriteSuccessExactFinalPayloadCall WriteSuccessExactFinalByteListCall WriteSuccessNativeCode WriteSuccessExactPrefixCalls
  WriteSuccessEpilogueBlock.
Definition writeSuccessExactFinalPayloadSequenceEntry `{!islaG Sigma} `{!threadG}
    (savedReturn : bv 64) (Q : iProp Sigma) : iProp Sigma :=
  (∃ (sp pointer count : bv 64) (items : list ByteListItem) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    "x2" ↦ᵣ RVal_Bits sp ∗ "x8" ↦ᵣ RVal_Bits pointer ∗
    "x10" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    "x11" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
    ⌜mapRamBase defaultMap <= bv_unsigned sp + 88 < machineRamEnd defaultMap⌝ ∗
    writeSuccessExactFinalPayloadCallEntryFrame sp pointer count items tail savedReturn
      ((bv_unsigned sp + 88) ↦ₘ count ∗ Q))%I.
Global Instance : LithiumUnfold (@writeSuccessExactFinalPayloadSequenceEntry) := I.
Lemma write_success_exact_final_payload_sequence `{!islaG Sigma} `{!threadG}
    (savedReturn : bv 64) (Q : iProp Sigma) :
  ⊢ (writeSuccessCompleteNativeCode -∗
    instr_body 0x159c8 (writeSuccessExactFinalPayloadSequenceEntry savedReturn Q))%I.
Proof.
  iIntros "#Hnative".
  iPoseProof (exact_prefix_calls with "Hnative") as "(#Hcopy & #Houtput & #Hint & #Hbytes)".
  iEval (unfold writeSuccessCompleteNativeCode) in "Hnative".
  iDestruct "Hnative" as "#(H00 & Hlookup & Hmain & HoutCode & HcopyCode & HboolCode & HoptCode & Hlists & HbytesCode & HintCode & Hu256 & Hu128)".
  iAssert (∀ (sp count : bv 64), instr_body 0x159d4
    (writeSuccessExactPost159d4PayloadCallEntrySpec savedReturn ((bv_unsigned sp + 88) ↦ₘ count ∗ Q)))%I
    with "[]" as "#Hcall".
  { iIntros (sp count).
    iApply (write_success_exact_post_159d4_payload_byte_lists_call with "Hlookup Hmain Hlists Hint Hbytes []").
    iIntros (sp0 pointer0 items0 tail0).
    iApply (write_success_epilogue_block with "Hlookup"). }
  iPoseProof (write_success_exact_final_payload_setup_correct savedReturn Q with "Hlookup") as "Hsetup".
  iApply (instr_pre_wand 0x159c8 0x159c8 false false with "Hsetup"); [done | reflexivity |].
  iIntros "Hentry".
  iEval (unfold writeSuccessExactFinalPayloadSequenceEntry) in "Hentry".
  iDestruct "Hentry" as (sp pointer count items tail)
    "(Hsys & H1 & H2 & H8 & H10 & H11 & Halign & Hrange & Hframe)".
  rewrite /writeSuccessExactFinalPayloadSetupEntry.
  iExists sp, pointer, count, items, tail.
  iFrame "Hsys H1 H2 H8 H10 H11 Halign Hrange Hframe".
  iApply instr_pre_to_body. iNext.
  iApply "Hcall".
Qed.
Print Assumptions write_success_exact_final_payload_sequence.
