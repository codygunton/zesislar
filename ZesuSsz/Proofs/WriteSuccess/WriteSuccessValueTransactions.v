From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import InstrSpecs.Specs.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesLoop.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCalls.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderBooleanCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderBytesCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderIntCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderInt1645Call.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderOptionalU64Call.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderU256.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessHeaderSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOuterDispatcher.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsAuthorizationsAnyLoop.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsLoop.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsValueAdapter.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessValueBlock.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Definition writeSuccessValueExitAdapter
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∀ (sp : bv 64) (values : list (bv 64)) (payload : list (bv 8))
      (tail : spec),
    □ instr_pre 0x15668 (writeSuccessValuePost sp values payload tail P))%I.

Definition writeSuccessValueReadySpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (values : list (bv 64)) (payload : list (bv 8))
      (tail : spec),
    reg_col zesu_ram_sys_regs ∗ reg_col writeSuccessHeaderRegShapes ∗
    "x2" ↦ᵣ RVal_Bits sp ∗ (bv_unsigned sp - 48) ↦ₘ? 48 ∗
    (bv_unsigned sp + 104) ↦ₘ? 16 ∗
    (bv_unsigned sp + 1032) ↦ₘ∗ values ∗
    bv_unsigned (writeSuccessValueWord values 4) ↦ₘ∗ payload ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace (writeSuccessValueEvents sp values tail) ∗
    ⌜length values = 74%nat⌝ ∗
    ⌜bv_unsigned (writeSuccessValueWord values 5) = length payload⌝ ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned sp - 48⌝ ∗
    ⌜bv_unsigned sp + 1896 < 0x40000000⌝ ∗ P)%I.

Global Instance : LithiumUnfold (@writeSuccessValueReadySpec) := I.

Lemma write_success_value_transactions
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x101d4 zesuMemcpyCallSpec -∗
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  □ instr_pre 0x15b9c zesuEncoderBooleanCallSpec -∗
  □ instr_pre 0x15bc8 zesuEncoderOptionalU64CallSpec -∗
  □ instr_pre 0x15c6c zesuEncoderBytesCallSpec -∗
  □ instr_pre 0x15cb0 zesuEncoderU256CallSpec -∗
  □ instr_pre 0x15ce4 zesuEncoderInt1645CallSpec -∗
  □ instr_pre 0x15d10 zesuEncoderIntCallSpec -∗
  □ writeSuccessTransactionsValueAdapter P -∗
  □ writeSuccessValueExitAdapter P -∗
  instr_body 0x14e88 (writeSuccessValueReadySpec P).
Proof.
  iStartProof.
  iIntros "#Hlookup #Hcode #Hmemcpy #Houtput #Hboolean #Hoptional #Hbytes
    #Hu256 #Hint128 #Hint64 #HvalueAdapter #HexitAdapter".
  iPoseProof (write_success_blob_hashes_loop_pre P with
    "Hlookup Hcode Houtput") as "#Hblob".
  iPoseProof (write_success_transactions_authorizations_any_loop_pre P with
    "Hlookup Hcode Hmemcpy Hu256 Hint64 Houtput") as "#Hauth".
  iPoseProof (write_success_transactions_loop_pre P with
    "Hlookup Hcode Hmemcpy Houtput Hblob Hauth Hboolean Hoptional Hbytes
     Hu256 Hint128 Hint64") as "#Hloop".
  iPoseProof (write_success_value_block P with
    "Hlookup Hcode Houtput Hint64 Hbytes") as "Hvalue".
  iApply (instr_pre_wand 0x14e88 0x14e88 false false with "Hvalue");
    [done | reflexivity |].
  iIntros "Hentry".
  iEval (rewrite /writeSuccessValueReadySpec) in "Hentry".
  iDestruct "Hentry" as (sp values payload tail)
    "(Hsys & Hother & H2 & Hlow & Hfields & Hvalues & Hpayload & Hmmio &
      Htrace & %Hlength & %HpayloadLength & %Halign16 & %Halign8 & %Hlower &
      %Hupper & HP)".
  iEval (rewrite /writeSuccessValueSpec).
  iExists sp, values, payload, tail.
  iFrame "Hsys Hother H2 Hlow Hfields Hvalues Hpayload Hmmio Htrace HP".
  repeat iSplit; try iPureIntro; try assumption.
  iEval (rewrite /writeSuccessValueExitAdapter) in "HexitAdapter".
  iPoseProof ("HexitAdapter" $! sp values payload tail) as "#Hexit".
  iApply (write_success_outer_dispatcher_pre P sp values payload tail with
    "Hlookup HvalueAdapter Hloop Hexit").
Qed.
