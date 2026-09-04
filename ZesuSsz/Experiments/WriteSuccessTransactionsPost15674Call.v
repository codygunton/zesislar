From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
From IslaTraces.write_success_87 Require Import a15674_spec.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Experiments.WriteSuccessByteLists.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPost15674Boundary.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Lemma write_success_transactions_post_15674_call
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15c10 zesuEncoderByteListsCallSpec -∗
  instr_body 0x15674
    (writeSuccessTransactionsPost15674CallEntrySpec P).
Proof.
  iStartProof. iIntros "#Hlookup #Hcode #Hcallee".
  iPoseProof "Hlookup" as "#Hlookup15674".
  iEval (rewrite /instr_lookup_resources) in "Hlookup15674".
  iPoseProof ("Hlookup15674" $! 0x15674 with "[]") as "#Hinstr15674".
  { iPureIntro.
    rewrite IslaTraces.write_success_blocks.Index.lookup_a15674.
    done. }
  iPoseProof (IslaTraces.write_success_87.a15674_spec.a15674_spec
    0x15674 with "Hinstr15674") as "Hjalr".
  rewrite instr_pre'_eq. iIntros "Hentry".
  iEval (rewrite /writeSuccessTransactionsPost15674CallEntrySpec) in "Hentry".
  iDestruct "Hentry" as
    (sp base transactions bytes tail first second items saved)
    "(Hsys & Hcaller & Hsaved & HreturnOther & H1 & H2 & H10 & H11 &
      HbaseWord & HlengthWord & HscratchPrefix & HscratchFirst & HscratchSecond &
      HscratchSuffix & Hbase & Hown & Hitems & Hfacts & Hstack & Hmmio &
      Htrace & HP & _)".
  iApply "Hjalr".
  rewrite /InstrSpecs.Specs.zesu_jalr_same_spec.
  iExists (BV 64 0x15670). iFrame "Hsys H1".
  iSplit; first (iPureIntro; bv_solve).
  have Htarget :
      bv_unsigned
        (bv_or (bv_and ((BV 64 0x15670) + BV 64 1440)%bv
          (BV 64 18446744073709551614)) (BV 64 0)) = 0x15c10
    by native_compute.
  rewrite Htarget.
  iApply (instr_pre_wand 0x15c10 0x15c10 true true with "Hcallee");
    [done | reflexivity |].
  iIntros "Hcall".
  iEval (unfold zesuEncoderByteListsCallSpec, zesu_c_call) in "Hcall".
  iExists sp, (BV 64 0x15678).
  iDestruct "Hcall" as "(HcallSys & HcallTmp & HcallRest)".
  iFrame "HcallSys".
Qed.
