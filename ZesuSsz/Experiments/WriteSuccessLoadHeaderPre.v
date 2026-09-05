From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccessCalls.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderBytesCall.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderIntCall.
Require Import ZesuSsz.Experiments.WriteSuccessHeaderSpec.
Require Import ZesuSsz.Experiments.WriteSuccessLoadHeader.
Require Import ZesuSsz.Experiments.WriteSuccessToLoadWithFrame.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Experiments.WriteSuccessValueBlock.
Require Import ZesuSsz.Experiments.WriteSuccessValueTransactionsEntry.

Lemma write_success_load_header_pre
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
  □ instr_pre 0x14d80
    (writeSuccessAtLoadHeaderWithFrame sp sourceBytes
      (writeSuccessHeaderEvents sp
        (writeSuccessValueEvents sp values
          (writeSuccessTransactionsEvents sp transactions tail)))
      (writeSuccessLoadHeaderRemainder P sp sourceBytes values payload tail base
        transactions transactionBytes)).
Proof.
  iStartProof.
  iIntros "#Hlookup #Hcode #Hmemcpy #Houtput #Hbytes #Hint #Hloop".
  iPoseProof (write_success_load_header P sp sourceBytes values payload tail
    base transactions transactionBytes with
    "Hlookup Hcode Hmemcpy Houtput Hbytes Hint Hloop") as "Hheader".
  iModIntro. iApply instr_pre_to_body. iNext.
  iApply (instr_pre_wand 0x14d80 0x14d80 false false with "Hheader");
    [done | reflexivity |].
  iIntros "HatLoad".
  iApply (write_success_at_load_header_with_frame_to_header P sp sourceBytes
    values payload tail base transactions transactionBytes with "HatLoad").
Qed.
