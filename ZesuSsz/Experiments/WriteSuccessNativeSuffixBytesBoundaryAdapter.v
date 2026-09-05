From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessNativeSuffixBytes15920.
Require Import ZesuSsz.Experiments.WriteSuccessNativeSuffixBytesCompose.

Import ListNotations.

(** The aggregate exit keeps all five descriptor resources.  The old
    0x15930 suffix contract exposes descriptor five in registers and keeps
    descriptors one through four in its continuation frame. *)
Definition writeSuccessSuffixBytesAggregateExitAt15930
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp d1 s1 d2 s2 d3 s3 d4 s4 d5 s5 oldS0 oldS1 : bv 64)
      (b1 b2 b3 b4 b5 : list (bv 8)) (tail : spec),
    writeSuccessSuffixAt15930
      (writeSuccessSuffixBytesP5 sp d1 s1 d2 s2 d3 s3 d4 s4 d5 s5
        b1 b2 b3 b4 b5 P))%I.

Global Instance : LithiumUnfold
  (@writeSuccessSuffixBytesAggregateExitAt15930) := I.

Lemma write_success_suffix_bytes_aggregate_exit_to_15930
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  writeSuccessSuffixBytesAggregateExit P -∗
  writeSuccessSuffixBytesAggregateExitAt15930 P.
Proof.
  iIntros "Hexit".
  iEval (rewrite /writeSuccessSuffixBytesAggregateExit) in "Hexit".
  iDestruct "Hexit" as
    (sp d1 s1 d2 s2 d3 s3 d4 s4 d5 s5 oldS0 oldS1
      b1 b2 b3 b4 b5 tail)
    "(Hsys & H1 & H2 & H5 & H6 & H8 & H9 & H10 & H11 & Hstack & Hmmio &
      Htrace & Hdata1 & Hlen1 & Hdata2 & Hlen2 & Hdata3 & Hlen3 & Hdata4 &
      Hlen4 & Hdata5 & Hlen5 & Hspmod & Hlow & Hhigh & Hbound & Hregs &
      HframeData1 & HframeSize1 & HframeData2 & HframeSize2 & HframeData3 &
      HframeSize3 & HframeData4 & HframeSize4 & HframeData5 & HframeSize5 &
      HP & _)".
  rewrite /writeSuccessSuffixBytesAggregateExitAt15930.
  iExists sp, d1, s1, d2, s2, d3, s3, d4, s4, d5, s5,
    oldS0, oldS1, b1, b2, b3, b4, b5, tail.
  iEval (rewrite /writeSuccessSuffixAt15930
    /writeSuccessSuffixBytes15920Frame
    /writeSuccessSuffixBytesP5
    /writeSuccessSuffixBytesDescriptor) .
  have Haddr928 : bv_unsigned sp + 920 + 8 = bv_unsigned sp + 928 by lia.
  have Haddr944 : bv_unsigned sp + 936 + 8 = bv_unsigned sp + 944 by lia.
  have Haddr960 : bv_unsigned sp + 952 + 8 = bv_unsigned sp + 960 by lia.
  have Haddr976 : bv_unsigned sp + 968 + 8 = bv_unsigned sp + 976 by lia.
  have Haddr992 : bv_unsigned sp + 984 + 8 = bv_unsigned sp + 992 by lia.
  rewrite Haddr928 Haddr944 Haddr960 Haddr976.
  iFrame.
  all: lazymatch goal with |- ?G => fail "adapter residual" G end.
Qed.
