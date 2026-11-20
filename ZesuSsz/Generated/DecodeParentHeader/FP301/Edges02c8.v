(* Generated from FP-20261102-Level1-domain-v1. Proofs use only EDGE_SENTENCES (tools/block/render_edges.py). *)
Require ZesuSsz.Automation.Hooks.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import InstrSpecs.Machine.
Require Import EvmSailRlp.evm_rlp_types.
Require Export ZesuSsz.Interfaces.DecodeItem.
Require Export ZesuSsz.Interfaces.NextUint64.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Contracts.ParentHeaderRootFacts.
Require Import ZesuSsz.Contracts.ParentHeaderMemcpyService.
Require Import ZesuSsz.Contracts.AbiBytes.
Require Import ZesuSsz.Contracts.ZiskRuntime.
Require Export ZesuSsz.Compliance.ParentHeaderHints.
Require Import ZesuSsz.Contracts.Level1.
Local Open Scope Z_scope.
Require Import lithium.lvar.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot02c8Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot02c8Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot02d0Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot02d0Structural.
Require Import ZesuSsz.Automation2.Hist.
From iris.proofmode Require Import proofmode.

Section edges.
Context `{!islaG Sigma} `{!threadG}.

(* fp_machineAt02c8_ForwardA0N0 -> fp_machineAt02d0_LoopClass0 (loop_entry) *)
Global Instance zesu_hist_edge_73 (args : ParentHeaderArgs) (returnAddress : Z) (call11_after : DecodeItemOutcome) (call11_kept_x18 : bv 64) (call11_kept_x19 : bv 64) (call10_after : DecodeItemOutcome) (call10_kept_x20 : bv 64) (call_after : DecodeItemOutcome) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt02c8_ForwardA0N0_Hist (args) (returnAddress) (call11_after) (call11_kept_x18) (call11_kept_x19) (call10_after) (call10_kept_x20) (call_after))
    (fp_machineAt02d0_LoopClass0_Hist (args) (returnAddress) (call11_after) (call11_kept_x18) (call11_kept_x19) (call10_after) (call10_kept_x20) (call_after))
    (⌜((negb (bool_decide ((bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 15%nat call11_after (BV 8%N 0%Z)) (List.nth 14%nat call11_after (BV 8%N 0%Z))) (List.nth 13%nat call11_after (BV 8%N 0%Z))) (List.nth 12%nat call11_after (BV 8%N 0%Z))) (List.nth 11%nat call11_after (BV 8%N 0%Z))) (List.nth 10%nat call11_after (BV 8%N 0%Z))) (List.nth 9%nat call11_after (BV 8%N 0%Z))) (List.nth 8%nat call11_after (BV 8%N 0%Z))) = (BV 64%N 0%Z)))) = true) /\ ((((bv_unsigned (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 15%nat call11_after (BV 8%N 0%Z)) (List.nth 14%nat call11_after (BV 8%N 0%Z))) (List.nth 13%nat call11_after (BV 8%N 0%Z))) (List.nth 12%nat call11_after (BV 8%N 0%Z))) (List.nth 11%nat call11_after (BV 8%N 0%Z))) (List.nth 10%nat call11_after (BV 8%N 0%Z))) (List.nth 9%nat call11_after (BV 8%N 0%Z))) (List.nth 8%nat call11_after (BV 8%N 0%Z)))) <> (0%Z))%Z))⌝ ∗ True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt02c8_ForwardA0N0_Hist in Hh.
  destruct Hh as (call10_kept_x19 & call9_after & call9_kept_x18 & call9_kept_x19 & call8_after & call8_kept_x18 & call8_kept_x19 & call7_after & call7_kept_x18 & call7_kept_x19 & call6_after & call6_kept_x18 & call6_kept_x19 & call5_after & call5_kept_x18 & call5_kept_x19 & call4_after & call4_kept_x18 & call4_kept_x19 & call3_after & call3_kept_x18 & call3_kept_x19 & call2_after & call2_kept_x18 & call2_kept_x19 & fp_seed_mstatus_bits & forward_witness_cbcac9df79b9221c & forward_witness_1be931110d776902 & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_88383840afa7af74 & forward_witness_1492ef7bd46b3b7a & forward_witness_d77b5950a2aea933 & forward_witness_21649d1cf161453f & forward_witness_1eea82d2945b4618 & forward_witness_751588b52f8a71ff & forward_witness_9644ccf41f39915a & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19 & HF20 & HF21 & HF22 & HF23 & HF24 & HF25 & HF26 & HF27 & HF28 & HF29 & HF30 & HF31 & HF32 & HF33 & HF34 & HF35 & HF36 & HF37 & HF38 & HF39 & HF40 & HF41 & HF42 & HF43 & HF44 & HF45 & HF46 & HF47 & HF48 & HF49 & HF50 & HF51 & HF52 & HF53 & HF54 & HF55 & HF56 & HF57 & HF58 & HF59 & HF60 & HF61 & HF62 & HF63 & HF64 & HF65 & HF66 & HF67 & HF68 & HF69 & HF70 & HF71 & HF72 & HF73 & HF74 & HF75 & HF76 & HF77 & HF78 & HF79 & HF80 & HF81 & HF82).
  iIntros "HN".
  iDestruct "HN" as "(%HV8 & _)".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineAt02d0_LoopClass0_Hist.
  exists call10_kept_x19, call9_after, call9_kept_x18, call9_kept_x19, call8_after, call8_kept_x18, call8_kept_x19, call7_after, call7_kept_x18, call7_kept_x19, call6_after, call6_kept_x18, call6_kept_x19, call5_after, call5_kept_x18, call5_kept_x19, call4_after, call4_kept_x18, call4_kept_x19, call3_after, call3_kept_x18, call3_kept_x19, call2_after, call2_kept_x18, call2_kept_x19.
  split; [exact HF0|].
  split; [exact HF1|].
  split; [exact HF2|].
  split; [exact HF3|].
  split; [exact HF4|].
  split; [exact HF5|].
  split; [exact HF6|].
  split; [exact HF7|].
  split; [exact HF8|].
  split; [exact HF9|].
  split; [exact HF10|].
  split; [exact HF11|].
  split; [exact HF12|].
  split; [exact HF13|].
  split; [exact HF14|].
  split; [exact HF15|].
  split; [exact HF16|].
  split; [exact HF17|].
  split; [exact HF18|].
  split; [exact HF19|].
  split; [exact HF20|].
  split; [exact HF21|].
  split; [exact HF22|].
  split; [exact HF23|].
  split; [exact HF24|].
  split; [exact HF25|].
  split; [exact HF26|].
  split; [exact HF27|].
  split; [exact HF28|].
  split; [exact HF29|].
  split; [exact HF30|].
  split; [exact HF31|].
  split; [exact HF32|].
  split; [exact HF33|].
  split; [exact HF34|].
  split; [exact HF35|].
  split; [exact HF36|].
  split; [exact HF37|].
  split; [exact HF38|].
  split; [exact HF39|].
  split; [exact HF40|].
  split; [exact HF41|].
  split; [exact HF42|].
  split; [exact HF43|].
  split; [exact HF44|].
  split; [exact HF45|].
  split; [exact HF46|].
  split; [exact (proj1 HF53)|].
  split; [exact (proj1 HF56)|].
  split; [exact (proj1 HF58)|].
  split; [exact (proj1 HF62)|].
  split; [exact (proj1 HF63)|].
  split; [exact (proj1 HF65)|].
  split; [exact (proj1 HF66)|].
  split; [exact (proj1 HF67)|].
  split; [exact (proj1 HF68)|].
  split; [exact (proj1 HF69)|].
  split; [exact (proj1 HF70)|].
  split; [exact (proj1 HF71)|].
  split; [exact (proj1 HF72)|].
  split; [exact (proj1 HF73)|].
  split; [exact (proj1 HF74)|].
  split; [exact (proj1 HF75)|].
  split; [exact (proj1 HF76)|].
  split; [exact (proj1 HF77)|].
  split; [exact (proj1 HF78)|].
  split; [exact (proj1 HF79)|].
  split; [exact (proj1 HF81)|].
  split; [exact (proj1 HF82)|].
  exact (proj1 HV8).
Qed.

End edges.
