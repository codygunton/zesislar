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
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot02d0Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot02d0Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot02e4Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot02e4Structural.
Require Import ZesuSsz.Automation2.Hist.
From iris.proofmode Require Import proofmode.

Section edges.
Context `{!islaG Sigma} `{!threadG}.

(* fp_machineAt02d0_LoopClass0 -> fp_machineAt02e4_ForwardA0N0 (join) *)
Global Instance zesu_hist_edge_68 (args : ParentHeaderArgs) (returnAddress : Z) (call11_after : DecodeItemOutcome) (call11_kept_x18 : bv 64) (call11_kept_x19 : bv 64) (call10_after : DecodeItemOutcome) (call10_kept_x20 : bv 64) (call_after : DecodeItemOutcome) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt02d0_LoopClass0_Hist (args) (returnAddress) (call11_after) (call11_kept_x18) (call11_kept_x19) (call10_after) (call10_kept_x20) (call_after))
    (fp_machineAt02e4_ForwardA0N0_Hist (args) (returnAddress) (call11_after) (call11_kept_x18) (call10_kept_x20) (call10_after) (call_after))
    (True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt02d0_LoopClass0_Hist in Hh.
  destruct Hh as (call10_kept_x19 & call9_after & call9_kept_x18 & call9_kept_x19 & call8_after & call8_kept_x18 & call8_kept_x19 & call7_after & call7_kept_x18 & call7_kept_x19 & call6_after & call6_kept_x18 & call6_kept_x19 & call5_after & call5_kept_x18 & call5_kept_x19 & call4_after & call4_kept_x18 & call4_kept_x19 & call3_after & call3_kept_x18 & call3_kept_x19 & call2_after & call2_kept_x18 & call2_kept_x19 & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19 & HF20 & HF21 & HF22 & HF23 & HF24 & HF25 & HF26 & HF27 & HF28 & HF29 & HF30 & HF31 & HF32 & HF33 & HF34 & HF35 & HF36 & HF37 & HF38 & HF39 & HF40 & HF41 & HF42 & HF43 & HF44 & HF45 & HF46 & HF47 & HF48 & HF49 & HF50 & HF51 & HF52 & HF53 & HF54 & HF55 & HF56 & HF57 & HF58 & HF59 & HF60 & HF61 & HF62 & HF63 & HF64 & HF65 & HF66 & HF67 & HF68 & HF69).
  iIntros "HN".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineAt02e4_ForwardA0N0_Hist.
  exists (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z), (BV 64%N 0%Z).
  split; [exact HF0|].
  split; [exact (ex_intro _ call10_kept_x19 (ex_intro _ call9_after (ex_intro _ call9_kept_x18 (ex_intro _ call9_kept_x19 (ex_intro _ call8_after (ex_intro _ call8_kept_x18 (ex_intro _ call8_kept_x19 (ex_intro _ call7_after (ex_intro _ call7_kept_x18 (ex_intro _ call7_kept_x19 (ex_intro _ call6_after (ex_intro _ call6_kept_x18 (ex_intro _ call6_kept_x19 (ex_intro _ call5_after (ex_intro _ call5_kept_x18 (ex_intro _ call5_kept_x19 (ex_intro _ call4_after (ex_intro _ call4_kept_x18 (ex_intro _ call4_kept_x19 (ex_intro _ call3_after (ex_intro _ call3_kept_x18 (ex_intro _ call3_kept_x19 (ex_intro _ call2_after (ex_intro _ call2_kept_x18 (ex_intro _ call2_kept_x19 (conj HF1 (conj HF2 (conj HF3 (conj HF4 (conj HF5 (conj HF6 (conj HF7 (conj HF8 (conj HF9 (conj HF10 (conj HF11 (conj HF12 (conj HF13 (conj HF14 (conj HF15 (conj HF16 (conj HF17 (conj HF18 (conj HF19 (conj HF20 (conj HF21 (conj HF22 (conj HF23 (conj HF24 (conj HF25 (conj HF26 (conj HF27 (conj HF28 (conj HF29 (conj HF30 (conj HF31 (conj HF32 (conj HF33 (conj HF34 (conj HF35 (conj HF36 (conj HF37 (conj HF38 (conj HF39 (conj HF40 (conj HF41 (conj HF42 (conj HF43 (conj HF44 HF45)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [zesu_hist_view HF47|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [zesu_hist_view HF48|].
  split; [by vm_compute|].
  split; [zesu_hist_view HF49|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [by vm_compute|].
  split; [zesu_hist_view HF66|].
  split; [by vm_compute|].
  split; [zesu_hist_view HF67|].
  zesu_hist_view HF68.
Qed.

Global Instance zesu_hist_reveal_35 (args : ParentHeaderArgs) (returnAddress : Z) (call11_after : DecodeItemOutcome) (call11_kept_x18 : bv 64) (call11_kept_x19 : bv 64) (call10_after : DecodeItemOutcome) (call10_kept_x20 : bv 64) (call_after : DecodeItemOutcome) :
  ZesuHistReveal (fp_machineAt02d0_LoopClass0_Hist (args) (returnAddress) (call11_after) (call11_kept_x18) (call11_kept_x19) (call10_after) (call10_kept_x20) (call_after)) (((zesu_named_eq call11_kept_x19 (bv_sub call10_kept_x20 (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 31%nat call10_after (BV 8%N 0%Z)) (List.nth 30%nat call10_after (BV 8%N 0%Z))) (List.nth 29%nat call10_after (BV 8%N 0%Z))) (List.nth 28%nat call10_after (BV 8%N 0%Z))) (List.nth 27%nat call10_after (BV 8%N 0%Z))) (List.nth 26%nat call10_after (BV 8%N 0%Z))) (List.nth 25%nat call10_after (BV 8%N 0%Z))) (List.nth 24%nat call10_after (BV 8%N 0%Z))))))).
Proof.
  rewrite /ZesuHistReveal => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt02d0_LoopClass0_Hist in Hh.
  destruct Hh as (call10_kept_x19 & call9_after & call9_kept_x18 & call9_kept_x19 & call8_after & call8_kept_x18 & call8_kept_x19 & call7_after & call7_kept_x18 & call7_kept_x19 & call6_after & call6_kept_x18 & call6_kept_x19 & call5_after & call5_kept_x18 & call5_kept_x19 & call4_after & call4_kept_x18 & call4_kept_x19 & call3_after & call3_kept_x18 & call3_kept_x19 & call2_after & call2_kept_x18 & call2_kept_x19 & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19 & HF20 & HF21 & HF22 & HF23 & HF24 & HF25 & HF26 & HF27 & HF28 & HF29 & HF30 & HF31 & HF32 & HF33 & HF34 & HF35 & HF36 & HF37 & HF38 & HF39 & HF40 & HF41 & HF42 & HF43 & HF44 & HF45 & HF46 & HF47 & HF48 & HF49 & HF50 & HF51 & HF52 & HF53 & HF54 & HF55 & HF56 & HF57 & HF58 & HF59 & HF60 & HF61 & HF62 & HF63 & HF64 & HF65 & HF66 & HF67 & HF68 & HF69).
  exact HF46.
Qed.

End edges.
