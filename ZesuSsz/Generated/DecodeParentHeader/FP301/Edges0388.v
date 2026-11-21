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
Require Import ZesuSsz.Contracts.Candidates.ParentHeaderCandidate.
Require Import ZesuSsz.Automation2.ByteWindowFold.
Require Export ZesuSsz.Compliance.ParentHeaderHints.
Require Import ZesuSsz.Contracts.Level1.
Local Open Scope Z_scope.
Require Import lithium.lvar.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0388Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0388Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0394Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0394Structural.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot03b0Entries.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot03b0Structural.
Require Import ZesuSsz.Automation2.Hist.
From iris.proofmode Require Import proofmode.

Section edges.
Context `{!islaG Sigma} `{!threadG}.

(* fp_machineAt0388_ForwardA0N0 -> fp_machineAt0394_ForwardA0N0 (forward) *)
Global Instance zesu_hist_edge_95 (args : ParentHeaderArgs) (returnAddress : Z) (call13_after : DecodeItemOutcome) (call13_kept_x18 : bv 64) (call13_kept_x19 : bv 64) (call12_after : DecodeItemOutcome) (call12_kept_x18 : bv 64) (call12_kept_x20 : bv 64) (call10_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) (machine_x21_1 : bv 64) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt0388_ForwardA0N0_Hist (args) (returnAddress) (call13_after) (call13_kept_x18) (call13_kept_x19) (call12_after) (call12_kept_x18) (call12_kept_x20) (call10_after) (call_after) (machine_x21_1))
    (fp_machineAt0394_ForwardA0N0_Hist (args) (returnAddress) (call13_after) (call13_kept_x18) (call13_kept_x19) (call12_after) (call12_kept_x18) (call10_after) (call_after) (machine_x21_1))
    (True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt0388_ForwardA0N0_Hist in Hh.
  destruct Hh as (call11_kept_x19 & fp_seed_mstatus_bits & forward_witness_1be931110d776902 & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_88383840afa7af74 & forward_witness_1492ef7bd46b3b7a & forward_witness_d77b5950a2aea933 & forward_witness_21649d1cf161453f & forward_witness_1eea82d2945b4618 & forward_witness_751588b52f8a71ff & forward_witness_9644ccf41f39915a & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19 & HF20 & HF21 & HF22 & HF23 & HF24 & HF25 & HF26 & HF27 & HF28).
  iIntros "HN".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineAt0394_ForwardA0N0_Hist.
  exists call12_kept_x20, call11_kept_x19, fp_seed_mstatus_bits, forward_witness_1be931110d776902, forward_witness_905cf96e605c1117, forward_witness_55ab0ce59750150a, forward_witness_11fde2df72db9d06, forward_witness_88383840afa7af74, forward_witness_1492ef7bd46b3b7a, forward_witness_d77b5950a2aea933, forward_witness_21649d1cf161453f, forward_witness_1eea82d2945b4618, forward_witness_751588b52f8a71ff, forward_witness_9644ccf41f39915a.
  split; [exact HF0|].
  split; [exact HF1|].
  split; [exact HF2|].
  split; [exact HF3|].
  split; [exact HF4|].
  split; [exact HF5|].
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
  exact HF28.
Qed.

Global Instance zesu_hist_reveal_34 (args : ParentHeaderArgs) (returnAddress : Z) (call13_after : DecodeItemOutcome) (call13_kept_x18 : bv 64) (call13_kept_x19 : bv 64) (call12_after : DecodeItemOutcome) (call12_kept_x18 : bv 64) (call12_kept_x20 : bv 64) (call10_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) (machine_x21_1 : bv 64) :
  ZesuHistReveal (fp_machineAt0388_ForwardA0N0_Hist (args) (returnAddress) (call13_after) (call13_kept_x18) (call13_kept_x19) (call12_after) (call12_kept_x18) (call12_kept_x20) (call10_after) (call_after) (machine_x21_1)) ((∃ (call13_arg_x14 : bv 64) (call13_arg_x15 : bv 64) (call13_arg_x16 : bv 64) (call13_arg_x17 : bv 64) (call13_arg_x13 : bv 64) (call13_before : list byte), (decodeItemCallDomain
          (decodeItemCallDataArgs ([((bv_add (bv_add (bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)) (BV 64%N 400%Z)) (BV 64%N 18446744073709551496%Z))); (call13_kept_x19); (call13_kept_x18); (call13_arg_x13); (call13_arg_x14); (call13_arg_x15); (call13_arg_x16); (call13_arg_x17)]) (((bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)))) (bv_unsigned (((parentHeaderInputEnd args)))) (take (Z.to_nat (bv_unsigned (call13_kept_x18))) (drop (Z.to_nat (bv_unsigned (call13_kept_x19) - bv_unsigned (parentHeaderInputPointer args))) (parentHeaderInputBytes args))) call13_before)) /\ (decodeItemCallMeaning
            (decodeItemCallDataArgs ([((bv_add (bv_add (bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)) (BV 64%N 400%Z)) (BV 64%N 18446744073709551496%Z))); (call13_kept_x19); (call13_kept_x18); (call13_arg_x13); (call13_arg_x14); (call13_arg_x15); (call13_arg_x16); (call13_arg_x17)]) (((bv_add (parentHeaderStackPointer args) (BV 64%N 18446744073709551216%Z)))) (bv_unsigned (((parentHeaderInputEnd args)))) (take (Z.to_nat (bv_unsigned (call13_kept_x18))) (drop (Z.to_nat (bv_unsigned (call13_kept_x19) - bv_unsigned (parentHeaderInputPointer args))) (parentHeaderInputBytes args))) call13_before) (call13_after)))).
Proof.
  rewrite /ZesuHistReveal => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt0388_ForwardA0N0_Hist in Hh.
  destruct Hh as (call11_kept_x19 & fp_seed_mstatus_bits & forward_witness_1be931110d776902 & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_88383840afa7af74 & forward_witness_1492ef7bd46b3b7a & forward_witness_d77b5950a2aea933 & forward_witness_21649d1cf161453f & forward_witness_1eea82d2945b4618 & forward_witness_751588b52f8a71ff & forward_witness_9644ccf41f39915a & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19 & HF20 & HF21 & HF22 & HF23 & HF24 & HF25 & HF26 & HF27 & HF28).
  exact HF6.
Qed.

Global Instance zesu_hist_reveal_35 (args : ParentHeaderArgs) (returnAddress : Z) (call13_after : DecodeItemOutcome) (call13_kept_x18 : bv 64) (call13_kept_x19 : bv 64) (call12_after : DecodeItemOutcome) (call12_kept_x18 : bv 64) (call12_kept_x20 : bv 64) (call10_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) (machine_x21_1 : bv 64) :
  ZesuHistReveal (fp_machineAt0388_ForwardA0N0_Hist (args) (returnAddress) (call13_after) (call13_kept_x18) (call13_kept_x19) (call12_after) (call12_kept_x18) (call12_kept_x20) (call10_after) (call_after) (machine_x21_1)) (((bv_unsigned (parentHeaderInputPointer args) <= bv_unsigned (call13_kept_x19) /\ bv_unsigned (call13_kept_x19) + bv_unsigned (call13_kept_x18) <= bv_unsigned (parentHeaderInputPointer args) + Z.of_nat (List.length (parentHeaderInputBytes args)))%Z)).
Proof.
  rewrite /ZesuHistReveal => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt0388_ForwardA0N0_Hist in Hh.
  destruct Hh as (call11_kept_x19 & fp_seed_mstatus_bits & forward_witness_1be931110d776902 & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_88383840afa7af74 & forward_witness_1492ef7bd46b3b7a & forward_witness_d77b5950a2aea933 & forward_witness_21649d1cf161453f & forward_witness_1eea82d2945b4618 & forward_witness_751588b52f8a71ff & forward_witness_9644ccf41f39915a & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19 & HF20 & HF21 & HF22 & HF23 & HF24 & HF25 & HF26 & HF27 & HF28).
  exact HF7.
Qed.

(* fp_machineAt0388_ForwardA0N0 -> fp_machineAt03b0_ForwardA0N0 (join) *)
Global Instance zesu_hist_edge_96 (args : ParentHeaderArgs) (returnAddress : Z) (call13_after : DecodeItemOutcome) (call13_kept_x18 : bv 64) (call13_kept_x19 : bv 64) (call12_after : DecodeItemOutcome) (call12_kept_x18 : bv 64) (call12_kept_x20 : bv 64) (call10_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) (machine_x21_1 : bv 64) (machine_x22_1 : bv 64) :
  ZesuHistEdge (PROP := iProp Sigma)
    (fp_machineAt0388_ForwardA0N0_Hist (args) (returnAddress) (call13_after) (call13_kept_x18) (call13_kept_x19) (call12_after) (call12_kept_x18) (call12_kept_x20) (call10_after) (call_after) (machine_x21_1))
    (fp_machineAt03b0_ForwardA0N0_Hist (args) (returnAddress) (call13_after) (call13_kept_x18) (call13_kept_x19) (machine_x21_1) (machine_x22_1) (call10_after) (call_after))
    (⌜((List.length call12_after = 40)%nat)⌝ ∗ ⌜(bv_unsigned machine_x22_1 = ZesuSsz.Automation2.ByteWindowFold.zesu_byte_window_fold (parentHeaderInputBytes args) (Z.to_nat (bv_unsigned (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 7%nat call12_after (BV 8%N 0%Z)) (List.nth 6%nat call12_after (BV 8%N 0%Z))) (List.nth 5%nat call12_after (BV 8%N 0%Z))) (List.nth 4%nat call12_after (BV 8%N 0%Z))) (List.nth 3%nat call12_after (BV 8%N 0%Z))) (List.nth 2%nat call12_after (BV 8%N 0%Z))) (List.nth 1%nat call12_after (BV 8%N 0%Z))) (List.nth 0%nat call12_after (BV 8%N 0%Z))) - bv_unsigned (parentHeaderInputPointer args))) (Z.to_nat (bv_unsigned (bv_concat 64%N (bv_concat 56%N (bv_concat 48%N (bv_concat 40%N (bv_concat 32%N (bv_concat 24%N (bv_concat 16%N (List.nth 15%nat call12_after (BV 8%N 0%Z)) (List.nth 14%nat call12_after (BV 8%N 0%Z))) (List.nth 13%nat call12_after (BV 8%N 0%Z))) (List.nth 12%nat call12_after (BV 8%N 0%Z))) (List.nth 11%nat call12_after (BV 8%N 0%Z))) (List.nth 10%nat call12_after (BV 8%N 0%Z))) (List.nth 9%nat call12_after (BV 8%N 0%Z))) (List.nth 8%nat call12_after (BV 8%N 0%Z))))))⌝ ∗ True)%I.
Proof.
  rewrite /ZesuHistEdge => Hh. apply zesu_hist_elim in Hh. unfold fp_machineAt0388_ForwardA0N0_Hist in Hh.
  destruct Hh as (call11_kept_x19 & fp_seed_mstatus_bits & forward_witness_1be931110d776902 & forward_witness_905cf96e605c1117 & forward_witness_55ab0ce59750150a & forward_witness_11fde2df72db9d06 & forward_witness_88383840afa7af74 & forward_witness_1492ef7bd46b3b7a & forward_witness_d77b5950a2aea933 & forward_witness_21649d1cf161453f & forward_witness_1eea82d2945b4618 & forward_witness_751588b52f8a71ff & forward_witness_9644ccf41f39915a & HF0 & HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HF7 & HF8 & HF9 & HF10 & HF11 & HF12 & HF13 & HF14 & HF15 & HF16 & HF17 & HF18 & HF19 & HF20 & HF21 & HF22 & HF23 & HF24 & HF25 & HF26 & HF27 & HF28).
  iIntros "HN".
  iDestruct "HN" as "(%HV4 & %HV6 & _)".
  iPureIntro. apply zesu_hist_intro. unfold fp_machineAt03b0_ForwardA0N0_Hist.
  exists fp_seed_mstatus_bits, forward_witness_1be931110d776902, forward_witness_905cf96e605c1117, forward_witness_55ab0ce59750150a, forward_witness_11fde2df72db9d06, forward_witness_88383840afa7af74, forward_witness_1492ef7bd46b3b7a, forward_witness_d77b5950a2aea933, forward_witness_21649d1cf161453f, forward_witness_1eea82d2945b4618, forward_witness_751588b52f8a71ff, forward_witness_9644ccf41f39915a.
  split; [exact HF0|].
  split; [exact (ex_intro _ call12_after (ex_intro _ call12_kept_x18 (ex_intro _ call12_kept_x20 (ex_intro _ call11_kept_x19 (conj HF1 (conj HV4 (conj HF2 (conj HF3 (conj HF4 (conj HF5 HV6))))))))))|].
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
  split; [exact HF25|].
  split; [exact HF26|].
  split; [exact HF27|].
  exact HF28.
Qed.

End edges.
