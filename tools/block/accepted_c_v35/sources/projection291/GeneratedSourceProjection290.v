Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Evidence.RuleScratchRules.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith Lia.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.DecodeItemCompositional.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Contracts.IslarisMemory.
From iris.proofmode Require Import environments.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot6a78Entries.
Require Import ZesuSsz.Automation.EffectiveOverrides.
Open Scope Z_scope.

Lemma generated6a78_source_projection290 `{!islaG Sigma} `{!threadG} args returnAddress :
 fp_machineAt6a78_ForwardA0N0 args returnAddress ⊢
 ⌜decodeItemDomainAt returnAddress decodeItemC1BDomain args /\
   (exists rest, decodeItemInputHead args (List.nth 0 (decodeItemInputBytes args) (BV 8 0)) rest) /\
   192 <= bv_unsigned (List.nth 0 (decodeItemInputBytes args) (BV 8 0)) <= 247 /\
   bv_unsigned (List.nth 0 (decodeItemInputBytes args) (BV 8 0)) - 192 <
     bv_unsigned (Z_to_bv 64 (decodeItemInputLength args))⌝.
Proof.
 unfold fp_machineAt6a78_ForwardA0N0.
 iIntros "Hentry".
 iDestruct "Hentry" as (a5 a6 fp_seed_mstatus_bits fp_seed_satp fp_seed_zisk_free_input forward_witness_72b7e22ed74cb83b forward_witness_1492ef7bd46b3b7a forward_witness_d77b5950a2aea933 forward_witness_21649d1cf161453f forward_witness_9644ccf41f39915a forward_witness_407fca3a6f90b8db forward_witness_1eea82d2945b4618 forward_witness_751588b52f8a71ff forward_witness_cbcac9df79b9221c forward_witness_1be931110d776902 forward_witness_905cf96e605c1117 forward_witness_55ab0ce59750150a forward_witness_11fde2df72db9d06 forward_witness_791c5acc1109e8e6 forward_witness_f1505c797ad3010d forward_witness_d0511cb7161d8dd4) "Hentry".
 iDestruct "Hentry" as "(H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & %P14 & %P15 & %P16 & %P17 & %P18 & %P19 & %P20 & %P21 & %P22 & %P23 & %P24 & %P25 & %P26 & %P27 & %P28 & %P29 & %P30 & %P31 & %P32 & %P33 & %P34 & %P35 & %P36 & %P37 & %P38 & %P39 & %P40 & %P41 & %P42 & %P43)".
 iPureIntro.
 assert (Hclass : 192 <= bv_unsigned (List.nth 0 (decodeItemInputBytes args) (BV 8 0)) <= 247) by (destruct P26 as [_ [_ [? ?]]]; lia).
 split; [exact P14|].
 split.
 - destruct (decodeItemInputBytes args) as [|prefix rest] eqn:Hbytes.
   + change (192 <= 0 <= 247) in Hclass. lia.
   + exists rest. unfold decodeItemInputHead. rewrite Hbytes. reflexivity.
 - split; [exact Hclass|]. destruct P43 as [_ [Hfit _]]. exact Hfit.
Qed.
