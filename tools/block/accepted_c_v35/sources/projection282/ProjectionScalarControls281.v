Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Evidence.RuleScratchRules.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Generated.DecodeItem.EntryWitnessData184.
Require Import ZesuSsz.Automation.EntryWitnessFinish232.
Require Import ZesuSsz.Automation.ListHeadFromLength.
From lithium Require Import pure_definitions.
From Coq Require Import Lists.List ZArith Lia.
From stdpp Require Import bitvector.tactics.
Require Import ZesuSsz.Automation.EffectiveOverrides.
Local Open Scope Z_scope.
Ltac native_entry_scalar arguments :=
 cbv beta iota zeta delta [EntryWitnessData184.entry6ac4_payloadStart184 EntryWitnessData184.entry6ac4_lengthBytes184 EntryWitnessData184.entry6ac4_count184 EntryWitnessData184.entry6ac4_index184 EntryWitnessData184.entry6ac4_loaded184 EntryWitnessData184.entry6ac4_prefix184 EntryWitnessData184.entry6ac4_rest184];
 first [reflexivity |
 solve [rewrite take_0; unfold RlpDecodeItem.bigEndian; cbn; bv_solve] |
 solve [unfold RlpDecodeItem.decodeItemStackBytes; bv_solve] |
 solve [lia] | solve [bv_solve] |
 solve [let Hzero := fresh "Hzero" in let HunsignedZero := fresh "HunsignedZero" in eapply (ListHeadFromLength.zesu_list_head_from_cast_length (decodeItemInputBytes arguments) (BV 8 0) 64 (decodeItemInputLength arguments) (BV 64 0)); [eassumption | reflexivity | intro Hzero; pose proof (f_equal (@bv_unsigned 64) Hzero) as HunsignedZero; rewrite (Z_to_bv_small 64 (decodeItemInputLength arguments) ltac:(change (0 <= decodeItemInputLength arguments < 18446744073709551616); lia)) in HunsignedZero; change (decodeItemInputLength arguments = 0) in HunsignedZero; lia]] |
 solve [let HbyteRange := fresh "HbyteRange" in pose proof (bv_unsigned_in_range 8 (List.nth 0 (decodeItemInputBytes arguments) (BV 8 0))) as HbyteRange; change (0 <= bv_unsigned (List.nth 0 (decodeItemInputBytes arguments) (BV 8 0)) < 256) in HbyteRange; lia] |
 solve [rewrite length_take length_drop; rewrite Nat.min_l; [rewrite Z2Nat.id; lia | lia]]].

Ltac projection_scalar_finish arguments :=
 solve [cbn [li_fst li_snd]; native_entry_scalar arguments].
Lemma projected_count_positive281 (args : DecodeItemArgs) (byte : bv 8) :
 248 <= bv_unsigned byte <= 255 ->
 1 <= li_fst (li_pair (bv_unsigned byte - 247) tt) <= 8.
Proof. intros [Hlower Hupper]. projection_scalar_finish args. Qed.
Lemma nested_projected_bound_positive281 (args : DecodeItemArgs) (quantity : Z) :
 1 <= quantity <= 8 ->
 1 <= li_fst (li_snd (li_pair (0%Z) (li_pair quantity tt))) <= 8.
Proof. intros Hrange. projection_scalar_finish args. Qed.
Lemma symbolic_projection_refuses281 (args : DecodeItemArgs) (pair : li_prod Z unit) : True.
Proof.
 Fail assert (li_fst pair = 0) by projection_scalar_finish args.
 exact I.
Qed.
Lemma projected_missing_range_refuses281 (args : DecodeItemArgs) (byte : bv 8) : True.
Proof.
 Fail assert (1 <= li_fst (li_pair (bv_unsigned byte - 247) tt)) by projection_scalar_finish args.
 exact I.
Qed.
Lemma projected_boolean_refuses281 (args : DecodeItemArgs) (pair : li_prod bool unit) : True.
Proof.
 Fail assert (li_fst pair = true) by projection_scalar_finish args.
 exact I.
Qed.
Lemma projected_unknown_function_refuses281 (args : DecodeItemArgs) (function : Z -> Z) (quantity : Z) : True.
Proof.
 Fail assert (function (li_fst (li_pair quantity tt)) = quantity) by projection_scalar_finish args.
 exact I.
Qed.
