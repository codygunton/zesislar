Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Generated.DecodeItem.MachinePilot180Entries.
Require Import ZesuSsz.Generated.DecodeItem.MachinePilot180Structural.
Require Import ZesuSsz.Generated.DecodeItem.MachinePilot180Fallthrough6ac4Projection.
Require Import ZesuSsz.Generated.DecodeItem.MachinePilot180Fallthrough6ac4ProjectionStructural.
Require Import ZesuSsz.Generated.DecodeItem.Entry6ac4WitnessRegistration.
Require Import ZesuSsz.Automation.EntryWitnessReadiness.
Require Import ZesuSsz.Automation.EntryWitnessProfile.
Require Import ZesuSsz.Evidence.Entry6ac4ProfileReady181.
Require Import ZesuSsz.Automation.EffectiveOverrides.
Open Scope Z_scope.


Require Import ZesuSsz.Evidence.RuleScratchRules.
Require Import ZesuSsz.Automation.EntryWitnessFinish232.
Require Import ZesuSsz.Automation.ListHeadFromLength.
Require Import ZesuSsz.Automation.EffectiveOverrides.
Ltac native_entry_scalar arguments :=
 cbv beta iota zeta delta [EntryWitnessData184.entry6ac4_payloadStart184 EntryWitnessData184.entry6ac4_lengthBytes184 EntryWitnessData184.entry6ac4_count184 EntryWitnessData184.entry6ac4_index184 EntryWitnessData184.entry6ac4_loaded184 EntryWitnessData184.entry6ac4_prefix184 EntryWitnessData184.entry6ac4_rest184];
 first [reflexivity |
 solve [rewrite take_0; unfold RlpDecodeItem.bigEndian; cbn; bv_solve] |
 solve [unfold RlpDecodeItem.decodeItemStackBytes; bv_solve] |
 solve [lia] | solve [bv_solve] |
 solve [let Hzero := fresh "Hzero" in let HunsignedZero := fresh "HunsignedZero" in eapply (ListHeadFromLength.zesu_list_head_from_cast_length (decodeItemInputBytes arguments) (BV 8 0) 64 (decodeItemInputLength arguments) (BV 64 0)); [eassumption | reflexivity | intro Hzero; pose proof (f_equal (@bv_unsigned 64) Hzero) as HunsignedZero; rewrite (Z_to_bv_small 64 (decodeItemInputLength arguments) ltac:(change (0 <= decodeItemInputLength arguments < 18446744073709551616); lia)) in HunsignedZero; change (decodeItemInputLength arguments = 0) in HunsignedZero; lia]] |
 solve [let HbyteRange := fresh "HbyteRange" in pose proof (bv_unsigned_in_range 8 (List.nth 0 (decodeItemInputBytes arguments) (BV 8 0))) as HbyteRange; change (0 <= bv_unsigned (List.nth 0 (decodeItemInputBytes arguments) (BV 8 0)) < 256) in HbyteRange; lia] |
 solve [rewrite length_take length_drop; rewrite Nat.min_l; [rewrite Z2Nat.id; lia | lia]]].
Ltac zesu_native_entry_tail :=
 lazymatch goal with arguments : DecodeItemArgs |- _ =>
 EntryWitnessFinish232.zesu_entry_witness_finish ltac:(progress liAStep) ltac:(native_entry_scalar arguments)
 end.
(* Stop before consuming the first authenticated registered witness package. *)
Ltac zesu_registered_pending_ready :=
 lazymatch goal with
 | _ : @ZesuEntryWitnessPending _ ?Witness ?key _
   |- environments.envs_entails _ (@bi_exist _ (li_prod ?A ?B) ?body) =>
   EntryWitnessProfile.zesu_entry_witness_ready key Witness constr:(li_prod A B) body
 end.
Ltac zesu_registered_prefix_steps fuel :=
 first [zesu_registered_pending_ready |
   lazymatch fuel with
   | S ?remaining => progress ZesuSsz.Automation.Finish.zesu_run_pass_steps;
       try ZesuSsz.Automation.Finish.zesu_solve_instances; zesu_registered_prefix_steps remaining
   | O => idtac "BOUNDED_PREFIX_FUEL_FRONTIER"
   end | idtac "BOUNDED_PREFIX_STEP_FRONTIER"].
Ltac ZesuSsz.Automation.Finish.zesu_run ::=
 ZesuSsz.Automation.ResourceGroups.zesu_expose_environment_alias;
 try ZesuSsz.Automation.Hooks.zesu_prepare_uninit_goal;
 try ZesuSsz.Automation.Hooks.zesu_normalize_find_mem_address;
 let switches := ZesuSsz.Automation.Finish.zesu_search_switches in
 ZesuSsz.Automation.SwitchDispatch.zesu_dispatch_search switches ltac:(fun _ =>
   unshelve (zesu_registered_prefix_steps constr:(64%nat))).
Ltac zesu_native_entry_tail ::=
 lazymatch goal with arguments : DecodeItemArgs |- _ =>
 EntryWitnessFinish232.zesu_entry_witness_finish ltac:(progress liAStep)
   ltac:(cbn [li_fst li_snd]; native_entry_scalar arguments)
 end.
Ltac zesu_parallel_frontier_step :=
 lazymatch goal with arguments : DecodeItemArgs |- _ =>
 first [solve [unfold SHELVED_SIDECOND; apply Z_to_bv_small;
              change (0 <= decodeItemInputPointer arguments < 18446744073709551616); lia] |
        solve [unfold SHELVED_SIDECOND; f_equal; apply bool_decide_eq_true_2; bv_solve] |
        zesu_native_entry_tail | ZesuSsz.Automation.Finish.zesu_run]
 end.
Lemma DesignedBoundary_800d6ab4 `{!islaG Sigma} `{!threadG}
  (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma) (entry_fact_0 : (decodeItemReturnAddress ( args ) = ( returnAddress ))%Z) (entry_fact_1 : (( decodeItemInputLength ( args ) ) = Z.of_nat ( List.length ( decodeItemInputBytes ( args ) ) ))%Z) (entry_fact_2 : (List.length ( decodeItemBeforeStorage ( args ) ) = 40)%nat) (entry_fact_3 : (0 <= ( decodeItemInputPointer ( args ) ))%Z) (entry_fact_4 : (0 <= ( decodeItemInputLength ( args ) ))%Z) (entry_fact_5 : (0 <= ( decodeItemOutputPointer ( args ) ))%Z) (entry_fact_6 : (( decodeItemInputPointer ( args ) ) + ( decodeItemInputLength ( args ) ) < ( 18446744073709551616 ))%Z) (entry_fact_7 : (( decodeItemOutputPointer ( args ) ) + 40 < ( 18446744073709551616 ))%Z) (entry_fact_8 : (( 16 ) <= ( decodeItemStackPointer ( args ) ))%Z) (entry_fact_9 : (( decodeItemStackPointer ( args ) ) < ( 18446744073709551616 ))%Z) (entry_fact_10 : (( 2684354560 ) + ( 16 ) <= ( decodeItemStackPointer ( args ) ))%Z) (entry_fact_11 : (( decodeItemStackPointer ( args ) ) <= ( 3221225472 ))%Z) (entry_fact_12 : (0 <= ( decodeItemReturnAddress ( args ) ))%Z) (entry_fact_13 : (( decodeItemReturnAddress ( args ) ) < ( 18446744073709551616 ))%Z) (entry_fact_14 : (( decodeItemReturnAddress ( args ) ) mod 4 = 0)%Z) (entry_fact_15 : (( 2684354560 ) <= ( decodeItemOutputPointer ( args ) ))%Z) (entry_fact_16 : (( decodeItemOutputPointer ( args ) ) + 40 <= ( 3221225472 ))%Z) (entry_fact_17 : (0 <= ( decodeItemInputEnd ( args ) ))%Z) (entry_fact_18 : (( decodeItemInputEnd ( args ) ) < ( 18446744073709551616 ))%Z) (entry_fact_19 : (( decodeItemInputPointer ( args ) ) + ( decodeItemInputLength ( args ) ) <= ( decodeItemInputEnd ( args ) ))%Z) :
  instr_pre 0x800d6ac4 (machineAt6ac4_180 (args) (returnAddress) (K) (entry_fact_0) (entry_fact_1) (entry_fact_2) (entry_fact_3) (entry_fact_4) (entry_fact_5) (entry_fact_6) (entry_fact_7) (entry_fact_8) (entry_fact_9) (entry_fact_10) (entry_fact_11) (entry_fact_12) (entry_fact_13) (entry_fact_14) (entry_fact_15) (entry_fact_16) (entry_fact_17) (entry_fact_18) (entry_fact_19)) -∗
  decodeItemSelectedCode -∗
  instr_body 0x800d6ab4 (machineAt6ab4_180 (args) (returnAddress) (K) (entry_fact_0) (entry_fact_1) (entry_fact_2) (entry_fact_3) (entry_fact_4) (entry_fact_5) (entry_fact_6) (entry_fact_7) (entry_fact_8) (entry_fact_9) (entry_fact_10) (entry_fact_11) (entry_fact_12) (entry_fact_13) (entry_fact_14) (entry_fact_15) (entry_fact_16) (entry_fact_17) (entry_fact_18) (entry_fact_19)).


Proof.
Abort.
