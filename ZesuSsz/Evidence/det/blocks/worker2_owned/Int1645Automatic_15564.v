Set Printing Width 200.
Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.ReturnWand.
Require Import ZesuSsz.Automation.ReturnBundle.
Require Import isla.isla.
From iris.proofmode Require Import environments.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Generated.WriteSuccess.States.State_15564.
Require Import ZesuSsz.Automation.Sets.call.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsMaxBlobFee.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCalls.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactValueSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessHashesLoopSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsGasLoads.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAuthorizationsInt.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactWithdrawalsInt.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactBooleanSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeSuffixOptionalU64159b8Defs.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactOptionalU64NoneCallSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactEncoderU128.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderInt1645Contract.
Require Import ZesuSsz.Automation.Switches.ReturnBundle.
Require Import ZesuSsz.Automation.Switches.ReturnWand.
#[local] Instance : LithiumUnfold (@encoderInt1645Contract) := I.
#[local] Typeclasses Opaque encoderInt1645Contract.
Require Import Payload.
Require Import ZesuSsz.Automation.Switches.SpecTail.
Create HintDb zesu_payloads.

Ltac zesu_payload_trace requested :=
  lazymatch requested with
  | (spec_trace ?trace ∗ ?rest)%I => constr:(trace)
  | (?other ∗ ?rest)%I => zesu_payload_trace rest
  end.

(* Select payload witnesses only when owned resources and the complete
   payload trace match. Variable types alone do not establish that match. *)
Ltac zesu_match_owned_payload witness body :=
  let requested := eval cbv beta iota zeta delta [li_fst li_snd]
    in (body witness) in
  lazymatch requested with
  | (?resource ∗ ?rest)%I =>
      let trace := zesu_payload_trace rest in
      iSelect resource ltac:(fun Hresource =>
        iMatchHyp ltac:(fun Htrace owned =>
          lazymatch owned with
          | spec_trace ?available =>
              assert_fails (has_evar trace);
              assert_fails (has_evar available);
              first [unify trace available; iExists witness |
                let Hpayload := fresh "Hpayload" in
                assert (Hpayload : trace = available) by
                  (autorewrite with zesu_payloads; reflexivity);
                iEval (rewrite <- Hpayload) in Htrace;
                clear Hpayload; iExists witness]
          end))
  end.

Ltac zesu_match_payload_witness :=
  lazymatch goal with
  | |- envs_entails _ (@bi_exist _ (li_prod spec (li_prod (list ?A) unit)) ?body) =>
      multimatch goal with items : list A, tail : spec |- _ =>
        let witness := constr:((tail, (items, tt)ₗ)ₗ) in
        zesu_match_owned_payload witness body
      end
  | |- envs_entails _ (@bi_exist _ (li_prod spec unit) ?body) =>
      multimatch goal with tail : spec |- _ =>
        let witness := constr:((tail, tt)ₗ) in
        zesu_match_owned_payload witness body
      end
  end.


#[local] Hint Rewrite payload : zesu_payloads lithium_rewrite isla_coq_rewrite.
Ltac zesu_liAStep ::=
 liEnsureInvariant;
 try progress (unfold TRACE_LET);
 try liAIntroduceLetInGoal;
 first [
    zesu_normalize_find_mem_address
  | zesu_liAWriteMem
  | zesu_liAReadMem
  | liAAsm
  | liAExp
  | liAOther
  | liUnfoldEarly
  | zesu_liInstrPreMatch
  | zesu_close_spec_tail_if_enabled
  | zesu_match_payload_witness
  | zesu_preserve_current_unsigned
  | liStep
  | liLetBindHint
  | liUnfoldLate
 ]; liSimpl.
Ltac zesu_spec_tail_reflexivity ::=
  autorewrite with zesu_payloads;
  solve [repeat first [reflexivity | zesu_unfold_declared_spec | progress hnf]].
Lemma infer_boundary `{!islaG Sigma} `{!threadG} (sp : bv 64) (low : bv 64) (high : bv 64) (oldra : bv 64) (old5 : bv 64) (tail : spec) (P : iProp Sigma)  (BLK_STOP_15574 : iProp Sigma) :
  instr_pre 0x15574 BLK_STOP_15574 -∗
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15ce4 encoderInt1645Contract -∗
  instr_body 0x15564
    (State_15564 sp low high oldra old5 tail P).
Proof.
idtac "PROBE-BEGIN".
try intros.
idtac.
try zesu_block.
all: try zesu_enter_return_bundle_if_enabled.
all: try zesu_enter_return_wand_if_enabled.

all: try liShow.
all: lazymatch goal with |- ?E ?D ?G => idtac "RESIDUAL" G end.
Abort.
