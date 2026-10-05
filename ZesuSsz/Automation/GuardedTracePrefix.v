(* A registered trace prefix preserves its resource and determines its tail.
   The caller supplies the guard through its existing pure facts. *)
Require Import ZesuSsz.Automation.PureFacts.
Require Import isla.isla.
From iris.proofmode Require Import environments.

Section trace_prefix.
Context `{!islaG Sigma}.
Class ZesuGuardedTracePrefix (guard : Prop) (resource : iProp Sigma)
    (declared : spec) (prefix : spec -> spec) : Prop :=
  zesu_guarded_trace_prefix :
    guard -> (resource ⊢
      (∃ tail : spec, ⌜declared = prefix tail⌝ ∗ resource)).
End trace_prefix.

Ltac zesu_registered_trace_tail_core :=
  lazymatch goal with
  | |- envs_entails _ (@bi_exist _ (li_prod spec unit) ?body) =>
      let candidate := constr:(fun _ : list seq_label => False) in
      let opened := eval cbv beta in (body (candidate, tt)ₗ) in
      lazymatch opened with
      | (⌜?generated ⊆ ?declared⌝ ∗ _)%I =>
          let abstracted := eval pattern candidate in generated in
          lazymatch abstracted with
          | ?prefix ?candidate =>
              iMatchHyp ltac:(fun H resource =>
                let provider := constr:(_ : ZesuGuardedTracePrefix _ resource declared prefix) in
                lazymatch type of provider with
                | ZesuGuardedTracePrefix ?guard _ _ _ =>
                    match goal with
                    | Hguard : guard |- _ =>
                        let tail := fresh "tail" in
                        iDestruct (zesu_guarded_trace_prefix
                          (ZesuGuardedTracePrefix := provider) Hguard with H)
                          as (tail) "[% ?]";
                        iExists (tail, tt)ₗ;
                        iSplit; [iPureIntro;
                          match goal with
                          | Hconnection : declared = _ |- _ =>
                              rewrite Hconnection; reflexivity
                          end |]
                    end
                end)
          end
      end
  end.

(* This marker records a completed expansion in the current branch. *)
Definition ZesuTracePrefixUsed (declared : spec) : Prop := True.

Ltac zesu_registered_trace_tail :=
  lazymatch goal with
  | |- envs_entails _ (@bi_exist _ (li_prod spec unit) ?body) =>
      let candidate := constr:(fun _ : list seq_label => False) in
      let opened := eval cbv beta in (body (candidate, tt)ₗ) in
      lazymatch opened with
      | (⌜?generated ⊆ ?declared⌝ ∗ ?bundle)%I =>
          let head := get_head generated in
          let expanded := eval cbv beta delta [head] in generated in
          lazymatch expanded with
          | scons (SWriteMem _ _) (scons_snap (SWriteMem _ ?size) _ _) =>
          unify size (bv_to_bvn (BV 64 1));
          lazymatch bundle with
          | context [instr_pre _ _] =>
              lazymatch goal with
              | _ : ZesuTracePrefixUsed declared |- _ =>
                  fail "The registered trace prefix was already expanded"
              | _ =>
                  zesu_registered_trace_tail_core;
                  let Hused := fresh "HtracePrefixUsed" in
                  pose proof (I : ZesuTracePrefixUsed declared) as Hused
              end
          end
          end
      end
  end.
