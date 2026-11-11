(* The registered-introduction path that every FP301 generated entry uses.
   An FP301 entry predicate is opaque (Typeclasses Opaque) and carries a
   ZesuPureFactIntro instance in its Structural module. When the predicate is the
   goal, zesu_pure_fact_hints_if_enabled applies that instance and leaves the
   introduction body: first the entry's forward alternative with the continuation,
   then the alternative's existential witnesses, pure facts and resources. *)
Require Import isla.riscv64.riscv64.
From iris.proofmode Require Import environments.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot69b0Entries.
Require Import ZesuSsz.Generated.DecodeItem.FP301.Pilot69b0Structural.
Require Import ZesuSsz.Automation2.All.

Set Default Proof Using "Type".

Section tests.
  Context `{!islaG Sigma} `{!threadG}.

  (* The entry goal becomes its forward alternative and the continuation. *)
  Lemma fp301_entry_introduction_step (args : DecodeItemArgs) (returnAddress : Z) (K : iProp Sigma) :
    fp_machineAt69b0_ForwardA0N0 args returnAddress ∗ K ⊢ fp_machineAt69b0 args returnAddress K.
  Proof.
    iIntros "H".
    ZesuSsz.Automation2.Hooks.zesu_pure_fact_hints_if_enabled.
    lazymatch goal with
    | |- envs_entails _ (fp_machineAt69b0_ForwardA0N0 args returnAddress ∗ K)%I => idtac
    end.
    iExact "H".
  Qed.

  (* The forward alternative becomes the body its registered introduction names:
     existential witnesses over pure facts and resources. *)
  Lemma fp301_alternative_introduction_step (args : DecodeItemArgs) (returnAddress : Z) :
    let body := ltac:(
      let evidence := constr:(_ : ZesuSsz.Automation.Hooks.ZesuPureFactIntro
                                    (fp_machineAt69b0_ForwardA0N0 args returnAddress) _) in
      lazymatch type of evidence with
      | ZesuSsz.Automation.Hooks.ZesuPureFactIntro _ ?source => exact source
      end) in
    body ⊢ fp_machineAt69b0_ForwardA0N0 args returnAddress.
  Proof.
    intros body. iIntros "H".
    ZesuSsz.Automation2.Hooks.zesu_pure_fact_hints_if_enabled.
    lazymatch goal with
    | |- envs_entails _ (bi_exist _) => idtac
    end.
    iExact "H".
  Qed.

  (* Without a registered introduction, the step does not apply to an opaque predicate
     that is otherwise shaped like an FP301 entry (an unfold instance, opaque). *)
  Definition fp301_unregistered_entry (args : DecodeItemArgs) : iProp Sigma := True%I.
  #[local] Instance fp301_unregistered_entry_unfold : LithiumUnfold (@fp301_unregistered_entry) := I.
  Typeclasses Opaque fp301_unregistered_entry.

  Lemma fp301_unregistered_entry_is_refused (args : DecodeItemArgs) :
    True ⊢ fp301_unregistered_entry args.
  Proof.
    iIntros "_".
    Fail ZesuSsz.Automation2.Hooks.zesu_pure_fact_hints_if_enabled.
    unfold fp301_unregistered_entry. done.
  Qed.
End tests.
