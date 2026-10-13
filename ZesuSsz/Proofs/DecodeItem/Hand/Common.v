Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From iris.proofmode Require Import tactics.

Ltac hand_repack_loop choose entry_fact normalize finish_resources frame_fact continuation :=
  choose;
  iSplit; [iPureIntro; exact entry_fact|];
  normalize; iFrame;
  finish_resources; iFrame;
  iSplit;
  [iSplit; [iPureIntro; exact frame_fact|done]|continuation; iFrame].


Ltac hand_witness_at_evar bound needle witnesses resume :=
  is_evar needle;
  let rec seek remaining :=
    first
      [ only 1: (multimatch goal with
          | |- context[?term] => constr_eq term needle
          end)
      | lazymatch remaining with
        | O => fail 0 "The witness search reached its step bound."
        | S ?next => only 1: (progress zesu_liAStep); seek next
        end ] in
  seek bound;
  only 1: (witnesses; resume).

Ltac hand_return_exit_resources open_exit frame_length :=
  open_exit; cbn;
  repeat (case_decide; try congruence); iFrame;
  repeat iDestruct select (_ ∗ emp)%I as "[? _]"; iFrame;
  lazymatch type of frame_length with
  | length ?bytes = ?count =>
    iMatchHyp ltac:(fun name resource => lazymatch resource with
      | (?base ↦ₘ∗ bytes)%I => iDestruct (IslarisMemory.mem_mapsto_byte_array_to_mapsto_len count with name) as "HhandFrame"; first exact frame_length
      end)
  end;
  iSplitR "HhandFrame"; first (repeat iSplit; iPureIntro; reflexivity);
  first [iApply (ghost_state.mem_mapsto_mapsto_to_uninit with "HhandFrame")
        | iSplitL "HhandFrame"; [iApply (ghost_state.mem_mapsto_mapsto_to_uninit with "HhandFrame") | done]].

Ltac hand_return_exit normalize_return advance_return select_caller choose_output
    prove_meaning restore_exit reject_fault :=
  normalize_return; advance_return;
  [ select_caller; choose_output; iSplitR;
    [ prove_meaning | restore_exit ]
  | reject_fault ].

Ltac hand_decode_saved_registers return_fact frame_fact stack_fact frame_register :=
  let returned := fresh "HhandReturnDecoded" in
  let framed := fresh "HhandFrameDecoded" in
  let stacked := fresh "HhandStackRestored" in
  pose proof return_fact as returned;
  pose proof frame_fact as framed;
  pose proof stack_fact as stacked;
  repeat match type of returned with
  | context[Z.to_nat (?base + ?offset - ?base)] =>
      replace (base + offset - base)%Z with offset in returned by lia
  end;
  repeat match type of framed with
  | context[Z.to_nat (?base + ?offset - ?base)] =>
      replace (base + offset - base)%Z with offset in framed by lia
  end;
  cbn [N.to_nat Z.to_nat] in returned, framed;
  subst frame_register; rewrite returned framed stacked.
