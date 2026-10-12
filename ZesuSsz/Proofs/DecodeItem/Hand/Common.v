Require Import ZesuSsz.Automation.All.
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
