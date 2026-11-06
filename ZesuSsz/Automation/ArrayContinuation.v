Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith Lia.
Require Import ZesuSsz.Automation.SwitchDispatch.
Require Import ZesuSsz.Automation.ArrayPayloadPresentation.
From iris.proofmode Require Import environments.
Local Open Scope Z_scope.

Class ZesuStepArrayContinuation : Prop := {}.

(* Normalize only lengths and address differences already present in the goal.
   A length equation must come from the unchanged proof context. *)
Ltac zesu_array_continuation_lengths :=
  repeat match goal with
  | |- context [(?base + ?offset - ?base)%Z] =>
      replace (base + offset - base)%Z with offset by lia
  | |- context [(?base - ?base)%Z] =>
      replace (base - base)%Z with 0%Z by lia
  end;
  repeat progress (rewrite ?length_app ?length_take ?length_drop;
                   cbn [length N.to_nat]);
  repeat match goal with
  | H : length ?bytes = ?count |- context [length ?bytes] =>
      progress rewrite H
  end;
  cbn;
  lia.

(* The existing presentation rule checks width, address, fraction and payload.
   [solve] makes failure atomic, including failure of a remaining pure clause.
   The callback must prove an equality; it supplies no new entry assumption. *)
Ltac zesu_array_continuation codec :=
  ZesuSsz.Automation.SwitchDispatch.zesu_switch_enabled
    constr:(ZesuStepArrayContinuation);
  lazymatch goal with
  | |- environments.envs_entails _ ?requested =>
      lazymatch requested with
      | context [@mem_mapsto_array _ _ _ _ _ _] => idtac
      end
  end;
  solve [
    ZesuSsz.Automation.ArrayPayloadPresentation.zesu_array_payload_presentation codec;
    try iPureIntro;
    repeat split;
    first [assumption | reflexivity |
      ZesuSsz.Automation.MemoryAddress.zesu_stack_arithmetic |
      zesu_array_continuation_lengths]
  ].
