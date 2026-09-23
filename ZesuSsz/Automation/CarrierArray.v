Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMemory.
From iris.proofmode Require Import environments.

Lemma zesu_carrier_array_read_restore `{!islaG Sigma}
    (address : Z) (values : list (bv 8)) (index : nat) :
  (∃ byte : bv 8,
    address ↦ₘ∗ take index values ∗
    (address + Z.of_nat index) ↦ₘ byte ∗
    (address + Z.of_nat (S index)) ↦ₘ∗ drop (S index) values ∗
    ⌜values !! index = Some byte⌝) -∗
  address ↦ₘ∗ values.
Proof.
  iIntros "Hsplit".
  iDestruct "Hsplit" as (byte) "(Hprefix & Hbyte & Hsuffix & %Hlookup)".
  iApply (mem_mapsto_array_recombine_u8_read address values index byte
    (address + Z.of_nat (S index)) (address + Z.of_nat index)
    with "Hprefix Hsuffix Hbyte");
    iPureIntro; try exact Hlookup; reflexivity.
Qed.

Class ZesuStepCarrierArray : Prop := zesu_step_carrier_array : True.

Ltac zesu_carrier_exist_tail proposition expected :=
  lazymatch proposition with
  | @bi_exist _ expected ?body =>
    let witness := open_constr:(_ : expected) in
    let next := eval cbv beta in (body witness) in
    constr:(next)
  end.

Ltac zesu_carrier_array_goal_shape :=
  lazymatch goal with
  | |- envs_entails _ ?goal =>
    let next := zesu_carrier_exist_tail goal (bv 64) in
    let next := zesu_carrier_exist_tail next Z in
    lazymatch next with
    | @bi_exist _ ?transaction _ =>
      let next := zesu_carrier_exist_tail next transaction in
      let next := zesu_carrier_exist_tail next (list transaction) in
      let next := zesu_carrier_exist_tail next (list transaction) in
      let next := zesu_carrier_exist_tail next (list transaction) in
      let next := zesu_carrier_exist_tail next (list (bv 8)) in
      let next := zesu_carrier_exist_tail next (list (bv 8)) in
      let next := zesu_carrier_exist_tail next (list (bv 8)) in
      let _ := zesu_carrier_exist_tail next spec in idtac
    end
  end.

Ltac zesu_carrier_array_handoff :=
  iMatchHyp ltac:(fun H body =>
    iDestruct H as
      (sp base transaction transactions processed remaining bytes prefix
        suffix tail first second third fourth items)
      "(Hmachine & HarraySplit & Hframe & Hfacts & _)");
  iPoseProof (zesu_carrier_array_read_restore with "HarraySplit") as "Harray";
  iExists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _;
  iFrame.

Ltac zesu_carrier_array_handoff_if_enabled :=
  zesu_carrier_array_goal_shape;
  let _ := constr:(_ : ZesuStepCarrierArray) in
  zesu_carrier_array_handoff.
