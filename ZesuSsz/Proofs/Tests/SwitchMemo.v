From Coq Require Import Lists.List.
Require Import ZesuSsz.Automation2.SwitchDispatch.
Require Import ZesuSsz.Automation2.All.
Set Default Proof Mode "Classic".

Class ZesuStepMemoProbeOn : Prop := zesu_step_memo_probe_on : True.
Class ZesuStepMemoProbeOff : Prop := zesu_step_memo_probe_off : True.
#[local] Instance zesu_memo_probe_on : ZesuStepMemoProbeOn := I.

(* Inside one scope, repeated lookups keep their answers; a hypothesis that
   concludes in the switch (a local override) and a switch table still decide
   while they are present, and the recorded answer returns once they are
   gone. *)
Lemma switch_memo_scope_decisions : True.
Proof.
  zesu_switch_memo_scope ltac:(
    zesu_switch_enabled constr:(ZesuStepMemoProbeOn);
    zesu_switch_enabled constr:(ZesuStepMemoProbeOn);
    tryif zesu_switch_enabled constr:(ZesuStepMemoProbeOff) then fail else idtac;
    tryif zesu_switch_enabled constr:(ZesuStepMemoProbeOff) then fail else idtac;
    assert (Hoverride : ZesuStepMemoProbeOff) by exact I;
    zesu_switch_enabled constr:(ZesuStepMemoProbeOff);
    clear Hoverride;
    assert (Hlifted : ZesuStepMemoProbeOn -> ZesuStepMemoProbeOff) by (intros; exact I);
    zesu_switch_enabled constr:(ZesuStepMemoProbeOff);
    clear Hlifted;
    tryif zesu_switch_enabled constr:(ZesuStepMemoProbeOff) then fail else idtac;
    assert (Htable : ZesuSwitchDispatchCache
      (cons (ZesuStepMemoProbeOn : Prop, false) nil)) by constructor;
    tryif zesu_switch_enabled constr:(ZesuStepMemoProbeOn) then fail else idtac;
    clear Htable;
    zesu_switch_enabled constr:(ZesuStepMemoProbeOn)).
  exact I.
Qed.

(* The scope empties the memo when it fails and when it succeeds: a later
   proof, after the instance exists, sees the switch enabled. *)
Class ZesuStepMemoProbeLater : Prop := zesu_step_memo_probe_later : True.
Class ZesuStepMemoProbeLaterToo : Prop := zesu_step_memo_probe_later_too : True.

Lemma switch_memo_scope_records_off : True.
Proof.
  Fail zesu_switch_memo_scope ltac:(
    tryif zesu_switch_enabled constr:(ZesuStepMemoProbeLater) then fail else idtac;
    fail).
  zesu_switch_memo_scope ltac:(
    tryif zesu_switch_enabled constr:(ZesuStepMemoProbeLaterToo) then fail else idtac).
  exact I.
Qed.

#[local] Instance zesu_memo_probe_later : ZesuStepMemoProbeLater := I.
#[local] Instance zesu_memo_probe_later_too : ZesuStepMemoProbeLaterToo := I.

Lemma switch_memo_cleared_after_scope : True.
Proof.
  zesu_switch_enabled constr:(ZesuStepMemoProbeLater).
  zesu_switch_enabled constr:(ZesuStepMemoProbeLaterToo).
  zesu_switch_memo_scope ltac:(
    zesu_switch_enabled constr:(ZesuStepMemoProbeLater);
    zesu_switch_enabled constr:(ZesuStepMemoProbeLaterToo)).
  exact I.
Qed.
