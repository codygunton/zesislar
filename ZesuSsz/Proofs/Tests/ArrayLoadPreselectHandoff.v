Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.ArrayLoadPreselect.
Require Import ZesuSsz.Automation.ArrayLoadPriority.
Require Import isla.riscv64.riscv64.

Set Default Proof Using "Type".

Section Regression.
  Context `{!islaG Sigma} `{!threadG}.
  Local Instance guard_candidate_enabled : ZesuStepArrayLoadPriority := I.

  Lemma preselect_handoff_guard_preserves_explicit_body (pc : Z) (P : iProp Sigma) :
    instr_body pc P -∗ True.
  Proof.
    iIntros "Hhandoff".
    Fail zesu_array_load_no_explicit_handoff pc.
    done.
  Qed.

  Lemma preselect_handoff_guard_preserves_explicit_pre (pc : Z) (P : iProp Sigma) :
    instr_pre pc P -∗ True.
  Proof.
    iIntros "Hhandoff".
    Fail zesu_array_load_no_explicit_handoff pc.
    done.
  Qed.

  Lemma preselect_handoff_guard_allows_no_handoff (pc : Z) (P : iProp Sigma) : P -∗ True.
  Proof.
    iIntros "Hresource".
    zesu_array_load_no_explicit_handoff pc.
    done.
  Qed.
  Lemma preselect_handoff_kind_selects_explicit_body (pc : Z) (P : iProp Sigma)
      (lookup : Z -> option isla_trace) :
    instr_lookup_resources lookup -∗ instr_body pc P -∗
    find_in_context (FindInstrKind pc true)
      (fun kind => ⌜kind = IKPre false P⌝ ∗ True).
  Proof.
    iIntros "#Hlookup Hhandoff".
    zesu_array_load_use_explicit_handoff.
    done.
  Qed.

  Lemma preselect_handoff_kind_rejects_later_pre (pc : Z) (P Q : iProp Sigma) :
    instr_body pc P -∗ instr_pre pc Q -∗
    find_in_context (FindInstrKind pc false)
      (fun kind => ⌜kind = IKPre false P⌝ ∗ True).
  Proof.
    iIntros "Hbody Hpre".
    zesu_array_load_use_explicit_handoff.
    done.
  Qed.
  Lemma preselect_handoff_kind_selects_after_pre_open (pc : Z) (P : iProp Sigma)
      (lookup : Z -> option isla_trace) :
    instr_lookup_resources lookup -∗ instr_body pc P -∗
    instr_pre pc P.
  Proof.
    iIntros "#Hlookup Hhandoff".
    zesu_array_load_preselect.
    iSplit; [done | iIntros "$"].
  Qed.
  Local Remove Hints guard_candidate_enabled : typeclass_instances.
  Lemma preselect_handoff_inactive (pc : Z) (P : iProp Sigma) :
    instr_pre pc P -∗ instr_pre pc P.
  Proof.
    iIntros "Hhandoff".
    Fail zesu_array_load_preselect.
    iExact "Hhandoff".
  Qed.
End Regression.
Print Assumptions preselect_handoff_inactive.
Print Assumptions preselect_handoff_guard_preserves_explicit_body.
Print Assumptions preselect_handoff_guard_preserves_explicit_pre.
Print Assumptions preselect_handoff_guard_allows_no_handoff.
Print Assumptions preselect_handoff_kind_selects_explicit_body.
Print Assumptions preselect_handoff_kind_rejects_later_pre.
Print Assumptions preselect_handoff_kind_selects_after_pre_open.
