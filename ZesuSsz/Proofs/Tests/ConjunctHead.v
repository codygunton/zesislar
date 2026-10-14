Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Automation.Hooks.
Require Import ZesuSsz.Automation.ConjunctMatch.
Require Import ZesuSsz.Automation.Switches.ConjunctMatch.
From iris.proofmode Require Import environments.
Definition r1c_tagged (value : Z) : Prop := value = value.
Definition r1c_other (value : Z) : Prop := value = value.
#[local] Hint Extern 1 (SimplAnd (?flag = true) True) =>
  match goal with
  | Hguard : flag = true |- _ =>
      unfold SimplAnd; split; [intros _; exact Hguard | intros _; exact I]
  end : typeclass_instances.

Global Opaque r1c_tagged r1c_other.

Lemma r1c_constant_assignment (Sigma : gFunctors) (Hfact : r1c_tagged 42) :
    ⊢ (∃ value : Z, ⌜r1c_tagged value⌝ : iProp Sigma).
Proof.
iStartProof.
zesu_conjunct_head_if_enabled.
iPureIntro. exact Hfact.
Qed.
Print Assumptions r1c_constant_assignment.

Global Opaque r1c_tagged r1c_other.

Lemma r1c_ambiguous (Sigma : gFunctors) (Hleft : r1c_tagged 1) (Hright : r1c_tagged 2) :
    ⊢ (∃ value : Z, ⌜r1c_tagged value⌝ : iProp Sigma).
Proof.
iStartProof.
Fail zesu_conjunct_head_if_enabled.
iExists 1. iPureIntro. exact Hleft.
Qed.
Print Assumptions r1c_ambiguous.

Global Opaque r1c_tagged r1c_other.

Lemma r1c_absent_head (Sigma : gFunctors) (Hother : r1c_other 42) :
    ⊢ (∃ value : Z, ⌜r1c_tagged value⌝ : iProp Sigma).
Proof.
iStartProof.
Fail zesu_conjunct_head_if_enabled.
Transparent r1c_tagged.
iExists 0. iPureIntro. unfold r1c_tagged. reflexivity.
Qed.
Print Assumptions r1c_absent_head.

Global Opaque r1c_tagged r1c_other.

Lemma r1c_ignored_binder (Sigma : gFunctors) (Hfact : r1c_tagged 42) :
    ⊢ (∃ value : Z, True : iProp Sigma).
Proof.
iStartProof.
Fail zesu_conjunct_head_if_enabled.
iExists 0. done.
Qed.
Print Assumptions r1c_ignored_binder.

Global Opaque r1c_tagged r1c_other.

Lemma r1c_variable_head (Sigma : gFunctors) (Fact : Z -> Prop) (Hfact : Fact 42) :
    ⊢ (∃ value : Z, ⌜Fact value⌝ : iProp Sigma).
Proof.
iStartProof.
Fail zesu_conjunct_head_if_enabled.
iExists 42. iPureIntro. exact Hfact.
Qed.
Print Assumptions r1c_variable_head.

Global Opaque r1c_tagged r1c_other.

Lemma r1c_unregistered_premise (Sigma : gFunctors) (Premise : Prop) (Hpremise : Premise) (Hfact : Premise -> r1c_tagged 42) :
    ⊢ (∃ value : Z, ⌜r1c_tagged value⌝ : iProp Sigma).
Proof.
iStartProof.
Fail zesu_conjunct_head_if_enabled.
iExists 42. iPureIntro. exact (Hfact Hpremise).
Qed.
Print Assumptions r1c_unregistered_premise.

Global Opaque r1c_tagged r1c_other.

Lemma r1c_registered_guard (Sigma : gFunctors) (flag : bool) (Hguard : flag = true) (Hfact : flag = true -> r1c_tagged 42) :
    ⊢ (∃ value : Z, ⌜r1c_tagged value⌝ : iProp Sigma).
Proof.
iStartProof.
zesu_conjunct_head_if_enabled.
iPureIntro. exact (Hfact Hguard).
Qed.
Print Assumptions r1c_registered_guard.

Global Opaque r1c_tagged r1c_other.

Lemma r1c_absent_guard (Sigma : gFunctors) (flag : bool) (Hfact : flag = true -> r1c_tagged 42) :
    ⊢ (∃ value : Z, ⌜r1c_tagged value⌝ : iProp Sigma).
Proof.
iStartProof.
Fail zesu_conjunct_head_if_enabled.
Transparent r1c_tagged.
iExists 0. iPureIntro. unfold r1c_tagged. reflexivity.
Qed.
Print Assumptions r1c_absent_guard.

Global Opaque r1c_tagged r1c_other.

Lemma r1c_reordered (Sigma : gFunctors) (Hfact : r1c_tagged 42) (Hother : r1c_other 7) :
    ⊢ (∃ value : Z, ⌜r1c_tagged value⌝ : iProp Sigma).
Proof.
iStartProof.
zesu_conjunct_head_if_enabled.
iPureIntro. exact Hfact.
Qed.
Print Assumptions r1c_reordered.

Global Opaque r1c_tagged r1c_other.

Lemma r1c_plain_goal (Sigma : gFunctors) (Hfact : r1c_tagged 42) :
    ⊢ (True : iProp Sigma).
Proof.
iStartProof.
Fail zesu_conjunct_head_if_enabled.
done.
Qed.
Print Assumptions r1c_plain_goal.

Global Opaque r1c_tagged r1c_other.

Lemma r1c_real_eq_ambiguous (Sigma : gFunctors) (inputPrefix : bv 64) (headerSaved otherSaved : Z) (Hheader : headerSaved = (1 + (bv_unsigned inputPrefix - 183))%Z) (Hother : otherSaved = (1 + (bv_unsigned inputPrefix - 183))%Z) :
    ⊢ (∃ headerLength : Z, ⌜headerLength = (1 + (bv_unsigned inputPrefix - 183))%Z⌝ : iProp Sigma).
Proof.
iStartProof.
Fail zesu_conjunct_head_if_enabled.
iExists headerSaved. iPureIntro. exact Hheader.
Qed.
Print Assumptions r1c_real_eq_ambiguous.

Global Opaque r1c_tagged r1c_other.

Lemma r1c_real_eq_header_discrimination (Sigma : gFunctors) (n headerSaved payloadSaved : Z) (lengthBytes : list byte) (Hheader : headerSaved = (1 + n)%Z) (Hpayload : payloadSaved = bigEndian lengthBytes) :
    ⊢ (∃ headerLength : Z, ⌜headerLength = (1 + n)%Z⌝ : iProp Sigma).
Proof.
iStartProof.
zesu_conjunct_head_if_enabled.
iPureIntro. exact Hheader.
Qed.
Print Assumptions r1c_real_eq_header_discrimination.

Global Opaque r1c_tagged r1c_other.

Lemma r1c_real_eq_payload_discrimination (Sigma : gFunctors) (n headerSaved payloadSaved : Z) (lengthBytes : list byte) (Hheader : headerSaved = (1 + n)%Z) (Hpayload : payloadSaved = bigEndian lengthBytes) :
    ⊢ (∃ payloadLength : Z, ⌜payloadLength = bigEndian lengthBytes⌝ : iProp Sigma).
Proof.
iStartProof.
zesu_conjunct_head_if_enabled.
iPureIntro. exact Hpayload.
Qed.
Print Assumptions r1c_real_eq_payload_discrimination.

Global Opaque r1c_tagged r1c_other.

Lemma r1c_real_eq_fixed_mismatch (Sigma : gFunctors) (n headerSaved payloadSaved : Z) (lengthBytes : list byte) (Hheader : headerSaved = (1 + n)%Z) (Hpayload : payloadSaved = bigEndian lengthBytes) (inputPrefix : bv 64) :
    ⊢ (∃ headerLength : Z, ⌜headerLength = (1 + (bv_unsigned inputPrefix - 183))%Z⌝ : iProp Sigma).
Proof.
iStartProof.
Fail zesu_conjunct_head_if_enabled.
iExists (1 + (bv_unsigned inputPrefix - 183))%Z. iPureIntro. reflexivity.
Qed.
Print Assumptions r1c_real_eq_fixed_mismatch.
