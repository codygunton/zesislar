Require Import ZesuSsz.Automation2.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import List ZArith.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Contracts.DecodeItemCompositional.
Require Import ZesuSsz.Compliance.DecodeItemComplianceGenerated.
Require Import ZesuSsz.Compliance.DecodeItemCompositionalBridge.
Open Scope Z_scope.

(* The registers and compositional statements rest on the theorem over the
   24 generated block proofs (DecodeItemComplianceGenerated.v). *)
Lemma decodeItemInstrPreExistOrder `{!islaG Sigma} `{!threadG}
    (pc : Z) (A : Type) (resources : A -> iProp Sigma) (fact : A -> Prop) :
  instr_pre pc (∃ x : A, resources x ∗ ⌜fact x⌝) ⊣⊢
  instr_pre pc (∃ x : A, ⌜fact x⌝ ∗ resources x).
Proof.
  assert (Hswap : (∃ x : A, resources x ∗ ⌜fact x⌝)%I ⊣⊢
                 (∃ x : A, ⌜fact x⌝ ∗ resources x)%I).
  { apply bi.exist_proper. intros x. apply bi.sep_comm. }
  rewrite instr_pre'_eq. unfold instr_pre'_def. rewrite Hswap. reflexivity.
Qed.

Lemma decodeItemSelectedComplianceRegisters :
  forall returnAddress,
    IslarisContractCorrect decodeItemEntry returnAddress
      (decodeItemSelectedModelRegisters returnAddress).
Proof.
  exact decodeItemGeneratedComplianceRegisters.
Qed.

Lemma decodeItemSelectedComplianceCompositional :
  forall returnAddress,
    IslarisContractCorrect decodeItemEntry returnAddress
      (decodeItemSelectedModelCompositional returnAddress).
Proof.
  intros returnAddress.
  apply decodeItemRegisterComplianceFrames.
  apply decodeItemSelectedComplianceRegisters.
Qed.
