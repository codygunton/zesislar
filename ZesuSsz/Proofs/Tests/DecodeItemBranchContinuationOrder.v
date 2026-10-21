Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemCompositional.

Lemma decodeItemBranchContinuation_order_equiv `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (returnAddress : Z) :
  decodeItemBranchContinuationAt args returnAddress ⊣⊢
  (instr_pre returnAddress
    (∃ outcome : DecodeItemOutcome,
      ⌜decodeItemDomainAt returnAddress decodeItemC1BDomain args /\
        DecodeMeaningModuloKnownBugs args outcome⌝ ∗
      decodeItemExitResourcesRegisters args outcome))%I.
Proof.
  unfold decodeItemBranchContinuationAt.
  assert (Hswap :
    (∃ outcome : DecodeItemOutcome,
      decodeItemExitResourcesRegisters args outcome ∗
      ⌜decodeItemDomainAt returnAddress decodeItemC1BDomain args /\
        DecodeMeaningModuloKnownBugs args outcome⌝)%I ⊣⊢
    (∃ outcome : DecodeItemOutcome,
      ⌜decodeItemDomainAt returnAddress decodeItemC1BDomain args /\
        DecodeMeaningModuloKnownBugs args outcome⌝ ∗
      decodeItemExitResourcesRegisters args outcome)%I).
  { apply bi.exist_proper. intros outcome. apply bi.sep_comm. }
  rewrite instr_pre'_eq. unfold instr_pre'_def. rewrite Hswap. reflexivity.
Qed.
Print Assumptions decodeItemBranchContinuation_order_equiv.
