Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Switches.RecordWitness.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.Switches.InstructionLookup.
Require Import ZesuSsz.Automation.Switches.RamFault.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
Require Import ZesuSsz.Contracts.RlpDecodeItemJoinTransfers.
From iris.proofmode Require Import environments.
Open Scope Z_scope.
Require Import ZesuSsz.Contracts.DecodeItemErrorBranch.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Compliance.DecodeItemSemanticIntroduction.
Require Import ZesuSsz.Compliance.DecodeItemSailIntroduction.

Ltac decode_item_error_at_return_witness _ :=
  first [match goal with
         | Hno : ~ ?P, Hyes : ?P |- _ => exfalso; exact (Hno Hyes)
         end
        | match goal with
          | Hge : ?a >= ?b, Hlt : ?a < ?b |- _ => exfalso; lia
          end
        | lazymatch goal with
          | |- envs_entails _ (@bi_exist _ ?T _) =>
      lazymatch T with
      | li_prod DecodeItemReturnLocals unit => idtac
      end
          end].

Ltac decode_item_error_at_trace_start _ :=
  lazymatch goal with
  | |- envs_entails _ (WPasm _) => idtac
  end.

Lemma decodeItemErrorBranchBridge_correct `{!islaG Sigma} `{!threadG}
    args (frameBytes : list byte) (masked : bv 64)
    (inputPrefix : byte) (rest : list byte) :
  ⊢ decodeItemJoinTransferObligation 0x800d69e4 0x800d6ae0
    (decodeItemErrorBranchEntry args frameBytes masked inputPrefix rest)
    (decodeItemJoin6ae0Target args).
Proof.
  unfold decodeItemJoinTransferObligation, decodeItemErrorBranchEntry,
    decodeItemJoin6ae0Target.
  iIntros "Hcode".
  iEval (unfold decodeItemSelectedCode) in "Hcode".
  iDestruct "Hcode" as "#Hcode".
  zesu_run_until decode_item_error_at_trace_start.
  zesu_expose_environment_alias.
  match goal with Hdomain : decodeItemDomainAt _ _ args |- _ =>
    pose proof Hdomain as Hfacts end.
  pose proof (decodeItemDomainInputLengthBounds args (proj2 Hfacts)) as HlengthBounds.
  assert (Hlen : 0 <= decodeItemInputLength args < word64Modulus) by
    (unfold word64Modulus; lia).
  assert (Hrejected : decodeItemRejectedFacts args) by
    (eapply (decodeItemShortStringRejected args inputPrefix rest); [exact (proj2 Hfacts) | assumption | split; assumption |];
     unfold decodeItemDomainAt, decodeItemC1BDomain, decodeItemArgsWellFormed in Hfacts;
     assert (HinputLength : decodeItemInputLength args = Z.of_nat (length (decodeItemInputBytes args))) by tauto;
     rewrite -HinputLength Z.add_1_l; apply (proj2 (Z.lt_succ_r _ _)); apply Z.ge_le;
     match goal with Hguard : bv_unsigned masked >= _ |- _ => rewrite (Z_to_bv_small 64 (decodeItemInputLength args) Hlen) in Hguard;
       match goal with Hmasked : bv_unsigned masked = _ |- _ => rewrite Hmasked in Hguard end;
       exact Hguard end).
  assert (Hstorage : length (decodeItemBeforeStorage args) = 40%nat) by
    (match goal with Hdomain : decodeItemDomainAt _ _ args |- _ =>
       unfold decodeItemDomainAt, decodeItemC1BDomain,
         decodeItemArgsWellFormed in Hdomain; tauto
     end).
  match goal with Hguard : bv_unsigned masked >=
      bv_unsigned (Z_to_bv 64 (decodeItemInputLength args)) |- _ =>
    pose proof (decodeItemErrorUnsignedComparison masked
      (Z_to_bv 64 (decodeItemInputLength args)) Hguard) as Hsigned
  end.
  zesu_run_until decode_item_error_at_return_witness.
  all: try solve [exfalso; unLET; bv_solve].
Unshelve.
all: try solve [exfalso; unLET;
  match goal with Hbad : bv_extract _ _ _ = _ |- _ =>
    vm_compute in Hbad; discriminate
  end].
all: prepare_sidecond.
all: try solve [reflexivity | bv_solve].
Qed.

Print Assumptions decodeItemErrorBranchBridge_correct.
